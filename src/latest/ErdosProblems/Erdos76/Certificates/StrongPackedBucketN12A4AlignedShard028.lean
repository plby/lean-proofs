/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A4Shard028

/-! Decode-only alignment checks for n=12, a=4, records 3584--3711. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard028

open PackedBucketCertificate

def missing3584 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8485626535481442304
theorem maskCheck3584 :
    checkMaskFor missing3584 StrongPackedBucketN12A4Shard028.record3584 = true := by
  decide

def missing3585 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8593712926538334208
theorem maskCheck3585 :
    checkMaskFor missing3585 StrongPackedBucketN12A4Shard028.record3585 = true := by
  decide

def missing3586 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10359123980467568640
theorem maskCheck3586 :
    checkMaskFor missing3586 StrongPackedBucketN12A4Shard028.record3586 = true := by
  decide

def missing3587 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10935584732770992128
theorem maskCheck3587 :
    checkMaskFor missing3587 StrongPackedBucketN12A4Shard028.record3587 = true := by
  decide

def missing3588 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12953197365832974336
theorem maskCheck3588 :
    checkMaskFor missing3588 StrongPackedBucketN12A4Shard028.record3588 = true := by
  decide

def missing3589 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13097312553908830208
theorem maskCheck3589 :
    checkMaskFor missing3589 StrongPackedBucketN12A4Shard028.record3589 = true := by
  decide

def missing3590 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 17420768196184506368
theorem maskCheck3590 :
    checkMaskFor missing3590 StrongPackedBucketN12A4Shard028.record3590 = true := by
  decide

def missing3591 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19582496017322344448
theorem maskCheck3591 :
    checkMaskFor missing3591 StrongPackedBucketN12A4Shard028.record3591 = true := by
  decide

def missing3592 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20158956769625767936
theorem maskCheck3592 :
    checkMaskFor missing3592 StrongPackedBucketN12A4Shard028.record3592 = true := by
  decide

def missing3593 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20591302333853335552
theorem maskCheck3593 :
    checkMaskFor missing3593 StrongPackedBucketN12A4Shard028.record3593 = true := by
  decide

def missing3594 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20699388724910227456
theorem maskCheck3594 :
    checkMaskFor missing3594 StrongPackedBucketN12A4Shard028.record3594 = true := by
  decide

def missing3595 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22176569402687750144
theorem maskCheck3595 :
    checkMaskFor missing3595 StrongPackedBucketN12A4Shard028.record3595 = true := by
  decide

def missing3596 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22320684590763606016
theorem maskCheck3596 :
    checkMaskFor missing3596 StrongPackedBucketN12A4Shard028.record3596 = true := by
  decide

def missing3597 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22428770981820497920
theorem maskCheck3597 :
    checkMaskFor missing3597 StrongPackedBucketN12A4Shard028.record3597 = true := by
  decide

def missing3598 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22825087749029101568
theorem maskCheck3598 :
    checkMaskFor missing3598 StrongPackedBucketN12A4Shard028.record3598 = true := by
  decide

def missing3599 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22861116546048065536
theorem maskCheck3599 :
    checkMaskFor missing3599 StrongPackedBucketN12A4Shard028.record3599 = true := by
  decide

def missing3600 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 26644140233039282176
theorem maskCheck3600 :
    checkMaskFor missing3600 StrongPackedBucketN12A4Shard028.record3600 = true := by
  decide

def missing3601 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 26752226624096174080
theorem maskCheck3601 :
    checkMaskFor missing3601 StrongPackedBucketN12A4Shard028.record3601 = true := by
  decide

def missing3602 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 26860313015153065984
theorem maskCheck3602 :
    checkMaskFor missing3602 StrongPackedBucketN12A4Shard028.record3602 = true := by
  decide

def missing3603 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 26896341812172029952
theorem maskCheck3603 :
    checkMaskFor missing3603 StrongPackedBucketN12A4Shard028.record3603 = true := by
  decide

def missing3604 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27400744970437525504
theorem maskCheck3604 :
    checkMaskFor missing3604 StrongPackedBucketN12A4Shard028.record3604 = true := by
  decide

def missing3605 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28229407301873696768
theorem maskCheck3605 :
    checkMaskFor missing3605 StrongPackedBucketN12A4Shard028.record3605 = true := by
  decide

def missing3606 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28661752866101264384
theorem maskCheck3606 :
    checkMaskFor missing3606 StrongPackedBucketN12A4Shard028.record3606 = true := by
  decide

def missing3607 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29094098430328832000
theorem maskCheck3607 :
    checkMaskFor missing3607 StrongPackedBucketN12A4Shard028.record3607 = true := by
  decide

def missing3608 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29238213618404687872
theorem maskCheck3608 :
    checkMaskFor missing3608 StrongPackedBucketN12A4Shard028.record3608 = true := by
  decide

def missing3609 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29742616776670183424
theorem maskCheck3609 :
    checkMaskFor missing3609 StrongPackedBucketN12A4Shard028.record3609 = true := by
  decide

def missing3610 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 31255826251466670080
theorem maskCheck3610 :
    checkMaskFor missing3610 StrongPackedBucketN12A4Shard028.record3610 = true := by
  decide

def missing3611 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 31471999033580453888
theorem maskCheck3611 :
    checkMaskFor missing3611 StrongPackedBucketN12A4Shard028.record3611 = true := by
  decide

def missing3612 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 35795454675856130048
theorem maskCheck3612 :
    checkMaskFor missing3612 StrongPackedBucketN12A4Shard028.record3612 = true := by
  decide

def missing3613 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55899523412438024192
theorem maskCheck3613 :
    checkMaskFor missing3613 StrongPackedBucketN12A4Shard028.record3613 = true := by
  decide

def missing3614 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56439955367722483712
theorem maskCheck3614 :
    checkMaskFor missing3614 StrongPackedBucketN12A4Shard028.record3614 = true := by
  decide

def missing3615 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56764214540893159424
theorem maskCheck3615 :
    checkMaskFor missing3615 StrongPackedBucketN12A4Shard028.record3615 = true := by
  decide

def missing3616 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56908329728969015296
theorem maskCheck3616 :
    checkMaskFor missing3616 StrongPackedBucketN12A4Shard028.record3616 = true := by
  decide

def missing3617 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57016416120025907200
theorem maskCheck3617 :
    checkMaskFor missing3617 StrongPackedBucketN12A4Shard028.record3617 = true := by
  decide

def missing3618 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 58925942362030997504
theorem maskCheck3618 :
    checkMaskFor missing3618 StrongPackedBucketN12A4Shard028.record3618 = true := by
  decide

def missing3619 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 59034028753087889408
theorem maskCheck3619 :
    checkMaskFor missing3619 StrongPackedBucketN12A4Shard028.record3619 = true := by
  decide

def missing3620 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 59178143941163745280
theorem maskCheck3620 :
    checkMaskFor missing3620 StrongPackedBucketN12A4Shard028.record3620 = true := by
  decide

def missing3621 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 63465570786420457472
theorem maskCheck3621 :
    checkMaskFor missing3621 StrongPackedBucketN12A4Shard028.record3621 = true := by
  decide

def missing3622 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 63501599583439421440
theorem maskCheck3622 :
    checkMaskFor missing3622 StrongPackedBucketN12A4Shard028.record3622 = true := by
  decide

def missing3623 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64834665073141088256
theorem maskCheck3623 :
    checkMaskFor missing3623 StrongPackedBucketN12A4Shard028.record3623 = true := by
  decide

def missing3624 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64978780261216944128
theorem maskCheck3624 :
    checkMaskFor missing3624 StrongPackedBucketN12A4Shard028.record3624 = true := by
  decide

def missing3625 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 65843471389672079360
theorem maskCheck3625 :
    checkMaskFor missing3625 StrongPackedBucketN12A4Shard028.record3625 = true := by
  decide

def missing3626 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 68077256804847845376
theorem maskCheck3626 :
    checkMaskFor missing3626 StrongPackedBucketN12A4Shard028.record3626 = true := by
  decide

def missing3627 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2296871406916337664
theorem maskCheck3627 :
    checkMaskFor missing3627 StrongPackedBucketN12A4Shard028.record3627 = true := by
  decide

def missing3628 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4458599228054175744
theorem maskCheck3628 :
    checkMaskFor missing3628 StrongPackedBucketN12A4Shard028.record3628 = true := by
  decide

def missing3629 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4566685619111067648
theorem maskCheck3629 :
    checkMaskFor missing3629 StrongPackedBucketN12A4Shard028.record3629 = true := by
  decide

def missing3630 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8998227652443635712
theorem maskCheck3630 :
    checkMaskFor missing3630 StrongPackedBucketN12A4Shard028.record3630 = true := by
  decide

def missing3631 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9034256449462599680
theorem maskCheck3631 :
    checkMaskFor missing3631 StrongPackedBucketN12A4Shard028.record3631 = true := by
  decide

def missing3632 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10367321939164266496
theorem maskCheck3632 :
    checkMaskFor missing3632 StrongPackedBucketN12A4Shard028.record3632 = true := by
  decide

def missing3633 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11376128255695257600
theorem maskCheck3633 :
    checkMaskFor missing3633 StrongPackedBucketN12A4Shard028.record3633 = true := by
  decide

def missing3634 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13609913670871023616
theorem maskCheck3634 :
    checkMaskFor missing3634 StrongPackedBucketN12A4Shard028.record3634 = true := by
  decide

def missing3635 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19590693976019042304
theorem maskCheck3635 :
    checkMaskFor missing3635 StrongPackedBucketN12A4Shard028.record3635 = true := by
  decide

def missing3636 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20599500292550033408
theorem maskCheck3636 :
    checkMaskFor missing3636 StrongPackedBucketN12A4Shard028.record3636 = true := by
  decide

def missing3637 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20707586683606925312
theorem maskCheck3637 :
    checkMaskFor missing3637 StrongPackedBucketN12A4Shard028.record3637 = true := by
  decide

def missing3638 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22833285707725799424
theorem maskCheck3638 :
    checkMaskFor missing3638 StrongPackedBucketN12A4Shard028.record3638 = true := by
  decide

def missing3639 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22869314504744763392
theorem maskCheck3639 :
    checkMaskFor missing3639 StrongPackedBucketN12A4Shard028.record3639 = true := by
  decide

def missing3640 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27408942929134223360
theorem maskCheck3640 :
    checkMaskFor missing3640 StrongPackedBucketN12A4Shard028.record3640 = true := by
  decide

def missing3641 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28237605260570394624
theorem maskCheck3641 :
    checkMaskFor missing3641 StrongPackedBucketN12A4Shard028.record3641 = true := by
  decide

def missing3642 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28669950824797962240
theorem maskCheck3642 :
    checkMaskFor missing3642 StrongPackedBucketN12A4Shard028.record3642 = true := by
  decide

def missing3643 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29750814735366881280
theorem maskCheck3643 :
    checkMaskFor missing3643 StrongPackedBucketN12A4Shard028.record3643 = true := by
  decide

def missing3644 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38037438049728593920
theorem maskCheck3644 :
    checkMaskFor missing3644 StrongPackedBucketN12A4Shard028.record3644 = true := by
  decide

def missing3645 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39046244366259585024
theorem maskCheck3645 :
    checkMaskFor missing3645 StrongPackedBucketN12A4Shard028.record3645 = true := by
  decide

def missing3646 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39154330757316476928
theorem maskCheck3646 :
    checkMaskFor missing3646 StrongPackedBucketN12A4Shard028.record3646 = true := by
  decide

def missing3647 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41280029781435351040
theorem maskCheck3647 :
    checkMaskFor missing3647 StrongPackedBucketN12A4Shard028.record3647 = true := by
  decide

def missing3648 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41316058578454315008
theorem maskCheck3648 :
    checkMaskFor missing3648 StrongPackedBucketN12A4Shard028.record3648 = true := by
  decide

def missing3649 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 45855687002843774976
theorem maskCheck3649 :
    checkMaskFor missing3649 StrongPackedBucketN12A4Shard028.record3649 = true := by
  decide

def missing3650 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46684349334279946240
theorem maskCheck3650 :
    checkMaskFor missing3650 StrongPackedBucketN12A4Shard028.record3650 = true := by
  decide

def missing3651 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47116694898507513856
theorem maskCheck3651 :
    checkMaskFor missing3651 StrongPackedBucketN12A4Shard028.record3651 = true := by
  decide

def missing3652 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 48197558809076432896
theorem maskCheck3652 :
    checkMaskFor missing3652 StrongPackedBucketN12A4Shard028.record3652 = true := by
  decide

def missing3653 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55907721371134722048
theorem maskCheck3653 :
    checkMaskFor missing3653 StrongPackedBucketN12A4Shard028.record3653 = true := by
  decide

def missing3654 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56340066935362289664
theorem maskCheck3654 :
    checkMaskFor missing3654 StrongPackedBucketN12A4Shard028.record3654 = true := by
  decide

def missing3655 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56448153326419181568
theorem maskCheck3655 :
    checkMaskFor missing3655 StrongPackedBucketN12A4Shard028.record3655 = true := by
  decide

def missing3656 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57420930845931208704
theorem maskCheck3656 :
    checkMaskFor missing3656 StrongPackedBucketN12A4Shard028.record3656 = true := by
  decide

def missing3657 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57456959642950172672
theorem maskCheck3657 :
    checkMaskFor missing3657 StrongPackedBucketN12A4Shard028.record3657 = true := by
  decide

def missing3658 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 59690745058125938688
theorem maskCheck3658 :
    checkMaskFor missing3658 StrongPackedBucketN12A4Shard028.record3658 = true := by
  decide

def missing3659 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64842863031837786112
theorem maskCheck3659 :
    checkMaskFor missing3659 StrongPackedBucketN12A4Shard028.record3659 = true := by
  decide

def missing3660 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64986978219913641984
theorem maskCheck3660 :
    checkMaskFor missing3660 StrongPackedBucketN12A4Shard028.record3660 = true := by
  decide

def missing3661 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 65491381378179137536
theorem maskCheck3661 :
    checkMaskFor missing3661 StrongPackedBucketN12A4Shard028.record3661 = true := by
  decide

def missing3662 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1117420885754511360
theorem maskCheck3662 :
    checkMaskFor missing3662 StrongPackedBucketN12A4Shard028.record3662 = true := by
  decide

def missing3663 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1982112014209646592
theorem maskCheck3663 :
    checkMaskFor missing3663 StrongPackedBucketN12A4Shard028.record3663 = true := by
  decide

def missing3664 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2126227202285502464
theorem maskCheck3664 :
    checkMaskFor missing3664 StrongPackedBucketN12A4Shard028.record3664 = true := by
  decide

def missing3665 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2234313593342394368
theorem maskCheck3665 :
    checkMaskFor missing3665 StrongPackedBucketN12A4Shard028.record3665 = true := by
  decide

def missing3666 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4143839835347484672
theorem maskCheck3666 :
    checkMaskFor missing3666 StrongPackedBucketN12A4Shard028.record3666 = true := by
  decide

def missing3667 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4251926226404376576
theorem maskCheck3667 :
    checkMaskFor missing3667 StrongPackedBucketN12A4Shard028.record3667 = true := by
  decide

def missing3668 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4360012617461268480
theorem maskCheck3668 :
    checkMaskFor missing3668 StrongPackedBucketN12A4Shard028.record3668 = true := by
  decide

def missing3669 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4396041414480232448
theorem maskCheck3669 :
    checkMaskFor missing3669 StrongPackedBucketN12A4Shard028.record3669 = true := by
  decide

def missing3670 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8683468259736944640
theorem maskCheck3670 :
    checkMaskFor missing3670 StrongPackedBucketN12A4Shard028.record3670 = true := by
  decide

def missing3671 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8719497056755908608
theorem maskCheck3671 :
    checkMaskFor missing3671 StrongPackedBucketN12A4Shard028.record3671 = true := by
  decide

def missing3672 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8935669838869692416
theorem maskCheck3672 :
    checkMaskFor missing3672 StrongPackedBucketN12A4Shard028.record3672 = true := by
  decide

def missing3673 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9764332170305863680
theorem maskCheck3673 :
    checkMaskFor missing3673 StrongPackedBucketN12A4Shard028.record3673 = true := by
  decide

def missing3674 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10052562546457575424
theorem maskCheck3674 :
    checkMaskFor missing3674 StrongPackedBucketN12A4Shard028.record3674 = true := by
  decide

def missing3675 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10196677734533431296
theorem maskCheck3675 :
    checkMaskFor missing3675 StrongPackedBucketN12A4Shard028.record3675 = true := by
  decide

def missing3676 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10304764125590323200
theorem maskCheck3676 :
    checkMaskFor missing3676 StrongPackedBucketN12A4Shard028.record3676 = true := by
  decide

def missing3677 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11061368862988566528
theorem maskCheck3677 :
    checkMaskFor missing3677 StrongPackedBucketN12A4Shard028.record3677 = true := by
  decide

def missing3678 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11169455254045458432
theorem maskCheck3678 :
    checkMaskFor missing3678 StrongPackedBucketN12A4Shard028.record3678 = true := by
  decide

def missing3679 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11277541645102350336
theorem maskCheck3679 :
    checkMaskFor missing3679 StrongPackedBucketN12A4Shard028.record3679 = true := by
  decide

def missing3680 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11313570442121314304
theorem maskCheck3680 :
    checkMaskFor missing3680 StrongPackedBucketN12A4Shard028.record3680 = true := by
  decide

def missing3681 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13295154278164332544
theorem maskCheck3681 :
    checkMaskFor missing3681 StrongPackedBucketN12A4Shard028.record3681 = true := by
  decide

def missing3682 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13331183075183296512
theorem maskCheck3682 :
    checkMaskFor missing3682 StrongPackedBucketN12A4Shard028.record3682 = true := by
  decide

def missing3683 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13547355857297080320
theorem maskCheck3683 :
    checkMaskFor missing3683 StrongPackedBucketN12A4Shard028.record3683 = true := by
  decide

def missing3684 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 17870811499572756480
theorem maskCheck3684 :
    checkMaskFor missing3684 StrongPackedBucketN12A4Shard028.record3684 = true := by
  decide

def missing3685 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18987704207160639488
theorem maskCheck3685 :
    checkMaskFor missing3685 StrongPackedBucketN12A4Shard028.record3685 = true := by
  decide

def missing3686 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19275934583312351232
theorem maskCheck3686 :
    checkMaskFor missing3686 StrongPackedBucketN12A4Shard028.record3686 = true := by
  decide

def missing3687 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19420049771388207104
theorem maskCheck3687 :
    checkMaskFor missing3687 StrongPackedBucketN12A4Shard028.record3687 = true := by
  decide

def missing3688 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19528136162445099008
theorem maskCheck3688 :
    checkMaskFor missing3688 StrongPackedBucketN12A4Shard028.record3688 = true := by
  decide

def missing3689 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20284740899843342336
theorem maskCheck3689 :
    checkMaskFor missing3689 StrongPackedBucketN12A4Shard028.record3689 = true := by
  decide

def missing3690 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20392827290900234240
theorem maskCheck3690 :
    checkMaskFor missing3690 StrongPackedBucketN12A4Shard028.record3690 = true := by
  decide

def missing3691 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20500913681957126144
theorem maskCheck3691 :
    checkMaskFor missing3691 StrongPackedBucketN12A4Shard028.record3691 = true := by
  decide

def missing3692 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20536942478976090112
theorem maskCheck3692 :
    checkMaskFor missing3692 StrongPackedBucketN12A4Shard028.record3692 = true := by
  decide

def missing3693 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22518526315019108352
theorem maskCheck3693 :
    checkMaskFor missing3693 StrongPackedBucketN12A4Shard028.record3693 = true := by
  decide

def missing3694 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22554555112038072320
theorem maskCheck3694 :
    checkMaskFor missing3694 StrongPackedBucketN12A4Shard028.record3694 = true := by
  decide

def missing3695 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22770727894151856128
theorem maskCheck3695 :
    checkMaskFor missing3695 StrongPackedBucketN12A4Shard028.record3695 = true := by
  decide

def missing3696 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27094183536427532288
theorem maskCheck3696 :
    checkMaskFor missing3696 StrongPackedBucketN12A4Shard028.record3696 = true := by
  decide

def missing3697 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27922845867863703552
theorem maskCheck3697 :
    checkMaskFor missing3697 StrongPackedBucketN12A4Shard028.record3697 = true := by
  decide

def missing3698 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28066961055939559424
theorem maskCheck3698 :
    checkMaskFor missing3698 StrongPackedBucketN12A4Shard028.record3698 = true := by
  decide

def missing3699 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28175047446996451328
theorem maskCheck3699 :
    checkMaskFor missing3699 StrongPackedBucketN12A4Shard028.record3699 = true := by
  decide

def missing3700 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28355191432091271168
theorem maskCheck3700 :
    checkMaskFor missing3700 StrongPackedBucketN12A4Shard028.record3700 = true := by
  decide

def missing3701 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28463277823148163072
theorem maskCheck3701 :
    checkMaskFor missing3701 StrongPackedBucketN12A4Shard028.record3701 = true := by
  decide

def missing3702 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28571364214205054976
theorem maskCheck3702 :
    checkMaskFor missing3702 StrongPackedBucketN12A4Shard028.record3702 = true := by
  decide

def missing3703 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28607393011224018944
theorem maskCheck3703 :
    checkMaskFor missing3703 StrongPackedBucketN12A4Shard028.record3703 = true := by
  decide

def missing3704 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29436055342660190208
theorem maskCheck3704 :
    checkMaskFor missing3704 StrongPackedBucketN12A4Shard028.record3704 = true := by
  decide

def missing3705 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29472084139679154176
theorem maskCheck3705 :
    checkMaskFor missing3705 StrongPackedBucketN12A4Shard028.record3705 = true := by
  decide

def missing3706 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29688256921792937984
theorem maskCheck3706 :
    checkMaskFor missing3706 StrongPackedBucketN12A4Shard028.record3706 = true := by
  decide

def missing3707 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 31705869554854920192
theorem maskCheck3707 :
    checkMaskFor missing3707 StrongPackedBucketN12A4Shard028.record3707 = true := by
  decide

def missing3708 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37434448280870191104
theorem maskCheck3708 :
    checkMaskFor missing3708 StrongPackedBucketN12A4Shard028.record3708 = true := by
  decide

def missing3709 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37722678657021902848
theorem maskCheck3709 :
    checkMaskFor missing3709 StrongPackedBucketN12A4Shard028.record3709 = true := by
  decide

def missing3710 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46369589941573255168
theorem maskCheck3710 :
    checkMaskFor missing3710 StrongPackedBucketN12A4Shard028.record3710 = true := by
  decide

def missing3711 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46513705129649111040
theorem maskCheck3711 :
    checkMaskFor missing3711 StrongPackedBucketN12A4Shard028.record3711 = true := by
  decide

def missing3584_3585 : List (BitVec (edgeCount 12)) :=
  [missing3584]
abbrev records3584_3585 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3584]
theorem aligned3584_3585 :
    AlignedValid 12 4 missing3584_3585 records3584_3585 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3584
    maskCheck3584 AlignedValid.nil

def missing3585_3586 : List (BitVec (edgeCount 12)) :=
  [missing3585]
abbrev records3585_3586 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3585]
theorem aligned3585_3586 :
    AlignedValid 12 4 missing3585_3586 records3585_3586 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3585
    maskCheck3585 AlignedValid.nil

def missing3584_3586 : List (BitVec (edgeCount 12)) :=
  missing3584_3585 ++ missing3585_3586
abbrev records3584_3586 : List Blob :=
  records3584_3585 ++ records3585_3586
theorem aligned3584_3586 :
    AlignedValid 12 4 missing3584_3586 records3584_3586 :=
  aligned3584_3585.append aligned3585_3586

def missing3586_3587 : List (BitVec (edgeCount 12)) :=
  [missing3586]
abbrev records3586_3587 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3586]
theorem aligned3586_3587 :
    AlignedValid 12 4 missing3586_3587 records3586_3587 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3586
    maskCheck3586 AlignedValid.nil

def missing3587_3588 : List (BitVec (edgeCount 12)) :=
  [missing3587]
abbrev records3587_3588 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3587]
theorem aligned3587_3588 :
    AlignedValid 12 4 missing3587_3588 records3587_3588 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3587
    maskCheck3587 AlignedValid.nil

def missing3586_3588 : List (BitVec (edgeCount 12)) :=
  missing3586_3587 ++ missing3587_3588
abbrev records3586_3588 : List Blob :=
  records3586_3587 ++ records3587_3588
theorem aligned3586_3588 :
    AlignedValid 12 4 missing3586_3588 records3586_3588 :=
  aligned3586_3587.append aligned3587_3588

def missing3584_3588 : List (BitVec (edgeCount 12)) :=
  missing3584_3586 ++ missing3586_3588
abbrev records3584_3588 : List Blob :=
  records3584_3586 ++ records3586_3588
theorem aligned3584_3588 :
    AlignedValid 12 4 missing3584_3588 records3584_3588 :=
  aligned3584_3586.append aligned3586_3588

def missing3588_3589 : List (BitVec (edgeCount 12)) :=
  [missing3588]
abbrev records3588_3589 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3588]
theorem aligned3588_3589 :
    AlignedValid 12 4 missing3588_3589 records3588_3589 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3588
    maskCheck3588 AlignedValid.nil

def missing3589_3590 : List (BitVec (edgeCount 12)) :=
  [missing3589]
abbrev records3589_3590 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3589]
theorem aligned3589_3590 :
    AlignedValid 12 4 missing3589_3590 records3589_3590 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3589
    maskCheck3589 AlignedValid.nil

def missing3588_3590 : List (BitVec (edgeCount 12)) :=
  missing3588_3589 ++ missing3589_3590
abbrev records3588_3590 : List Blob :=
  records3588_3589 ++ records3589_3590
theorem aligned3588_3590 :
    AlignedValid 12 4 missing3588_3590 records3588_3590 :=
  aligned3588_3589.append aligned3589_3590

def missing3590_3591 : List (BitVec (edgeCount 12)) :=
  [missing3590]
abbrev records3590_3591 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3590]
theorem aligned3590_3591 :
    AlignedValid 12 4 missing3590_3591 records3590_3591 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3590
    maskCheck3590 AlignedValid.nil

def missing3591_3592 : List (BitVec (edgeCount 12)) :=
  [missing3591]
abbrev records3591_3592 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3591]
theorem aligned3591_3592 :
    AlignedValid 12 4 missing3591_3592 records3591_3592 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3591
    maskCheck3591 AlignedValid.nil

def missing3590_3592 : List (BitVec (edgeCount 12)) :=
  missing3590_3591 ++ missing3591_3592
abbrev records3590_3592 : List Blob :=
  records3590_3591 ++ records3591_3592
theorem aligned3590_3592 :
    AlignedValid 12 4 missing3590_3592 records3590_3592 :=
  aligned3590_3591.append aligned3591_3592

def missing3588_3592 : List (BitVec (edgeCount 12)) :=
  missing3588_3590 ++ missing3590_3592
abbrev records3588_3592 : List Blob :=
  records3588_3590 ++ records3590_3592
theorem aligned3588_3592 :
    AlignedValid 12 4 missing3588_3592 records3588_3592 :=
  aligned3588_3590.append aligned3590_3592

def missing3584_3592 : List (BitVec (edgeCount 12)) :=
  missing3584_3588 ++ missing3588_3592
abbrev records3584_3592 : List Blob :=
  records3584_3588 ++ records3588_3592
theorem aligned3584_3592 :
    AlignedValid 12 4 missing3584_3592 records3584_3592 :=
  aligned3584_3588.append aligned3588_3592

def missing3592_3593 : List (BitVec (edgeCount 12)) :=
  [missing3592]
abbrev records3592_3593 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3592]
theorem aligned3592_3593 :
    AlignedValid 12 4 missing3592_3593 records3592_3593 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3592
    maskCheck3592 AlignedValid.nil

def missing3593_3594 : List (BitVec (edgeCount 12)) :=
  [missing3593]
abbrev records3593_3594 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3593]
theorem aligned3593_3594 :
    AlignedValid 12 4 missing3593_3594 records3593_3594 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3593
    maskCheck3593 AlignedValid.nil

def missing3592_3594 : List (BitVec (edgeCount 12)) :=
  missing3592_3593 ++ missing3593_3594
abbrev records3592_3594 : List Blob :=
  records3592_3593 ++ records3593_3594
theorem aligned3592_3594 :
    AlignedValid 12 4 missing3592_3594 records3592_3594 :=
  aligned3592_3593.append aligned3593_3594

def missing3594_3595 : List (BitVec (edgeCount 12)) :=
  [missing3594]
abbrev records3594_3595 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3594]
theorem aligned3594_3595 :
    AlignedValid 12 4 missing3594_3595 records3594_3595 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3594
    maskCheck3594 AlignedValid.nil

def missing3595_3596 : List (BitVec (edgeCount 12)) :=
  [missing3595]
abbrev records3595_3596 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3595]
theorem aligned3595_3596 :
    AlignedValid 12 4 missing3595_3596 records3595_3596 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3595
    maskCheck3595 AlignedValid.nil

def missing3594_3596 : List (BitVec (edgeCount 12)) :=
  missing3594_3595 ++ missing3595_3596
abbrev records3594_3596 : List Blob :=
  records3594_3595 ++ records3595_3596
theorem aligned3594_3596 :
    AlignedValid 12 4 missing3594_3596 records3594_3596 :=
  aligned3594_3595.append aligned3595_3596

def missing3592_3596 : List (BitVec (edgeCount 12)) :=
  missing3592_3594 ++ missing3594_3596
abbrev records3592_3596 : List Blob :=
  records3592_3594 ++ records3594_3596
theorem aligned3592_3596 :
    AlignedValid 12 4 missing3592_3596 records3592_3596 :=
  aligned3592_3594.append aligned3594_3596

def missing3596_3597 : List (BitVec (edgeCount 12)) :=
  [missing3596]
abbrev records3596_3597 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3596]
theorem aligned3596_3597 :
    AlignedValid 12 4 missing3596_3597 records3596_3597 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3596
    maskCheck3596 AlignedValid.nil

def missing3597_3598 : List (BitVec (edgeCount 12)) :=
  [missing3597]
abbrev records3597_3598 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3597]
theorem aligned3597_3598 :
    AlignedValid 12 4 missing3597_3598 records3597_3598 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3597
    maskCheck3597 AlignedValid.nil

def missing3596_3598 : List (BitVec (edgeCount 12)) :=
  missing3596_3597 ++ missing3597_3598
abbrev records3596_3598 : List Blob :=
  records3596_3597 ++ records3597_3598
theorem aligned3596_3598 :
    AlignedValid 12 4 missing3596_3598 records3596_3598 :=
  aligned3596_3597.append aligned3597_3598

def missing3598_3599 : List (BitVec (edgeCount 12)) :=
  [missing3598]
abbrev records3598_3599 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3598]
theorem aligned3598_3599 :
    AlignedValid 12 4 missing3598_3599 records3598_3599 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3598
    maskCheck3598 AlignedValid.nil

def missing3599_3600 : List (BitVec (edgeCount 12)) :=
  [missing3599]
abbrev records3599_3600 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3599]
theorem aligned3599_3600 :
    AlignedValid 12 4 missing3599_3600 records3599_3600 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3599
    maskCheck3599 AlignedValid.nil

def missing3598_3600 : List (BitVec (edgeCount 12)) :=
  missing3598_3599 ++ missing3599_3600
abbrev records3598_3600 : List Blob :=
  records3598_3599 ++ records3599_3600
theorem aligned3598_3600 :
    AlignedValid 12 4 missing3598_3600 records3598_3600 :=
  aligned3598_3599.append aligned3599_3600

def missing3596_3600 : List (BitVec (edgeCount 12)) :=
  missing3596_3598 ++ missing3598_3600
abbrev records3596_3600 : List Blob :=
  records3596_3598 ++ records3598_3600
theorem aligned3596_3600 :
    AlignedValid 12 4 missing3596_3600 records3596_3600 :=
  aligned3596_3598.append aligned3598_3600

def missing3592_3600 : List (BitVec (edgeCount 12)) :=
  missing3592_3596 ++ missing3596_3600
abbrev records3592_3600 : List Blob :=
  records3592_3596 ++ records3596_3600
theorem aligned3592_3600 :
    AlignedValid 12 4 missing3592_3600 records3592_3600 :=
  aligned3592_3596.append aligned3596_3600

def missing3584_3600 : List (BitVec (edgeCount 12)) :=
  missing3584_3592 ++ missing3592_3600
abbrev records3584_3600 : List Blob :=
  records3584_3592 ++ records3592_3600
theorem aligned3584_3600 :
    AlignedValid 12 4 missing3584_3600 records3584_3600 :=
  aligned3584_3592.append aligned3592_3600

def missing3600_3601 : List (BitVec (edgeCount 12)) :=
  [missing3600]
abbrev records3600_3601 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3600]
theorem aligned3600_3601 :
    AlignedValid 12 4 missing3600_3601 records3600_3601 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3600
    maskCheck3600 AlignedValid.nil

def missing3601_3602 : List (BitVec (edgeCount 12)) :=
  [missing3601]
abbrev records3601_3602 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3601]
theorem aligned3601_3602 :
    AlignedValid 12 4 missing3601_3602 records3601_3602 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3601
    maskCheck3601 AlignedValid.nil

def missing3600_3602 : List (BitVec (edgeCount 12)) :=
  missing3600_3601 ++ missing3601_3602
abbrev records3600_3602 : List Blob :=
  records3600_3601 ++ records3601_3602
theorem aligned3600_3602 :
    AlignedValid 12 4 missing3600_3602 records3600_3602 :=
  aligned3600_3601.append aligned3601_3602

def missing3602_3603 : List (BitVec (edgeCount 12)) :=
  [missing3602]
abbrev records3602_3603 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3602]
theorem aligned3602_3603 :
    AlignedValid 12 4 missing3602_3603 records3602_3603 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3602
    maskCheck3602 AlignedValid.nil

def missing3603_3604 : List (BitVec (edgeCount 12)) :=
  [missing3603]
abbrev records3603_3604 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3603]
theorem aligned3603_3604 :
    AlignedValid 12 4 missing3603_3604 records3603_3604 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3603
    maskCheck3603 AlignedValid.nil

def missing3602_3604 : List (BitVec (edgeCount 12)) :=
  missing3602_3603 ++ missing3603_3604
abbrev records3602_3604 : List Blob :=
  records3602_3603 ++ records3603_3604
theorem aligned3602_3604 :
    AlignedValid 12 4 missing3602_3604 records3602_3604 :=
  aligned3602_3603.append aligned3603_3604

def missing3600_3604 : List (BitVec (edgeCount 12)) :=
  missing3600_3602 ++ missing3602_3604
abbrev records3600_3604 : List Blob :=
  records3600_3602 ++ records3602_3604
theorem aligned3600_3604 :
    AlignedValid 12 4 missing3600_3604 records3600_3604 :=
  aligned3600_3602.append aligned3602_3604

def missing3604_3605 : List (BitVec (edgeCount 12)) :=
  [missing3604]
abbrev records3604_3605 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3604]
theorem aligned3604_3605 :
    AlignedValid 12 4 missing3604_3605 records3604_3605 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3604
    maskCheck3604 AlignedValid.nil

def missing3605_3606 : List (BitVec (edgeCount 12)) :=
  [missing3605]
abbrev records3605_3606 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3605]
theorem aligned3605_3606 :
    AlignedValid 12 4 missing3605_3606 records3605_3606 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3605
    maskCheck3605 AlignedValid.nil

def missing3604_3606 : List (BitVec (edgeCount 12)) :=
  missing3604_3605 ++ missing3605_3606
abbrev records3604_3606 : List Blob :=
  records3604_3605 ++ records3605_3606
theorem aligned3604_3606 :
    AlignedValid 12 4 missing3604_3606 records3604_3606 :=
  aligned3604_3605.append aligned3605_3606

def missing3606_3607 : List (BitVec (edgeCount 12)) :=
  [missing3606]
abbrev records3606_3607 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3606]
theorem aligned3606_3607 :
    AlignedValid 12 4 missing3606_3607 records3606_3607 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3606
    maskCheck3606 AlignedValid.nil

def missing3607_3608 : List (BitVec (edgeCount 12)) :=
  [missing3607]
abbrev records3607_3608 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3607]
theorem aligned3607_3608 :
    AlignedValid 12 4 missing3607_3608 records3607_3608 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3607
    maskCheck3607 AlignedValid.nil

def missing3606_3608 : List (BitVec (edgeCount 12)) :=
  missing3606_3607 ++ missing3607_3608
abbrev records3606_3608 : List Blob :=
  records3606_3607 ++ records3607_3608
theorem aligned3606_3608 :
    AlignedValid 12 4 missing3606_3608 records3606_3608 :=
  aligned3606_3607.append aligned3607_3608

def missing3604_3608 : List (BitVec (edgeCount 12)) :=
  missing3604_3606 ++ missing3606_3608
abbrev records3604_3608 : List Blob :=
  records3604_3606 ++ records3606_3608
theorem aligned3604_3608 :
    AlignedValid 12 4 missing3604_3608 records3604_3608 :=
  aligned3604_3606.append aligned3606_3608

def missing3600_3608 : List (BitVec (edgeCount 12)) :=
  missing3600_3604 ++ missing3604_3608
abbrev records3600_3608 : List Blob :=
  records3600_3604 ++ records3604_3608
theorem aligned3600_3608 :
    AlignedValid 12 4 missing3600_3608 records3600_3608 :=
  aligned3600_3604.append aligned3604_3608

def missing3608_3609 : List (BitVec (edgeCount 12)) :=
  [missing3608]
abbrev records3608_3609 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3608]
theorem aligned3608_3609 :
    AlignedValid 12 4 missing3608_3609 records3608_3609 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3608
    maskCheck3608 AlignedValid.nil

def missing3609_3610 : List (BitVec (edgeCount 12)) :=
  [missing3609]
abbrev records3609_3610 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3609]
theorem aligned3609_3610 :
    AlignedValid 12 4 missing3609_3610 records3609_3610 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3609
    maskCheck3609 AlignedValid.nil

def missing3608_3610 : List (BitVec (edgeCount 12)) :=
  missing3608_3609 ++ missing3609_3610
abbrev records3608_3610 : List Blob :=
  records3608_3609 ++ records3609_3610
theorem aligned3608_3610 :
    AlignedValid 12 4 missing3608_3610 records3608_3610 :=
  aligned3608_3609.append aligned3609_3610

def missing3610_3611 : List (BitVec (edgeCount 12)) :=
  [missing3610]
abbrev records3610_3611 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3610]
theorem aligned3610_3611 :
    AlignedValid 12 4 missing3610_3611 records3610_3611 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3610
    maskCheck3610 AlignedValid.nil

def missing3611_3612 : List (BitVec (edgeCount 12)) :=
  [missing3611]
abbrev records3611_3612 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3611]
theorem aligned3611_3612 :
    AlignedValid 12 4 missing3611_3612 records3611_3612 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3611
    maskCheck3611 AlignedValid.nil

def missing3610_3612 : List (BitVec (edgeCount 12)) :=
  missing3610_3611 ++ missing3611_3612
abbrev records3610_3612 : List Blob :=
  records3610_3611 ++ records3611_3612
theorem aligned3610_3612 :
    AlignedValid 12 4 missing3610_3612 records3610_3612 :=
  aligned3610_3611.append aligned3611_3612

def missing3608_3612 : List (BitVec (edgeCount 12)) :=
  missing3608_3610 ++ missing3610_3612
abbrev records3608_3612 : List Blob :=
  records3608_3610 ++ records3610_3612
theorem aligned3608_3612 :
    AlignedValid 12 4 missing3608_3612 records3608_3612 :=
  aligned3608_3610.append aligned3610_3612

def missing3612_3613 : List (BitVec (edgeCount 12)) :=
  [missing3612]
abbrev records3612_3613 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3612]
theorem aligned3612_3613 :
    AlignedValid 12 4 missing3612_3613 records3612_3613 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3612
    maskCheck3612 AlignedValid.nil

def missing3613_3614 : List (BitVec (edgeCount 12)) :=
  [missing3613]
abbrev records3613_3614 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3613]
theorem aligned3613_3614 :
    AlignedValid 12 4 missing3613_3614 records3613_3614 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3613
    maskCheck3613 AlignedValid.nil

def missing3612_3614 : List (BitVec (edgeCount 12)) :=
  missing3612_3613 ++ missing3613_3614
abbrev records3612_3614 : List Blob :=
  records3612_3613 ++ records3613_3614
theorem aligned3612_3614 :
    AlignedValid 12 4 missing3612_3614 records3612_3614 :=
  aligned3612_3613.append aligned3613_3614

def missing3614_3615 : List (BitVec (edgeCount 12)) :=
  [missing3614]
abbrev records3614_3615 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3614]
theorem aligned3614_3615 :
    AlignedValid 12 4 missing3614_3615 records3614_3615 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3614
    maskCheck3614 AlignedValid.nil

def missing3615_3616 : List (BitVec (edgeCount 12)) :=
  [missing3615]
abbrev records3615_3616 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3615]
theorem aligned3615_3616 :
    AlignedValid 12 4 missing3615_3616 records3615_3616 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3615
    maskCheck3615 AlignedValid.nil

def missing3614_3616 : List (BitVec (edgeCount 12)) :=
  missing3614_3615 ++ missing3615_3616
abbrev records3614_3616 : List Blob :=
  records3614_3615 ++ records3615_3616
theorem aligned3614_3616 :
    AlignedValid 12 4 missing3614_3616 records3614_3616 :=
  aligned3614_3615.append aligned3615_3616

def missing3612_3616 : List (BitVec (edgeCount 12)) :=
  missing3612_3614 ++ missing3614_3616
abbrev records3612_3616 : List Blob :=
  records3612_3614 ++ records3614_3616
theorem aligned3612_3616 :
    AlignedValid 12 4 missing3612_3616 records3612_3616 :=
  aligned3612_3614.append aligned3614_3616

def missing3608_3616 : List (BitVec (edgeCount 12)) :=
  missing3608_3612 ++ missing3612_3616
abbrev records3608_3616 : List Blob :=
  records3608_3612 ++ records3612_3616
theorem aligned3608_3616 :
    AlignedValid 12 4 missing3608_3616 records3608_3616 :=
  aligned3608_3612.append aligned3612_3616

def missing3600_3616 : List (BitVec (edgeCount 12)) :=
  missing3600_3608 ++ missing3608_3616
abbrev records3600_3616 : List Blob :=
  records3600_3608 ++ records3608_3616
theorem aligned3600_3616 :
    AlignedValid 12 4 missing3600_3616 records3600_3616 :=
  aligned3600_3608.append aligned3608_3616

def missing3584_3616 : List (BitVec (edgeCount 12)) :=
  missing3584_3600 ++ missing3600_3616
abbrev records3584_3616 : List Blob :=
  records3584_3600 ++ records3600_3616
theorem aligned3584_3616 :
    AlignedValid 12 4 missing3584_3616 records3584_3616 :=
  aligned3584_3600.append aligned3600_3616

def missing3616_3617 : List (BitVec (edgeCount 12)) :=
  [missing3616]
abbrev records3616_3617 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3616]
theorem aligned3616_3617 :
    AlignedValid 12 4 missing3616_3617 records3616_3617 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3616
    maskCheck3616 AlignedValid.nil

def missing3617_3618 : List (BitVec (edgeCount 12)) :=
  [missing3617]
abbrev records3617_3618 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3617]
theorem aligned3617_3618 :
    AlignedValid 12 4 missing3617_3618 records3617_3618 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3617
    maskCheck3617 AlignedValid.nil

def missing3616_3618 : List (BitVec (edgeCount 12)) :=
  missing3616_3617 ++ missing3617_3618
abbrev records3616_3618 : List Blob :=
  records3616_3617 ++ records3617_3618
theorem aligned3616_3618 :
    AlignedValid 12 4 missing3616_3618 records3616_3618 :=
  aligned3616_3617.append aligned3617_3618

def missing3618_3619 : List (BitVec (edgeCount 12)) :=
  [missing3618]
abbrev records3618_3619 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3618]
theorem aligned3618_3619 :
    AlignedValid 12 4 missing3618_3619 records3618_3619 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3618
    maskCheck3618 AlignedValid.nil

def missing3619_3620 : List (BitVec (edgeCount 12)) :=
  [missing3619]
abbrev records3619_3620 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3619]
theorem aligned3619_3620 :
    AlignedValid 12 4 missing3619_3620 records3619_3620 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3619
    maskCheck3619 AlignedValid.nil

def missing3618_3620 : List (BitVec (edgeCount 12)) :=
  missing3618_3619 ++ missing3619_3620
abbrev records3618_3620 : List Blob :=
  records3618_3619 ++ records3619_3620
theorem aligned3618_3620 :
    AlignedValid 12 4 missing3618_3620 records3618_3620 :=
  aligned3618_3619.append aligned3619_3620

def missing3616_3620 : List (BitVec (edgeCount 12)) :=
  missing3616_3618 ++ missing3618_3620
abbrev records3616_3620 : List Blob :=
  records3616_3618 ++ records3618_3620
theorem aligned3616_3620 :
    AlignedValid 12 4 missing3616_3620 records3616_3620 :=
  aligned3616_3618.append aligned3618_3620

def missing3620_3621 : List (BitVec (edgeCount 12)) :=
  [missing3620]
abbrev records3620_3621 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3620]
theorem aligned3620_3621 :
    AlignedValid 12 4 missing3620_3621 records3620_3621 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3620
    maskCheck3620 AlignedValid.nil

def missing3621_3622 : List (BitVec (edgeCount 12)) :=
  [missing3621]
abbrev records3621_3622 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3621]
theorem aligned3621_3622 :
    AlignedValid 12 4 missing3621_3622 records3621_3622 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3621
    maskCheck3621 AlignedValid.nil

def missing3620_3622 : List (BitVec (edgeCount 12)) :=
  missing3620_3621 ++ missing3621_3622
abbrev records3620_3622 : List Blob :=
  records3620_3621 ++ records3621_3622
theorem aligned3620_3622 :
    AlignedValid 12 4 missing3620_3622 records3620_3622 :=
  aligned3620_3621.append aligned3621_3622

def missing3622_3623 : List (BitVec (edgeCount 12)) :=
  [missing3622]
abbrev records3622_3623 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3622]
theorem aligned3622_3623 :
    AlignedValid 12 4 missing3622_3623 records3622_3623 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3622
    maskCheck3622 AlignedValid.nil

def missing3623_3624 : List (BitVec (edgeCount 12)) :=
  [missing3623]
abbrev records3623_3624 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3623]
theorem aligned3623_3624 :
    AlignedValid 12 4 missing3623_3624 records3623_3624 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3623
    maskCheck3623 AlignedValid.nil

def missing3622_3624 : List (BitVec (edgeCount 12)) :=
  missing3622_3623 ++ missing3623_3624
abbrev records3622_3624 : List Blob :=
  records3622_3623 ++ records3623_3624
theorem aligned3622_3624 :
    AlignedValid 12 4 missing3622_3624 records3622_3624 :=
  aligned3622_3623.append aligned3623_3624

def missing3620_3624 : List (BitVec (edgeCount 12)) :=
  missing3620_3622 ++ missing3622_3624
abbrev records3620_3624 : List Blob :=
  records3620_3622 ++ records3622_3624
theorem aligned3620_3624 :
    AlignedValid 12 4 missing3620_3624 records3620_3624 :=
  aligned3620_3622.append aligned3622_3624

def missing3616_3624 : List (BitVec (edgeCount 12)) :=
  missing3616_3620 ++ missing3620_3624
abbrev records3616_3624 : List Blob :=
  records3616_3620 ++ records3620_3624
theorem aligned3616_3624 :
    AlignedValid 12 4 missing3616_3624 records3616_3624 :=
  aligned3616_3620.append aligned3620_3624

def missing3624_3625 : List (BitVec (edgeCount 12)) :=
  [missing3624]
abbrev records3624_3625 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3624]
theorem aligned3624_3625 :
    AlignedValid 12 4 missing3624_3625 records3624_3625 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3624
    maskCheck3624 AlignedValid.nil

def missing3625_3626 : List (BitVec (edgeCount 12)) :=
  [missing3625]
abbrev records3625_3626 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3625]
theorem aligned3625_3626 :
    AlignedValid 12 4 missing3625_3626 records3625_3626 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3625
    maskCheck3625 AlignedValid.nil

def missing3624_3626 : List (BitVec (edgeCount 12)) :=
  missing3624_3625 ++ missing3625_3626
abbrev records3624_3626 : List Blob :=
  records3624_3625 ++ records3625_3626
theorem aligned3624_3626 :
    AlignedValid 12 4 missing3624_3626 records3624_3626 :=
  aligned3624_3625.append aligned3625_3626

def missing3626_3627 : List (BitVec (edgeCount 12)) :=
  [missing3626]
abbrev records3626_3627 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3626]
theorem aligned3626_3627 :
    AlignedValid 12 4 missing3626_3627 records3626_3627 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3626
    maskCheck3626 AlignedValid.nil

def missing3627_3628 : List (BitVec (edgeCount 12)) :=
  [missing3627]
abbrev records3627_3628 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3627]
theorem aligned3627_3628 :
    AlignedValid 12 4 missing3627_3628 records3627_3628 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3627
    maskCheck3627 AlignedValid.nil

def missing3626_3628 : List (BitVec (edgeCount 12)) :=
  missing3626_3627 ++ missing3627_3628
abbrev records3626_3628 : List Blob :=
  records3626_3627 ++ records3627_3628
theorem aligned3626_3628 :
    AlignedValid 12 4 missing3626_3628 records3626_3628 :=
  aligned3626_3627.append aligned3627_3628

def missing3624_3628 : List (BitVec (edgeCount 12)) :=
  missing3624_3626 ++ missing3626_3628
abbrev records3624_3628 : List Blob :=
  records3624_3626 ++ records3626_3628
theorem aligned3624_3628 :
    AlignedValid 12 4 missing3624_3628 records3624_3628 :=
  aligned3624_3626.append aligned3626_3628

def missing3628_3629 : List (BitVec (edgeCount 12)) :=
  [missing3628]
abbrev records3628_3629 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3628]
theorem aligned3628_3629 :
    AlignedValid 12 4 missing3628_3629 records3628_3629 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3628
    maskCheck3628 AlignedValid.nil

def missing3629_3630 : List (BitVec (edgeCount 12)) :=
  [missing3629]
abbrev records3629_3630 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3629]
theorem aligned3629_3630 :
    AlignedValid 12 4 missing3629_3630 records3629_3630 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3629
    maskCheck3629 AlignedValid.nil

def missing3628_3630 : List (BitVec (edgeCount 12)) :=
  missing3628_3629 ++ missing3629_3630
abbrev records3628_3630 : List Blob :=
  records3628_3629 ++ records3629_3630
theorem aligned3628_3630 :
    AlignedValid 12 4 missing3628_3630 records3628_3630 :=
  aligned3628_3629.append aligned3629_3630

def missing3630_3631 : List (BitVec (edgeCount 12)) :=
  [missing3630]
abbrev records3630_3631 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3630]
theorem aligned3630_3631 :
    AlignedValid 12 4 missing3630_3631 records3630_3631 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3630
    maskCheck3630 AlignedValid.nil

def missing3631_3632 : List (BitVec (edgeCount 12)) :=
  [missing3631]
abbrev records3631_3632 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3631]
theorem aligned3631_3632 :
    AlignedValid 12 4 missing3631_3632 records3631_3632 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3631
    maskCheck3631 AlignedValid.nil

def missing3630_3632 : List (BitVec (edgeCount 12)) :=
  missing3630_3631 ++ missing3631_3632
abbrev records3630_3632 : List Blob :=
  records3630_3631 ++ records3631_3632
theorem aligned3630_3632 :
    AlignedValid 12 4 missing3630_3632 records3630_3632 :=
  aligned3630_3631.append aligned3631_3632

def missing3628_3632 : List (BitVec (edgeCount 12)) :=
  missing3628_3630 ++ missing3630_3632
abbrev records3628_3632 : List Blob :=
  records3628_3630 ++ records3630_3632
theorem aligned3628_3632 :
    AlignedValid 12 4 missing3628_3632 records3628_3632 :=
  aligned3628_3630.append aligned3630_3632

def missing3624_3632 : List (BitVec (edgeCount 12)) :=
  missing3624_3628 ++ missing3628_3632
abbrev records3624_3632 : List Blob :=
  records3624_3628 ++ records3628_3632
theorem aligned3624_3632 :
    AlignedValid 12 4 missing3624_3632 records3624_3632 :=
  aligned3624_3628.append aligned3628_3632

def missing3616_3632 : List (BitVec (edgeCount 12)) :=
  missing3616_3624 ++ missing3624_3632
abbrev records3616_3632 : List Blob :=
  records3616_3624 ++ records3624_3632
theorem aligned3616_3632 :
    AlignedValid 12 4 missing3616_3632 records3616_3632 :=
  aligned3616_3624.append aligned3624_3632

def missing3632_3633 : List (BitVec (edgeCount 12)) :=
  [missing3632]
abbrev records3632_3633 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3632]
theorem aligned3632_3633 :
    AlignedValid 12 4 missing3632_3633 records3632_3633 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3632
    maskCheck3632 AlignedValid.nil

def missing3633_3634 : List (BitVec (edgeCount 12)) :=
  [missing3633]
abbrev records3633_3634 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3633]
theorem aligned3633_3634 :
    AlignedValid 12 4 missing3633_3634 records3633_3634 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3633
    maskCheck3633 AlignedValid.nil

def missing3632_3634 : List (BitVec (edgeCount 12)) :=
  missing3632_3633 ++ missing3633_3634
abbrev records3632_3634 : List Blob :=
  records3632_3633 ++ records3633_3634
theorem aligned3632_3634 :
    AlignedValid 12 4 missing3632_3634 records3632_3634 :=
  aligned3632_3633.append aligned3633_3634

def missing3634_3635 : List (BitVec (edgeCount 12)) :=
  [missing3634]
abbrev records3634_3635 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3634]
theorem aligned3634_3635 :
    AlignedValid 12 4 missing3634_3635 records3634_3635 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3634
    maskCheck3634 AlignedValid.nil

def missing3635_3636 : List (BitVec (edgeCount 12)) :=
  [missing3635]
abbrev records3635_3636 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3635]
theorem aligned3635_3636 :
    AlignedValid 12 4 missing3635_3636 records3635_3636 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3635
    maskCheck3635 AlignedValid.nil

def missing3634_3636 : List (BitVec (edgeCount 12)) :=
  missing3634_3635 ++ missing3635_3636
abbrev records3634_3636 : List Blob :=
  records3634_3635 ++ records3635_3636
theorem aligned3634_3636 :
    AlignedValid 12 4 missing3634_3636 records3634_3636 :=
  aligned3634_3635.append aligned3635_3636

def missing3632_3636 : List (BitVec (edgeCount 12)) :=
  missing3632_3634 ++ missing3634_3636
abbrev records3632_3636 : List Blob :=
  records3632_3634 ++ records3634_3636
theorem aligned3632_3636 :
    AlignedValid 12 4 missing3632_3636 records3632_3636 :=
  aligned3632_3634.append aligned3634_3636

def missing3636_3637 : List (BitVec (edgeCount 12)) :=
  [missing3636]
abbrev records3636_3637 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3636]
theorem aligned3636_3637 :
    AlignedValid 12 4 missing3636_3637 records3636_3637 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3636
    maskCheck3636 AlignedValid.nil

def missing3637_3638 : List (BitVec (edgeCount 12)) :=
  [missing3637]
abbrev records3637_3638 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3637]
theorem aligned3637_3638 :
    AlignedValid 12 4 missing3637_3638 records3637_3638 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3637
    maskCheck3637 AlignedValid.nil

def missing3636_3638 : List (BitVec (edgeCount 12)) :=
  missing3636_3637 ++ missing3637_3638
abbrev records3636_3638 : List Blob :=
  records3636_3637 ++ records3637_3638
theorem aligned3636_3638 :
    AlignedValid 12 4 missing3636_3638 records3636_3638 :=
  aligned3636_3637.append aligned3637_3638

def missing3638_3639 : List (BitVec (edgeCount 12)) :=
  [missing3638]
abbrev records3638_3639 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3638]
theorem aligned3638_3639 :
    AlignedValid 12 4 missing3638_3639 records3638_3639 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3638
    maskCheck3638 AlignedValid.nil

def missing3639_3640 : List (BitVec (edgeCount 12)) :=
  [missing3639]
abbrev records3639_3640 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3639]
theorem aligned3639_3640 :
    AlignedValid 12 4 missing3639_3640 records3639_3640 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3639
    maskCheck3639 AlignedValid.nil

def missing3638_3640 : List (BitVec (edgeCount 12)) :=
  missing3638_3639 ++ missing3639_3640
abbrev records3638_3640 : List Blob :=
  records3638_3639 ++ records3639_3640
theorem aligned3638_3640 :
    AlignedValid 12 4 missing3638_3640 records3638_3640 :=
  aligned3638_3639.append aligned3639_3640

def missing3636_3640 : List (BitVec (edgeCount 12)) :=
  missing3636_3638 ++ missing3638_3640
abbrev records3636_3640 : List Blob :=
  records3636_3638 ++ records3638_3640
theorem aligned3636_3640 :
    AlignedValid 12 4 missing3636_3640 records3636_3640 :=
  aligned3636_3638.append aligned3638_3640

def missing3632_3640 : List (BitVec (edgeCount 12)) :=
  missing3632_3636 ++ missing3636_3640
abbrev records3632_3640 : List Blob :=
  records3632_3636 ++ records3636_3640
theorem aligned3632_3640 :
    AlignedValid 12 4 missing3632_3640 records3632_3640 :=
  aligned3632_3636.append aligned3636_3640

def missing3640_3641 : List (BitVec (edgeCount 12)) :=
  [missing3640]
abbrev records3640_3641 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3640]
theorem aligned3640_3641 :
    AlignedValid 12 4 missing3640_3641 records3640_3641 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3640
    maskCheck3640 AlignedValid.nil

def missing3641_3642 : List (BitVec (edgeCount 12)) :=
  [missing3641]
abbrev records3641_3642 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3641]
theorem aligned3641_3642 :
    AlignedValid 12 4 missing3641_3642 records3641_3642 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3641
    maskCheck3641 AlignedValid.nil

def missing3640_3642 : List (BitVec (edgeCount 12)) :=
  missing3640_3641 ++ missing3641_3642
abbrev records3640_3642 : List Blob :=
  records3640_3641 ++ records3641_3642
theorem aligned3640_3642 :
    AlignedValid 12 4 missing3640_3642 records3640_3642 :=
  aligned3640_3641.append aligned3641_3642

def missing3642_3643 : List (BitVec (edgeCount 12)) :=
  [missing3642]
abbrev records3642_3643 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3642]
theorem aligned3642_3643 :
    AlignedValid 12 4 missing3642_3643 records3642_3643 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3642
    maskCheck3642 AlignedValid.nil

def missing3643_3644 : List (BitVec (edgeCount 12)) :=
  [missing3643]
abbrev records3643_3644 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3643]
theorem aligned3643_3644 :
    AlignedValid 12 4 missing3643_3644 records3643_3644 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3643
    maskCheck3643 AlignedValid.nil

def missing3642_3644 : List (BitVec (edgeCount 12)) :=
  missing3642_3643 ++ missing3643_3644
abbrev records3642_3644 : List Blob :=
  records3642_3643 ++ records3643_3644
theorem aligned3642_3644 :
    AlignedValid 12 4 missing3642_3644 records3642_3644 :=
  aligned3642_3643.append aligned3643_3644

def missing3640_3644 : List (BitVec (edgeCount 12)) :=
  missing3640_3642 ++ missing3642_3644
abbrev records3640_3644 : List Blob :=
  records3640_3642 ++ records3642_3644
theorem aligned3640_3644 :
    AlignedValid 12 4 missing3640_3644 records3640_3644 :=
  aligned3640_3642.append aligned3642_3644

def missing3644_3645 : List (BitVec (edgeCount 12)) :=
  [missing3644]
abbrev records3644_3645 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3644]
theorem aligned3644_3645 :
    AlignedValid 12 4 missing3644_3645 records3644_3645 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3644
    maskCheck3644 AlignedValid.nil

def missing3645_3646 : List (BitVec (edgeCount 12)) :=
  [missing3645]
abbrev records3645_3646 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3645]
theorem aligned3645_3646 :
    AlignedValid 12 4 missing3645_3646 records3645_3646 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3645
    maskCheck3645 AlignedValid.nil

def missing3644_3646 : List (BitVec (edgeCount 12)) :=
  missing3644_3645 ++ missing3645_3646
abbrev records3644_3646 : List Blob :=
  records3644_3645 ++ records3645_3646
theorem aligned3644_3646 :
    AlignedValid 12 4 missing3644_3646 records3644_3646 :=
  aligned3644_3645.append aligned3645_3646

def missing3646_3647 : List (BitVec (edgeCount 12)) :=
  [missing3646]
abbrev records3646_3647 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3646]
theorem aligned3646_3647 :
    AlignedValid 12 4 missing3646_3647 records3646_3647 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3646
    maskCheck3646 AlignedValid.nil

def missing3647_3648 : List (BitVec (edgeCount 12)) :=
  [missing3647]
abbrev records3647_3648 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3647]
theorem aligned3647_3648 :
    AlignedValid 12 4 missing3647_3648 records3647_3648 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3647
    maskCheck3647 AlignedValid.nil

def missing3646_3648 : List (BitVec (edgeCount 12)) :=
  missing3646_3647 ++ missing3647_3648
abbrev records3646_3648 : List Blob :=
  records3646_3647 ++ records3647_3648
theorem aligned3646_3648 :
    AlignedValid 12 4 missing3646_3648 records3646_3648 :=
  aligned3646_3647.append aligned3647_3648

def missing3644_3648 : List (BitVec (edgeCount 12)) :=
  missing3644_3646 ++ missing3646_3648
abbrev records3644_3648 : List Blob :=
  records3644_3646 ++ records3646_3648
theorem aligned3644_3648 :
    AlignedValid 12 4 missing3644_3648 records3644_3648 :=
  aligned3644_3646.append aligned3646_3648

def missing3640_3648 : List (BitVec (edgeCount 12)) :=
  missing3640_3644 ++ missing3644_3648
abbrev records3640_3648 : List Blob :=
  records3640_3644 ++ records3644_3648
theorem aligned3640_3648 :
    AlignedValid 12 4 missing3640_3648 records3640_3648 :=
  aligned3640_3644.append aligned3644_3648

def missing3632_3648 : List (BitVec (edgeCount 12)) :=
  missing3632_3640 ++ missing3640_3648
abbrev records3632_3648 : List Blob :=
  records3632_3640 ++ records3640_3648
theorem aligned3632_3648 :
    AlignedValid 12 4 missing3632_3648 records3632_3648 :=
  aligned3632_3640.append aligned3640_3648

def missing3616_3648 : List (BitVec (edgeCount 12)) :=
  missing3616_3632 ++ missing3632_3648
abbrev records3616_3648 : List Blob :=
  records3616_3632 ++ records3632_3648
theorem aligned3616_3648 :
    AlignedValid 12 4 missing3616_3648 records3616_3648 :=
  aligned3616_3632.append aligned3632_3648

def missing3584_3648 : List (BitVec (edgeCount 12)) :=
  missing3584_3616 ++ missing3616_3648
abbrev records3584_3648 : List Blob :=
  records3584_3616 ++ records3616_3648
theorem aligned3584_3648 :
    AlignedValid 12 4 missing3584_3648 records3584_3648 :=
  aligned3584_3616.append aligned3616_3648

def missing3648_3649 : List (BitVec (edgeCount 12)) :=
  [missing3648]
abbrev records3648_3649 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3648]
theorem aligned3648_3649 :
    AlignedValid 12 4 missing3648_3649 records3648_3649 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3648
    maskCheck3648 AlignedValid.nil

def missing3649_3650 : List (BitVec (edgeCount 12)) :=
  [missing3649]
abbrev records3649_3650 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3649]
theorem aligned3649_3650 :
    AlignedValid 12 4 missing3649_3650 records3649_3650 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3649
    maskCheck3649 AlignedValid.nil

def missing3648_3650 : List (BitVec (edgeCount 12)) :=
  missing3648_3649 ++ missing3649_3650
abbrev records3648_3650 : List Blob :=
  records3648_3649 ++ records3649_3650
theorem aligned3648_3650 :
    AlignedValid 12 4 missing3648_3650 records3648_3650 :=
  aligned3648_3649.append aligned3649_3650

def missing3650_3651 : List (BitVec (edgeCount 12)) :=
  [missing3650]
abbrev records3650_3651 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3650]
theorem aligned3650_3651 :
    AlignedValid 12 4 missing3650_3651 records3650_3651 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3650
    maskCheck3650 AlignedValid.nil

def missing3651_3652 : List (BitVec (edgeCount 12)) :=
  [missing3651]
abbrev records3651_3652 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3651]
theorem aligned3651_3652 :
    AlignedValid 12 4 missing3651_3652 records3651_3652 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3651
    maskCheck3651 AlignedValid.nil

def missing3650_3652 : List (BitVec (edgeCount 12)) :=
  missing3650_3651 ++ missing3651_3652
abbrev records3650_3652 : List Blob :=
  records3650_3651 ++ records3651_3652
theorem aligned3650_3652 :
    AlignedValid 12 4 missing3650_3652 records3650_3652 :=
  aligned3650_3651.append aligned3651_3652

def missing3648_3652 : List (BitVec (edgeCount 12)) :=
  missing3648_3650 ++ missing3650_3652
abbrev records3648_3652 : List Blob :=
  records3648_3650 ++ records3650_3652
theorem aligned3648_3652 :
    AlignedValid 12 4 missing3648_3652 records3648_3652 :=
  aligned3648_3650.append aligned3650_3652

def missing3652_3653 : List (BitVec (edgeCount 12)) :=
  [missing3652]
abbrev records3652_3653 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3652]
theorem aligned3652_3653 :
    AlignedValid 12 4 missing3652_3653 records3652_3653 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3652
    maskCheck3652 AlignedValid.nil

def missing3653_3654 : List (BitVec (edgeCount 12)) :=
  [missing3653]
abbrev records3653_3654 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3653]
theorem aligned3653_3654 :
    AlignedValid 12 4 missing3653_3654 records3653_3654 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3653
    maskCheck3653 AlignedValid.nil

def missing3652_3654 : List (BitVec (edgeCount 12)) :=
  missing3652_3653 ++ missing3653_3654
abbrev records3652_3654 : List Blob :=
  records3652_3653 ++ records3653_3654
theorem aligned3652_3654 :
    AlignedValid 12 4 missing3652_3654 records3652_3654 :=
  aligned3652_3653.append aligned3653_3654

def missing3654_3655 : List (BitVec (edgeCount 12)) :=
  [missing3654]
abbrev records3654_3655 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3654]
theorem aligned3654_3655 :
    AlignedValid 12 4 missing3654_3655 records3654_3655 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3654
    maskCheck3654 AlignedValid.nil

def missing3655_3656 : List (BitVec (edgeCount 12)) :=
  [missing3655]
abbrev records3655_3656 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3655]
theorem aligned3655_3656 :
    AlignedValid 12 4 missing3655_3656 records3655_3656 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3655
    maskCheck3655 AlignedValid.nil

def missing3654_3656 : List (BitVec (edgeCount 12)) :=
  missing3654_3655 ++ missing3655_3656
abbrev records3654_3656 : List Blob :=
  records3654_3655 ++ records3655_3656
theorem aligned3654_3656 :
    AlignedValid 12 4 missing3654_3656 records3654_3656 :=
  aligned3654_3655.append aligned3655_3656

def missing3652_3656 : List (BitVec (edgeCount 12)) :=
  missing3652_3654 ++ missing3654_3656
abbrev records3652_3656 : List Blob :=
  records3652_3654 ++ records3654_3656
theorem aligned3652_3656 :
    AlignedValid 12 4 missing3652_3656 records3652_3656 :=
  aligned3652_3654.append aligned3654_3656

def missing3648_3656 : List (BitVec (edgeCount 12)) :=
  missing3648_3652 ++ missing3652_3656
abbrev records3648_3656 : List Blob :=
  records3648_3652 ++ records3652_3656
theorem aligned3648_3656 :
    AlignedValid 12 4 missing3648_3656 records3648_3656 :=
  aligned3648_3652.append aligned3652_3656

def missing3656_3657 : List (BitVec (edgeCount 12)) :=
  [missing3656]
abbrev records3656_3657 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3656]
theorem aligned3656_3657 :
    AlignedValid 12 4 missing3656_3657 records3656_3657 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3656
    maskCheck3656 AlignedValid.nil

def missing3657_3658 : List (BitVec (edgeCount 12)) :=
  [missing3657]
abbrev records3657_3658 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3657]
theorem aligned3657_3658 :
    AlignedValid 12 4 missing3657_3658 records3657_3658 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3657
    maskCheck3657 AlignedValid.nil

def missing3656_3658 : List (BitVec (edgeCount 12)) :=
  missing3656_3657 ++ missing3657_3658
abbrev records3656_3658 : List Blob :=
  records3656_3657 ++ records3657_3658
theorem aligned3656_3658 :
    AlignedValid 12 4 missing3656_3658 records3656_3658 :=
  aligned3656_3657.append aligned3657_3658

def missing3658_3659 : List (BitVec (edgeCount 12)) :=
  [missing3658]
abbrev records3658_3659 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3658]
theorem aligned3658_3659 :
    AlignedValid 12 4 missing3658_3659 records3658_3659 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3658
    maskCheck3658 AlignedValid.nil

def missing3659_3660 : List (BitVec (edgeCount 12)) :=
  [missing3659]
abbrev records3659_3660 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3659]
theorem aligned3659_3660 :
    AlignedValid 12 4 missing3659_3660 records3659_3660 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3659
    maskCheck3659 AlignedValid.nil

def missing3658_3660 : List (BitVec (edgeCount 12)) :=
  missing3658_3659 ++ missing3659_3660
abbrev records3658_3660 : List Blob :=
  records3658_3659 ++ records3659_3660
theorem aligned3658_3660 :
    AlignedValid 12 4 missing3658_3660 records3658_3660 :=
  aligned3658_3659.append aligned3659_3660

def missing3656_3660 : List (BitVec (edgeCount 12)) :=
  missing3656_3658 ++ missing3658_3660
abbrev records3656_3660 : List Blob :=
  records3656_3658 ++ records3658_3660
theorem aligned3656_3660 :
    AlignedValid 12 4 missing3656_3660 records3656_3660 :=
  aligned3656_3658.append aligned3658_3660

def missing3660_3661 : List (BitVec (edgeCount 12)) :=
  [missing3660]
abbrev records3660_3661 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3660]
theorem aligned3660_3661 :
    AlignedValid 12 4 missing3660_3661 records3660_3661 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3660
    maskCheck3660 AlignedValid.nil

def missing3661_3662 : List (BitVec (edgeCount 12)) :=
  [missing3661]
abbrev records3661_3662 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3661]
theorem aligned3661_3662 :
    AlignedValid 12 4 missing3661_3662 records3661_3662 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3661
    maskCheck3661 AlignedValid.nil

def missing3660_3662 : List (BitVec (edgeCount 12)) :=
  missing3660_3661 ++ missing3661_3662
abbrev records3660_3662 : List Blob :=
  records3660_3661 ++ records3661_3662
theorem aligned3660_3662 :
    AlignedValid 12 4 missing3660_3662 records3660_3662 :=
  aligned3660_3661.append aligned3661_3662

def missing3662_3663 : List (BitVec (edgeCount 12)) :=
  [missing3662]
abbrev records3662_3663 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3662]
theorem aligned3662_3663 :
    AlignedValid 12 4 missing3662_3663 records3662_3663 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3662
    maskCheck3662 AlignedValid.nil

def missing3663_3664 : List (BitVec (edgeCount 12)) :=
  [missing3663]
abbrev records3663_3664 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3663]
theorem aligned3663_3664 :
    AlignedValid 12 4 missing3663_3664 records3663_3664 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3663
    maskCheck3663 AlignedValid.nil

def missing3662_3664 : List (BitVec (edgeCount 12)) :=
  missing3662_3663 ++ missing3663_3664
abbrev records3662_3664 : List Blob :=
  records3662_3663 ++ records3663_3664
theorem aligned3662_3664 :
    AlignedValid 12 4 missing3662_3664 records3662_3664 :=
  aligned3662_3663.append aligned3663_3664

def missing3660_3664 : List (BitVec (edgeCount 12)) :=
  missing3660_3662 ++ missing3662_3664
abbrev records3660_3664 : List Blob :=
  records3660_3662 ++ records3662_3664
theorem aligned3660_3664 :
    AlignedValid 12 4 missing3660_3664 records3660_3664 :=
  aligned3660_3662.append aligned3662_3664

def missing3656_3664 : List (BitVec (edgeCount 12)) :=
  missing3656_3660 ++ missing3660_3664
abbrev records3656_3664 : List Blob :=
  records3656_3660 ++ records3660_3664
theorem aligned3656_3664 :
    AlignedValid 12 4 missing3656_3664 records3656_3664 :=
  aligned3656_3660.append aligned3660_3664

def missing3648_3664 : List (BitVec (edgeCount 12)) :=
  missing3648_3656 ++ missing3656_3664
abbrev records3648_3664 : List Blob :=
  records3648_3656 ++ records3656_3664
theorem aligned3648_3664 :
    AlignedValid 12 4 missing3648_3664 records3648_3664 :=
  aligned3648_3656.append aligned3656_3664

def missing3664_3665 : List (BitVec (edgeCount 12)) :=
  [missing3664]
abbrev records3664_3665 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3664]
theorem aligned3664_3665 :
    AlignedValid 12 4 missing3664_3665 records3664_3665 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3664
    maskCheck3664 AlignedValid.nil

def missing3665_3666 : List (BitVec (edgeCount 12)) :=
  [missing3665]
abbrev records3665_3666 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3665]
theorem aligned3665_3666 :
    AlignedValid 12 4 missing3665_3666 records3665_3666 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3665
    maskCheck3665 AlignedValid.nil

def missing3664_3666 : List (BitVec (edgeCount 12)) :=
  missing3664_3665 ++ missing3665_3666
abbrev records3664_3666 : List Blob :=
  records3664_3665 ++ records3665_3666
theorem aligned3664_3666 :
    AlignedValid 12 4 missing3664_3666 records3664_3666 :=
  aligned3664_3665.append aligned3665_3666

def missing3666_3667 : List (BitVec (edgeCount 12)) :=
  [missing3666]
abbrev records3666_3667 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3666]
theorem aligned3666_3667 :
    AlignedValid 12 4 missing3666_3667 records3666_3667 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3666
    maskCheck3666 AlignedValid.nil

def missing3667_3668 : List (BitVec (edgeCount 12)) :=
  [missing3667]
abbrev records3667_3668 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3667]
theorem aligned3667_3668 :
    AlignedValid 12 4 missing3667_3668 records3667_3668 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3667
    maskCheck3667 AlignedValid.nil

def missing3666_3668 : List (BitVec (edgeCount 12)) :=
  missing3666_3667 ++ missing3667_3668
abbrev records3666_3668 : List Blob :=
  records3666_3667 ++ records3667_3668
theorem aligned3666_3668 :
    AlignedValid 12 4 missing3666_3668 records3666_3668 :=
  aligned3666_3667.append aligned3667_3668

def missing3664_3668 : List (BitVec (edgeCount 12)) :=
  missing3664_3666 ++ missing3666_3668
abbrev records3664_3668 : List Blob :=
  records3664_3666 ++ records3666_3668
theorem aligned3664_3668 :
    AlignedValid 12 4 missing3664_3668 records3664_3668 :=
  aligned3664_3666.append aligned3666_3668

def missing3668_3669 : List (BitVec (edgeCount 12)) :=
  [missing3668]
abbrev records3668_3669 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3668]
theorem aligned3668_3669 :
    AlignedValid 12 4 missing3668_3669 records3668_3669 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3668
    maskCheck3668 AlignedValid.nil

def missing3669_3670 : List (BitVec (edgeCount 12)) :=
  [missing3669]
abbrev records3669_3670 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3669]
theorem aligned3669_3670 :
    AlignedValid 12 4 missing3669_3670 records3669_3670 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3669
    maskCheck3669 AlignedValid.nil

def missing3668_3670 : List (BitVec (edgeCount 12)) :=
  missing3668_3669 ++ missing3669_3670
abbrev records3668_3670 : List Blob :=
  records3668_3669 ++ records3669_3670
theorem aligned3668_3670 :
    AlignedValid 12 4 missing3668_3670 records3668_3670 :=
  aligned3668_3669.append aligned3669_3670

def missing3670_3671 : List (BitVec (edgeCount 12)) :=
  [missing3670]
abbrev records3670_3671 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3670]
theorem aligned3670_3671 :
    AlignedValid 12 4 missing3670_3671 records3670_3671 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3670
    maskCheck3670 AlignedValid.nil

def missing3671_3672 : List (BitVec (edgeCount 12)) :=
  [missing3671]
abbrev records3671_3672 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3671]
theorem aligned3671_3672 :
    AlignedValid 12 4 missing3671_3672 records3671_3672 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3671
    maskCheck3671 AlignedValid.nil

def missing3670_3672 : List (BitVec (edgeCount 12)) :=
  missing3670_3671 ++ missing3671_3672
abbrev records3670_3672 : List Blob :=
  records3670_3671 ++ records3671_3672
theorem aligned3670_3672 :
    AlignedValid 12 4 missing3670_3672 records3670_3672 :=
  aligned3670_3671.append aligned3671_3672

def missing3668_3672 : List (BitVec (edgeCount 12)) :=
  missing3668_3670 ++ missing3670_3672
abbrev records3668_3672 : List Blob :=
  records3668_3670 ++ records3670_3672
theorem aligned3668_3672 :
    AlignedValid 12 4 missing3668_3672 records3668_3672 :=
  aligned3668_3670.append aligned3670_3672

def missing3664_3672 : List (BitVec (edgeCount 12)) :=
  missing3664_3668 ++ missing3668_3672
abbrev records3664_3672 : List Blob :=
  records3664_3668 ++ records3668_3672
theorem aligned3664_3672 :
    AlignedValid 12 4 missing3664_3672 records3664_3672 :=
  aligned3664_3668.append aligned3668_3672

def missing3672_3673 : List (BitVec (edgeCount 12)) :=
  [missing3672]
abbrev records3672_3673 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3672]
theorem aligned3672_3673 :
    AlignedValid 12 4 missing3672_3673 records3672_3673 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3672
    maskCheck3672 AlignedValid.nil

def missing3673_3674 : List (BitVec (edgeCount 12)) :=
  [missing3673]
abbrev records3673_3674 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3673]
theorem aligned3673_3674 :
    AlignedValid 12 4 missing3673_3674 records3673_3674 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3673
    maskCheck3673 AlignedValid.nil

def missing3672_3674 : List (BitVec (edgeCount 12)) :=
  missing3672_3673 ++ missing3673_3674
abbrev records3672_3674 : List Blob :=
  records3672_3673 ++ records3673_3674
theorem aligned3672_3674 :
    AlignedValid 12 4 missing3672_3674 records3672_3674 :=
  aligned3672_3673.append aligned3673_3674

def missing3674_3675 : List (BitVec (edgeCount 12)) :=
  [missing3674]
abbrev records3674_3675 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3674]
theorem aligned3674_3675 :
    AlignedValid 12 4 missing3674_3675 records3674_3675 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3674
    maskCheck3674 AlignedValid.nil

def missing3675_3676 : List (BitVec (edgeCount 12)) :=
  [missing3675]
abbrev records3675_3676 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3675]
theorem aligned3675_3676 :
    AlignedValid 12 4 missing3675_3676 records3675_3676 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3675
    maskCheck3675 AlignedValid.nil

def missing3674_3676 : List (BitVec (edgeCount 12)) :=
  missing3674_3675 ++ missing3675_3676
abbrev records3674_3676 : List Blob :=
  records3674_3675 ++ records3675_3676
theorem aligned3674_3676 :
    AlignedValid 12 4 missing3674_3676 records3674_3676 :=
  aligned3674_3675.append aligned3675_3676

def missing3672_3676 : List (BitVec (edgeCount 12)) :=
  missing3672_3674 ++ missing3674_3676
abbrev records3672_3676 : List Blob :=
  records3672_3674 ++ records3674_3676
theorem aligned3672_3676 :
    AlignedValid 12 4 missing3672_3676 records3672_3676 :=
  aligned3672_3674.append aligned3674_3676

def missing3676_3677 : List (BitVec (edgeCount 12)) :=
  [missing3676]
abbrev records3676_3677 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3676]
theorem aligned3676_3677 :
    AlignedValid 12 4 missing3676_3677 records3676_3677 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3676
    maskCheck3676 AlignedValid.nil

def missing3677_3678 : List (BitVec (edgeCount 12)) :=
  [missing3677]
abbrev records3677_3678 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3677]
theorem aligned3677_3678 :
    AlignedValid 12 4 missing3677_3678 records3677_3678 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3677
    maskCheck3677 AlignedValid.nil

def missing3676_3678 : List (BitVec (edgeCount 12)) :=
  missing3676_3677 ++ missing3677_3678
abbrev records3676_3678 : List Blob :=
  records3676_3677 ++ records3677_3678
theorem aligned3676_3678 :
    AlignedValid 12 4 missing3676_3678 records3676_3678 :=
  aligned3676_3677.append aligned3677_3678

def missing3678_3679 : List (BitVec (edgeCount 12)) :=
  [missing3678]
abbrev records3678_3679 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3678]
theorem aligned3678_3679 :
    AlignedValid 12 4 missing3678_3679 records3678_3679 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3678
    maskCheck3678 AlignedValid.nil

def missing3679_3680 : List (BitVec (edgeCount 12)) :=
  [missing3679]
abbrev records3679_3680 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3679]
theorem aligned3679_3680 :
    AlignedValid 12 4 missing3679_3680 records3679_3680 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3679
    maskCheck3679 AlignedValid.nil

def missing3678_3680 : List (BitVec (edgeCount 12)) :=
  missing3678_3679 ++ missing3679_3680
abbrev records3678_3680 : List Blob :=
  records3678_3679 ++ records3679_3680
theorem aligned3678_3680 :
    AlignedValid 12 4 missing3678_3680 records3678_3680 :=
  aligned3678_3679.append aligned3679_3680

def missing3676_3680 : List (BitVec (edgeCount 12)) :=
  missing3676_3678 ++ missing3678_3680
abbrev records3676_3680 : List Blob :=
  records3676_3678 ++ records3678_3680
theorem aligned3676_3680 :
    AlignedValid 12 4 missing3676_3680 records3676_3680 :=
  aligned3676_3678.append aligned3678_3680

def missing3672_3680 : List (BitVec (edgeCount 12)) :=
  missing3672_3676 ++ missing3676_3680
abbrev records3672_3680 : List Blob :=
  records3672_3676 ++ records3676_3680
theorem aligned3672_3680 :
    AlignedValid 12 4 missing3672_3680 records3672_3680 :=
  aligned3672_3676.append aligned3676_3680

def missing3664_3680 : List (BitVec (edgeCount 12)) :=
  missing3664_3672 ++ missing3672_3680
abbrev records3664_3680 : List Blob :=
  records3664_3672 ++ records3672_3680
theorem aligned3664_3680 :
    AlignedValid 12 4 missing3664_3680 records3664_3680 :=
  aligned3664_3672.append aligned3672_3680

def missing3648_3680 : List (BitVec (edgeCount 12)) :=
  missing3648_3664 ++ missing3664_3680
abbrev records3648_3680 : List Blob :=
  records3648_3664 ++ records3664_3680
theorem aligned3648_3680 :
    AlignedValid 12 4 missing3648_3680 records3648_3680 :=
  aligned3648_3664.append aligned3664_3680

def missing3680_3681 : List (BitVec (edgeCount 12)) :=
  [missing3680]
abbrev records3680_3681 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3680]
theorem aligned3680_3681 :
    AlignedValid 12 4 missing3680_3681 records3680_3681 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3680
    maskCheck3680 AlignedValid.nil

def missing3681_3682 : List (BitVec (edgeCount 12)) :=
  [missing3681]
abbrev records3681_3682 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3681]
theorem aligned3681_3682 :
    AlignedValid 12 4 missing3681_3682 records3681_3682 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3681
    maskCheck3681 AlignedValid.nil

def missing3680_3682 : List (BitVec (edgeCount 12)) :=
  missing3680_3681 ++ missing3681_3682
abbrev records3680_3682 : List Blob :=
  records3680_3681 ++ records3681_3682
theorem aligned3680_3682 :
    AlignedValid 12 4 missing3680_3682 records3680_3682 :=
  aligned3680_3681.append aligned3681_3682

def missing3682_3683 : List (BitVec (edgeCount 12)) :=
  [missing3682]
abbrev records3682_3683 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3682]
theorem aligned3682_3683 :
    AlignedValid 12 4 missing3682_3683 records3682_3683 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3682
    maskCheck3682 AlignedValid.nil

def missing3683_3684 : List (BitVec (edgeCount 12)) :=
  [missing3683]
abbrev records3683_3684 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3683]
theorem aligned3683_3684 :
    AlignedValid 12 4 missing3683_3684 records3683_3684 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3683
    maskCheck3683 AlignedValid.nil

def missing3682_3684 : List (BitVec (edgeCount 12)) :=
  missing3682_3683 ++ missing3683_3684
abbrev records3682_3684 : List Blob :=
  records3682_3683 ++ records3683_3684
theorem aligned3682_3684 :
    AlignedValid 12 4 missing3682_3684 records3682_3684 :=
  aligned3682_3683.append aligned3683_3684

def missing3680_3684 : List (BitVec (edgeCount 12)) :=
  missing3680_3682 ++ missing3682_3684
abbrev records3680_3684 : List Blob :=
  records3680_3682 ++ records3682_3684
theorem aligned3680_3684 :
    AlignedValid 12 4 missing3680_3684 records3680_3684 :=
  aligned3680_3682.append aligned3682_3684

def missing3684_3685 : List (BitVec (edgeCount 12)) :=
  [missing3684]
abbrev records3684_3685 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3684]
theorem aligned3684_3685 :
    AlignedValid 12 4 missing3684_3685 records3684_3685 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3684
    maskCheck3684 AlignedValid.nil

def missing3685_3686 : List (BitVec (edgeCount 12)) :=
  [missing3685]
abbrev records3685_3686 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3685]
theorem aligned3685_3686 :
    AlignedValid 12 4 missing3685_3686 records3685_3686 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3685
    maskCheck3685 AlignedValid.nil

def missing3684_3686 : List (BitVec (edgeCount 12)) :=
  missing3684_3685 ++ missing3685_3686
abbrev records3684_3686 : List Blob :=
  records3684_3685 ++ records3685_3686
theorem aligned3684_3686 :
    AlignedValid 12 4 missing3684_3686 records3684_3686 :=
  aligned3684_3685.append aligned3685_3686

def missing3686_3687 : List (BitVec (edgeCount 12)) :=
  [missing3686]
abbrev records3686_3687 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3686]
theorem aligned3686_3687 :
    AlignedValid 12 4 missing3686_3687 records3686_3687 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3686
    maskCheck3686 AlignedValid.nil

def missing3687_3688 : List (BitVec (edgeCount 12)) :=
  [missing3687]
abbrev records3687_3688 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3687]
theorem aligned3687_3688 :
    AlignedValid 12 4 missing3687_3688 records3687_3688 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3687
    maskCheck3687 AlignedValid.nil

def missing3686_3688 : List (BitVec (edgeCount 12)) :=
  missing3686_3687 ++ missing3687_3688
abbrev records3686_3688 : List Blob :=
  records3686_3687 ++ records3687_3688
theorem aligned3686_3688 :
    AlignedValid 12 4 missing3686_3688 records3686_3688 :=
  aligned3686_3687.append aligned3687_3688

def missing3684_3688 : List (BitVec (edgeCount 12)) :=
  missing3684_3686 ++ missing3686_3688
abbrev records3684_3688 : List Blob :=
  records3684_3686 ++ records3686_3688
theorem aligned3684_3688 :
    AlignedValid 12 4 missing3684_3688 records3684_3688 :=
  aligned3684_3686.append aligned3686_3688

def missing3680_3688 : List (BitVec (edgeCount 12)) :=
  missing3680_3684 ++ missing3684_3688
abbrev records3680_3688 : List Blob :=
  records3680_3684 ++ records3684_3688
theorem aligned3680_3688 :
    AlignedValid 12 4 missing3680_3688 records3680_3688 :=
  aligned3680_3684.append aligned3684_3688

def missing3688_3689 : List (BitVec (edgeCount 12)) :=
  [missing3688]
abbrev records3688_3689 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3688]
theorem aligned3688_3689 :
    AlignedValid 12 4 missing3688_3689 records3688_3689 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3688
    maskCheck3688 AlignedValid.nil

def missing3689_3690 : List (BitVec (edgeCount 12)) :=
  [missing3689]
abbrev records3689_3690 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3689]
theorem aligned3689_3690 :
    AlignedValid 12 4 missing3689_3690 records3689_3690 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3689
    maskCheck3689 AlignedValid.nil

def missing3688_3690 : List (BitVec (edgeCount 12)) :=
  missing3688_3689 ++ missing3689_3690
abbrev records3688_3690 : List Blob :=
  records3688_3689 ++ records3689_3690
theorem aligned3688_3690 :
    AlignedValid 12 4 missing3688_3690 records3688_3690 :=
  aligned3688_3689.append aligned3689_3690

def missing3690_3691 : List (BitVec (edgeCount 12)) :=
  [missing3690]
abbrev records3690_3691 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3690]
theorem aligned3690_3691 :
    AlignedValid 12 4 missing3690_3691 records3690_3691 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3690
    maskCheck3690 AlignedValid.nil

def missing3691_3692 : List (BitVec (edgeCount 12)) :=
  [missing3691]
abbrev records3691_3692 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3691]
theorem aligned3691_3692 :
    AlignedValid 12 4 missing3691_3692 records3691_3692 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3691
    maskCheck3691 AlignedValid.nil

def missing3690_3692 : List (BitVec (edgeCount 12)) :=
  missing3690_3691 ++ missing3691_3692
abbrev records3690_3692 : List Blob :=
  records3690_3691 ++ records3691_3692
theorem aligned3690_3692 :
    AlignedValid 12 4 missing3690_3692 records3690_3692 :=
  aligned3690_3691.append aligned3691_3692

def missing3688_3692 : List (BitVec (edgeCount 12)) :=
  missing3688_3690 ++ missing3690_3692
abbrev records3688_3692 : List Blob :=
  records3688_3690 ++ records3690_3692
theorem aligned3688_3692 :
    AlignedValid 12 4 missing3688_3692 records3688_3692 :=
  aligned3688_3690.append aligned3690_3692

def missing3692_3693 : List (BitVec (edgeCount 12)) :=
  [missing3692]
abbrev records3692_3693 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3692]
theorem aligned3692_3693 :
    AlignedValid 12 4 missing3692_3693 records3692_3693 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3692
    maskCheck3692 AlignedValid.nil

def missing3693_3694 : List (BitVec (edgeCount 12)) :=
  [missing3693]
abbrev records3693_3694 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3693]
theorem aligned3693_3694 :
    AlignedValid 12 4 missing3693_3694 records3693_3694 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3693
    maskCheck3693 AlignedValid.nil

def missing3692_3694 : List (BitVec (edgeCount 12)) :=
  missing3692_3693 ++ missing3693_3694
abbrev records3692_3694 : List Blob :=
  records3692_3693 ++ records3693_3694
theorem aligned3692_3694 :
    AlignedValid 12 4 missing3692_3694 records3692_3694 :=
  aligned3692_3693.append aligned3693_3694

def missing3694_3695 : List (BitVec (edgeCount 12)) :=
  [missing3694]
abbrev records3694_3695 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3694]
theorem aligned3694_3695 :
    AlignedValid 12 4 missing3694_3695 records3694_3695 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3694
    maskCheck3694 AlignedValid.nil

def missing3695_3696 : List (BitVec (edgeCount 12)) :=
  [missing3695]
abbrev records3695_3696 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3695]
theorem aligned3695_3696 :
    AlignedValid 12 4 missing3695_3696 records3695_3696 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3695
    maskCheck3695 AlignedValid.nil

def missing3694_3696 : List (BitVec (edgeCount 12)) :=
  missing3694_3695 ++ missing3695_3696
abbrev records3694_3696 : List Blob :=
  records3694_3695 ++ records3695_3696
theorem aligned3694_3696 :
    AlignedValid 12 4 missing3694_3696 records3694_3696 :=
  aligned3694_3695.append aligned3695_3696

def missing3692_3696 : List (BitVec (edgeCount 12)) :=
  missing3692_3694 ++ missing3694_3696
abbrev records3692_3696 : List Blob :=
  records3692_3694 ++ records3694_3696
theorem aligned3692_3696 :
    AlignedValid 12 4 missing3692_3696 records3692_3696 :=
  aligned3692_3694.append aligned3694_3696

def missing3688_3696 : List (BitVec (edgeCount 12)) :=
  missing3688_3692 ++ missing3692_3696
abbrev records3688_3696 : List Blob :=
  records3688_3692 ++ records3692_3696
theorem aligned3688_3696 :
    AlignedValid 12 4 missing3688_3696 records3688_3696 :=
  aligned3688_3692.append aligned3692_3696

def missing3680_3696 : List (BitVec (edgeCount 12)) :=
  missing3680_3688 ++ missing3688_3696
abbrev records3680_3696 : List Blob :=
  records3680_3688 ++ records3688_3696
theorem aligned3680_3696 :
    AlignedValid 12 4 missing3680_3696 records3680_3696 :=
  aligned3680_3688.append aligned3688_3696

def missing3696_3697 : List (BitVec (edgeCount 12)) :=
  [missing3696]
abbrev records3696_3697 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3696]
theorem aligned3696_3697 :
    AlignedValid 12 4 missing3696_3697 records3696_3697 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3696
    maskCheck3696 AlignedValid.nil

def missing3697_3698 : List (BitVec (edgeCount 12)) :=
  [missing3697]
abbrev records3697_3698 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3697]
theorem aligned3697_3698 :
    AlignedValid 12 4 missing3697_3698 records3697_3698 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3697
    maskCheck3697 AlignedValid.nil

def missing3696_3698 : List (BitVec (edgeCount 12)) :=
  missing3696_3697 ++ missing3697_3698
abbrev records3696_3698 : List Blob :=
  records3696_3697 ++ records3697_3698
theorem aligned3696_3698 :
    AlignedValid 12 4 missing3696_3698 records3696_3698 :=
  aligned3696_3697.append aligned3697_3698

def missing3698_3699 : List (BitVec (edgeCount 12)) :=
  [missing3698]
abbrev records3698_3699 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3698]
theorem aligned3698_3699 :
    AlignedValid 12 4 missing3698_3699 records3698_3699 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3698
    maskCheck3698 AlignedValid.nil

def missing3699_3700 : List (BitVec (edgeCount 12)) :=
  [missing3699]
abbrev records3699_3700 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3699]
theorem aligned3699_3700 :
    AlignedValid 12 4 missing3699_3700 records3699_3700 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3699
    maskCheck3699 AlignedValid.nil

def missing3698_3700 : List (BitVec (edgeCount 12)) :=
  missing3698_3699 ++ missing3699_3700
abbrev records3698_3700 : List Blob :=
  records3698_3699 ++ records3699_3700
theorem aligned3698_3700 :
    AlignedValid 12 4 missing3698_3700 records3698_3700 :=
  aligned3698_3699.append aligned3699_3700

def missing3696_3700 : List (BitVec (edgeCount 12)) :=
  missing3696_3698 ++ missing3698_3700
abbrev records3696_3700 : List Blob :=
  records3696_3698 ++ records3698_3700
theorem aligned3696_3700 :
    AlignedValid 12 4 missing3696_3700 records3696_3700 :=
  aligned3696_3698.append aligned3698_3700

def missing3700_3701 : List (BitVec (edgeCount 12)) :=
  [missing3700]
abbrev records3700_3701 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3700]
theorem aligned3700_3701 :
    AlignedValid 12 4 missing3700_3701 records3700_3701 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3700
    maskCheck3700 AlignedValid.nil

def missing3701_3702 : List (BitVec (edgeCount 12)) :=
  [missing3701]
abbrev records3701_3702 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3701]
theorem aligned3701_3702 :
    AlignedValid 12 4 missing3701_3702 records3701_3702 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3701
    maskCheck3701 AlignedValid.nil

def missing3700_3702 : List (BitVec (edgeCount 12)) :=
  missing3700_3701 ++ missing3701_3702
abbrev records3700_3702 : List Blob :=
  records3700_3701 ++ records3701_3702
theorem aligned3700_3702 :
    AlignedValid 12 4 missing3700_3702 records3700_3702 :=
  aligned3700_3701.append aligned3701_3702

def missing3702_3703 : List (BitVec (edgeCount 12)) :=
  [missing3702]
abbrev records3702_3703 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3702]
theorem aligned3702_3703 :
    AlignedValid 12 4 missing3702_3703 records3702_3703 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3702
    maskCheck3702 AlignedValid.nil

def missing3703_3704 : List (BitVec (edgeCount 12)) :=
  [missing3703]
abbrev records3703_3704 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3703]
theorem aligned3703_3704 :
    AlignedValid 12 4 missing3703_3704 records3703_3704 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3703
    maskCheck3703 AlignedValid.nil

def missing3702_3704 : List (BitVec (edgeCount 12)) :=
  missing3702_3703 ++ missing3703_3704
abbrev records3702_3704 : List Blob :=
  records3702_3703 ++ records3703_3704
theorem aligned3702_3704 :
    AlignedValid 12 4 missing3702_3704 records3702_3704 :=
  aligned3702_3703.append aligned3703_3704

def missing3700_3704 : List (BitVec (edgeCount 12)) :=
  missing3700_3702 ++ missing3702_3704
abbrev records3700_3704 : List Blob :=
  records3700_3702 ++ records3702_3704
theorem aligned3700_3704 :
    AlignedValid 12 4 missing3700_3704 records3700_3704 :=
  aligned3700_3702.append aligned3702_3704

def missing3696_3704 : List (BitVec (edgeCount 12)) :=
  missing3696_3700 ++ missing3700_3704
abbrev records3696_3704 : List Blob :=
  records3696_3700 ++ records3700_3704
theorem aligned3696_3704 :
    AlignedValid 12 4 missing3696_3704 records3696_3704 :=
  aligned3696_3700.append aligned3700_3704

def missing3704_3705 : List (BitVec (edgeCount 12)) :=
  [missing3704]
abbrev records3704_3705 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3704]
theorem aligned3704_3705 :
    AlignedValid 12 4 missing3704_3705 records3704_3705 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3704
    maskCheck3704 AlignedValid.nil

def missing3705_3706 : List (BitVec (edgeCount 12)) :=
  [missing3705]
abbrev records3705_3706 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3705]
theorem aligned3705_3706 :
    AlignedValid 12 4 missing3705_3706 records3705_3706 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3705
    maskCheck3705 AlignedValid.nil

def missing3704_3706 : List (BitVec (edgeCount 12)) :=
  missing3704_3705 ++ missing3705_3706
abbrev records3704_3706 : List Blob :=
  records3704_3705 ++ records3705_3706
theorem aligned3704_3706 :
    AlignedValid 12 4 missing3704_3706 records3704_3706 :=
  aligned3704_3705.append aligned3705_3706

def missing3706_3707 : List (BitVec (edgeCount 12)) :=
  [missing3706]
abbrev records3706_3707 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3706]
theorem aligned3706_3707 :
    AlignedValid 12 4 missing3706_3707 records3706_3707 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3706
    maskCheck3706 AlignedValid.nil

def missing3707_3708 : List (BitVec (edgeCount 12)) :=
  [missing3707]
abbrev records3707_3708 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3707]
theorem aligned3707_3708 :
    AlignedValid 12 4 missing3707_3708 records3707_3708 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3707
    maskCheck3707 AlignedValid.nil

def missing3706_3708 : List (BitVec (edgeCount 12)) :=
  missing3706_3707 ++ missing3707_3708
abbrev records3706_3708 : List Blob :=
  records3706_3707 ++ records3707_3708
theorem aligned3706_3708 :
    AlignedValid 12 4 missing3706_3708 records3706_3708 :=
  aligned3706_3707.append aligned3707_3708

def missing3704_3708 : List (BitVec (edgeCount 12)) :=
  missing3704_3706 ++ missing3706_3708
abbrev records3704_3708 : List Blob :=
  records3704_3706 ++ records3706_3708
theorem aligned3704_3708 :
    AlignedValid 12 4 missing3704_3708 records3704_3708 :=
  aligned3704_3706.append aligned3706_3708

def missing3708_3709 : List (BitVec (edgeCount 12)) :=
  [missing3708]
abbrev records3708_3709 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3708]
theorem aligned3708_3709 :
    AlignedValid 12 4 missing3708_3709 records3708_3709 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3708
    maskCheck3708 AlignedValid.nil

def missing3709_3710 : List (BitVec (edgeCount 12)) :=
  [missing3709]
abbrev records3709_3710 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3709]
theorem aligned3709_3710 :
    AlignedValid 12 4 missing3709_3710 records3709_3710 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3709
    maskCheck3709 AlignedValid.nil

def missing3708_3710 : List (BitVec (edgeCount 12)) :=
  missing3708_3709 ++ missing3709_3710
abbrev records3708_3710 : List Blob :=
  records3708_3709 ++ records3709_3710
theorem aligned3708_3710 :
    AlignedValid 12 4 missing3708_3710 records3708_3710 :=
  aligned3708_3709.append aligned3709_3710

def missing3710_3711 : List (BitVec (edgeCount 12)) :=
  [missing3710]
abbrev records3710_3711 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3710]
theorem aligned3710_3711 :
    AlignedValid 12 4 missing3710_3711 records3710_3711 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3710
    maskCheck3710 AlignedValid.nil

def missing3711_3712 : List (BitVec (edgeCount 12)) :=
  [missing3711]
abbrev records3711_3712 : List Blob :=
  [StrongPackedBucketN12A4Shard028.record3711]
theorem aligned3711_3712 :
    AlignedValid 12 4 missing3711_3712 records3711_3712 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard028.check3711
    maskCheck3711 AlignedValid.nil

def missing3710_3712 : List (BitVec (edgeCount 12)) :=
  missing3710_3711 ++ missing3711_3712
abbrev records3710_3712 : List Blob :=
  records3710_3711 ++ records3711_3712
theorem aligned3710_3712 :
    AlignedValid 12 4 missing3710_3712 records3710_3712 :=
  aligned3710_3711.append aligned3711_3712

def missing3708_3712 : List (BitVec (edgeCount 12)) :=
  missing3708_3710 ++ missing3710_3712
abbrev records3708_3712 : List Blob :=
  records3708_3710 ++ records3710_3712
theorem aligned3708_3712 :
    AlignedValid 12 4 missing3708_3712 records3708_3712 :=
  aligned3708_3710.append aligned3710_3712

def missing3704_3712 : List (BitVec (edgeCount 12)) :=
  missing3704_3708 ++ missing3708_3712
abbrev records3704_3712 : List Blob :=
  records3704_3708 ++ records3708_3712
theorem aligned3704_3712 :
    AlignedValid 12 4 missing3704_3712 records3704_3712 :=
  aligned3704_3708.append aligned3708_3712

def missing3696_3712 : List (BitVec (edgeCount 12)) :=
  missing3696_3704 ++ missing3704_3712
abbrev records3696_3712 : List Blob :=
  records3696_3704 ++ records3704_3712
theorem aligned3696_3712 :
    AlignedValid 12 4 missing3696_3712 records3696_3712 :=
  aligned3696_3704.append aligned3704_3712

def missing3680_3712 : List (BitVec (edgeCount 12)) :=
  missing3680_3696 ++ missing3696_3712
abbrev records3680_3712 : List Blob :=
  records3680_3696 ++ records3696_3712
theorem aligned3680_3712 :
    AlignedValid 12 4 missing3680_3712 records3680_3712 :=
  aligned3680_3696.append aligned3696_3712

def missing3648_3712 : List (BitVec (edgeCount 12)) :=
  missing3648_3680 ++ missing3680_3712
abbrev records3648_3712 : List Blob :=
  records3648_3680 ++ records3680_3712
theorem aligned3648_3712 :
    AlignedValid 12 4 missing3648_3712 records3648_3712 :=
  aligned3648_3680.append aligned3680_3712

def missing3584_3712 : List (BitVec (edgeCount 12)) :=
  missing3584_3648 ++ missing3648_3712
abbrev records3584_3712 : List Blob :=
  records3584_3648 ++ records3648_3712
theorem aligned3584_3712 :
    AlignedValid 12 4 missing3584_3712 records3584_3712 :=
  aligned3584_3648.append aligned3648_3712

abbrev missing : List (BitVec (edgeCount 12)) := missing3584_3712
abbrev records : List Blob := records3584_3712
theorem aligned : AlignedValid 12 4 missing records := aligned3584_3712

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard028
