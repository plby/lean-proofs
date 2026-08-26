/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A4Shard192

/-! Decode-only alignment checks for n=12, a=4, records 24576--24703. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard192

open PackedBucketCertificate

def missing24576 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11927221351944814592
theorem maskCheck24576 :
    checkMaskFor missing24576 StrongPackedBucketN12A4Shard192.record24576 = true := by
  decide

def missing24577 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11999278945982742528
theorem maskCheck24577 :
    checkMaskFor missing24577 StrongPackedBucketN12A4Shard192.record24577 = true := by
  decide

def missing24578 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12035307743001706496
theorem maskCheck24578 :
    checkMaskFor missing24578 StrongPackedBucketN12A4Shard192.record24578 = true := by
  decide

def missing24579 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12215451728096526336
theorem maskCheck24579 :
    checkMaskFor missing24579 StrongPackedBucketN12A4Shard192.record24579 = true := by
  decide

def missing24580 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12287509322134454272
theorem maskCheck24580 :
    checkMaskFor missing24580 StrongPackedBucketN12A4Shard192.record24580 = true := by
  decide

def missing24581 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12323538119153418240
theorem maskCheck24581 :
    checkMaskFor missing24581 StrongPackedBucketN12A4Shard192.record24581 = true := by
  decide

def missing24582 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12431624510210310144
theorem maskCheck24582 :
    checkMaskFor missing24582 StrongPackedBucketN12A4Shard192.record24582 = true := by
  decide

def missing24583 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12467653307229274112
theorem maskCheck24583 :
    checkMaskFor missing24583 StrongPackedBucketN12A4Shard192.record24583 = true := by
  decide

def missing24584 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12539710901267202048
theorem maskCheck24584 :
    checkMaskFor missing24584 StrongPackedBucketN12A4Shard192.record24584 = true := by
  decide

def missing24585 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13296315638665445376
theorem maskCheck24585 :
    checkMaskFor missing24585 StrongPackedBucketN12A4Shard192.record24585 = true := by
  decide

def missing24586 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13332344435684409344
theorem maskCheck24586 :
    checkMaskFor missing24586 StrongPackedBucketN12A4Shard192.record24586 = true := by
  decide

def missing24587 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13404402029722337280
theorem maskCheck24587 :
    checkMaskFor missing24587 StrongPackedBucketN12A4Shard192.record24587 = true := by
  decide

def missing24588 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13548517217798193152
theorem maskCheck24588 :
    checkMaskFor missing24588 StrongPackedBucketN12A4Shard192.record24588 = true := by
  decide

def missing24589 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14088949173082652672
theorem maskCheck24589 :
    checkMaskFor missing24589 StrongPackedBucketN12A4Shard192.record24589 = true := by
  decide

def missing24590 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14233064361158508544
theorem maskCheck24590 :
    checkMaskFor missing24590 StrongPackedBucketN12A4Shard192.record24590 = true := by
  decide

def missing24591 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14305121955196436480
theorem maskCheck24591 :
    checkMaskFor missing24591 StrongPackedBucketN12A4Shard192.record24591 = true := by
  decide

def missing24592 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14521294737310220288
theorem maskCheck24592 :
    checkMaskFor missing24592 StrongPackedBucketN12A4Shard192.record24592 = true := by
  decide

def missing24593 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14593352331348148224
theorem maskCheck24593 :
    checkMaskFor missing24593 StrongPackedBucketN12A4Shard192.record24593 = true := by
  decide

def missing24594 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14737467519424004096
theorem maskCheck24594 :
    checkMaskFor missing24594 StrongPackedBucketN12A4Shard192.record24594 = true := by
  decide

def missing24595 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 15602158647879139328
theorem maskCheck24595 :
    checkMaskFor missing24595 StrongPackedBucketN12A4Shard192.record24595 = true := by
  decide

def missing24596 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 16250676994220490752
theorem maskCheck24596 :
    checkMaskFor missing24596 StrongPackedBucketN12A4Shard192.record24596 = true := by
  decide

def missing24597 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 16322734588258418688
theorem maskCheck24597 :
    checkMaskFor missing24597 StrongPackedBucketN12A4Shard192.record24597 = true := by
  decide

def missing24598 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 16466849776334274560
theorem maskCheck24598 :
    checkMaskFor missing24598 StrongPackedBucketN12A4Shard192.record24598 = true := by
  decide

def missing24599 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 16755080152485986304
theorem maskCheck24599 :
    checkMaskFor missing24599 StrongPackedBucketN12A4Shard192.record24599 = true := by
  decide

def missing24600 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27924007228364816384
theorem maskCheck24600 :
    checkMaskFor missing24600 StrongPackedBucketN12A4Shard192.record24600 = true := by
  decide

def missing24601 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28140180010478600192
theorem maskCheck24601 :
    checkMaskFor missing24601 StrongPackedBucketN12A4Shard192.record24601 = true := by
  decide

def missing24602 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28176208807497564160
theorem maskCheck24602 :
    checkMaskFor missing24602 StrongPackedBucketN12A4Shard192.record24602 = true := by
  decide

def missing24603 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28356352792592384000
theorem maskCheck24603 :
    checkMaskFor missing24603 StrongPackedBucketN12A4Shard192.record24603 = true := by
  decide

def missing24604 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28428410386630311936
theorem maskCheck24604 :
    checkMaskFor missing24604 StrongPackedBucketN12A4Shard192.record24604 = true := by
  decide

def missing24605 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28464439183649275904
theorem maskCheck24605 :
    checkMaskFor missing24605 StrongPackedBucketN12A4Shard192.record24605 = true := by
  decide

def missing24606 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28680611965763059712
theorem maskCheck24606 :
    checkMaskFor missing24606 StrongPackedBucketN12A4Shard192.record24606 = true := by
  decide

def missing24607 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29437216703161303040
theorem maskCheck24607 :
    checkMaskFor missing24607 StrongPackedBucketN12A4Shard192.record24607 = true := by
  decide

def missing24608 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29473245500180267008
theorem maskCheck24608 :
    checkMaskFor missing24608 StrongPackedBucketN12A4Shard192.record24608 = true := by
  decide

def missing24609 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29545303094218194944
theorem maskCheck24609 :
    checkMaskFor missing24609 StrongPackedBucketN12A4Shard192.record24609 = true := by
  decide

def missing24610 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 30085735049502654464
theorem maskCheck24610 :
    checkMaskFor missing24610 StrongPackedBucketN12A4Shard192.record24610 = true := by
  decide

def missing24611 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 30157792643540582400
theorem maskCheck24611 :
    checkMaskFor missing24611 StrongPackedBucketN12A4Shard192.record24611 = true := by
  decide

def missing24612 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 30193821440559546368
theorem maskCheck24612 :
    checkMaskFor missing24612 StrongPackedBucketN12A4Shard192.record24612 = true := by
  decide

def missing24613 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 30409994222673330176
theorem maskCheck24613 :
    checkMaskFor missing24613 StrongPackedBucketN12A4Shard192.record24613 = true := by
  decide

def missing24614 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 30590138207768150016
theorem maskCheck24614 :
    checkMaskFor missing24614 StrongPackedBucketN12A4Shard192.record24614 = true := by
  decide

def missing24615 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 30626167004787113984
theorem maskCheck24615 :
    checkMaskFor missing24615 StrongPackedBucketN12A4Shard192.record24615 = true := by
  decide

def missing24616 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 30698224598825041920
theorem maskCheck24616 :
    checkMaskFor missing24616 StrongPackedBucketN12A4Shard192.record24616 = true := by
  decide

def missing24617 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 31707030915356033024
theorem maskCheck24617 :
    checkMaskFor missing24617 StrongPackedBucketN12A4Shard192.record24617 = true := by
  decide

def missing24618 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32391578058716348416
theorem maskCheck24618 :
    checkMaskFor missing24618 StrongPackedBucketN12A4Shard192.record24618 = true := by
  decide

def missing24619 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32463635652754276352
theorem maskCheck24619 :
    checkMaskFor missing24619 StrongPackedBucketN12A4Shard192.record24619 = true := by
  decide

def missing24620 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32895981216981843968
theorem maskCheck24620 :
    checkMaskFor missing24620 StrongPackedBucketN12A4Shard192.record24620 = true := by
  decide

def missing24621 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 34625363473892114432
theorem maskCheck24621 :
    checkMaskFor missing24621 StrongPackedBucketN12A4Shard192.record24621 = true := by
  decide

def missing24622 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37435609641371303936
theorem maskCheck24622 :
    checkMaskFor missing24622 StrongPackedBucketN12A4Shard192.record24622 = true := by
  decide

def missing24623 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37723840017523015680
theorem maskCheck24623 :
    checkMaskFor missing24623 StrongPackedBucketN12A4Shard192.record24623 = true := by
  decide

def missing24624 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37940012799636799488
theorem maskCheck24624 :
    checkMaskFor missing24624 StrongPackedBucketN12A4Shard192.record24624 = true := by
  decide

def missing24625 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37976041596655763456
theorem maskCheck24625 :
    checkMaskFor missing24625 StrongPackedBucketN12A4Shard192.record24625 = true := by
  decide

def missing24626 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38732646334054006784
theorem maskCheck24626 :
    checkMaskFor missing24626 StrongPackedBucketN12A4Shard192.record24626 = true := by
  decide

def missing24627 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38804703928091934720
theorem maskCheck24627 :
    checkMaskFor missing24627 StrongPackedBucketN12A4Shard192.record24627 = true := by
  decide

def missing24628 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38840732725110898688
theorem maskCheck24628 :
    checkMaskFor missing24628 StrongPackedBucketN12A4Shard192.record24628 = true := by
  decide

def missing24629 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39056905507224682496
theorem maskCheck24629 :
    checkMaskFor missing24629 StrongPackedBucketN12A4Shard192.record24629 = true := by
  decide

def missing24630 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39453222274433286144
theorem maskCheck24630 :
    checkMaskFor missing24630 StrongPackedBucketN12A4Shard192.record24630 = true := by
  decide

def missing24631 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39669395056547069952
theorem maskCheck24631 :
    checkMaskFor missing24631 StrongPackedBucketN12A4Shard192.record24631 = true := by
  decide

def missing24632 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39705423853566033920
theorem maskCheck24632 :
    checkMaskFor missing24632 StrongPackedBucketN12A4Shard192.record24632 = true := by
  decide

def missing24633 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39885567838660853760
theorem maskCheck24633 :
    checkMaskFor missing24633 StrongPackedBucketN12A4Shard192.record24633 = true := by
  decide

def missing24634 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39957625432698781696
theorem maskCheck24634 :
    checkMaskFor missing24634 StrongPackedBucketN12A4Shard192.record24634 = true := by
  decide

def missing24635 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39993654229717745664
theorem maskCheck24635 :
    checkMaskFor missing24635 StrongPackedBucketN12A4Shard192.record24635 = true := by
  decide

def missing24636 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 40209827011831529472
theorem maskCheck24636 :
    checkMaskFor missing24636 StrongPackedBucketN12A4Shard192.record24636 = true := by
  decide

def missing24637 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 40966431749229772800
theorem maskCheck24637 :
    checkMaskFor missing24637 StrongPackedBucketN12A4Shard192.record24637 = true := by
  decide

def missing24638 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41002460546248736768
theorem maskCheck24638 :
    checkMaskFor missing24638 StrongPackedBucketN12A4Shard192.record24638 = true := by
  decide

def missing24639 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41074518140286664704
theorem maskCheck24639 :
    checkMaskFor missing24639 StrongPackedBucketN12A4Shard192.record24639 = true := by
  decide

def missing24640 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41759065283646980096
theorem maskCheck24640 :
    checkMaskFor missing24640 StrongPackedBucketN12A4Shard192.record24640 = true := by
  decide

def missing24641 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41975238065760763904
theorem maskCheck24641 :
    checkMaskFor missing24641 StrongPackedBucketN12A4Shard192.record24641 = true := by
  decide

def missing24642 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42191410847874547712
theorem maskCheck24642 :
    checkMaskFor missing24642 StrongPackedBucketN12A4Shard192.record24642 = true := by
  decide

def missing24643 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42263468441912475648
theorem maskCheck24643 :
    checkMaskFor missing24643 StrongPackedBucketN12A4Shard192.record24643 = true := by
  decide

def missing24644 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 43272274758443466752
theorem maskCheck24644 :
    checkMaskFor missing24644 StrongPackedBucketN12A4Shard192.record24644 = true := by
  decide

def missing24645 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 43920793104784818176
theorem maskCheck24645 :
    checkMaskFor missing24645 StrongPackedBucketN12A4Shard192.record24645 = true := by
  decide

def missing24646 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 43992850698822746112
theorem maskCheck24646 :
    checkMaskFor missing24646 StrongPackedBucketN12A4Shard192.record24646 = true := by
  decide

def missing24647 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 44425196263050313728
theorem maskCheck24647 :
    checkMaskFor missing24647 StrongPackedBucketN12A4Shard192.record24647 = true := by
  decide

def missing24648 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46370751302074368000
theorem maskCheck24648 :
    checkMaskFor missing24648 StrongPackedBucketN12A4Shard192.record24648 = true := by
  decide

def missing24649 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46514866490150223872
theorem maskCheck24649 :
    checkMaskFor missing24649 StrongPackedBucketN12A4Shard192.record24649 = true := by
  decide

def missing24650 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46586924084188151808
theorem maskCheck24650 :
    checkMaskFor missing24650 StrongPackedBucketN12A4Shard192.record24650 = true := by
  decide

def missing24651 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46622952881207115776
theorem maskCheck24651 :
    checkMaskFor missing24651 StrongPackedBucketN12A4Shard192.record24651 = true := by
  decide

def missing24652 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46803096866301935616
theorem maskCheck24652 :
    checkMaskFor missing24652 StrongPackedBucketN12A4Shard192.record24652 = true := by
  decide

def missing24653 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46875154460339863552
theorem maskCheck24653 :
    checkMaskFor missing24653 StrongPackedBucketN12A4Shard192.record24653 = true := by
  decide

def missing24654 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46911183257358827520
theorem maskCheck24654 :
    checkMaskFor missing24654 StrongPackedBucketN12A4Shard192.record24654 = true := by
  decide

def missing24655 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47019269648415719424
theorem maskCheck24655 :
    checkMaskFor missing24655 StrongPackedBucketN12A4Shard192.record24655 = true := by
  decide

def missing24656 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47055298445434683392
theorem maskCheck24656 :
    checkMaskFor missing24656 StrongPackedBucketN12A4Shard192.record24656 = true := by
  decide

def missing24657 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47127356039472611328
theorem maskCheck24657 :
    checkMaskFor missing24657 StrongPackedBucketN12A4Shard192.record24657 = true := by
  decide

def missing24658 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47883960776870854656
theorem maskCheck24658 :
    checkMaskFor missing24658 StrongPackedBucketN12A4Shard192.record24658 = true := by
  decide

def missing24659 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47919989573889818624
theorem maskCheck24659 :
    checkMaskFor missing24659 StrongPackedBucketN12A4Shard192.record24659 = true := by
  decide

def missing24660 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47992047167927746560
theorem maskCheck24660 :
    checkMaskFor missing24660 StrongPackedBucketN12A4Shard192.record24660 = true := by
  decide

def missing24661 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 48136162356003602432
theorem maskCheck24661 :
    checkMaskFor missing24661 StrongPackedBucketN12A4Shard192.record24661 = true := by
  decide

def missing24662 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 48532479123212206080
theorem maskCheck24662 :
    checkMaskFor missing24662 StrongPackedBucketN12A4Shard192.record24662 = true := by
  decide

def missing24663 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 48604536717250134016
theorem maskCheck24663 :
    checkMaskFor missing24663 StrongPackedBucketN12A4Shard192.record24663 = true := by
  decide

def missing24664 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 48640565514269097984
theorem maskCheck24664 :
    checkMaskFor missing24664 StrongPackedBucketN12A4Shard192.record24664 = true := by
  decide

def missing24665 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 48748651905325989888
theorem maskCheck24665 :
    checkMaskFor missing24665 StrongPackedBucketN12A4Shard192.record24665 = true := by
  decide

def missing24666 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 48784680702344953856
theorem maskCheck24666 :
    checkMaskFor missing24666 StrongPackedBucketN12A4Shard192.record24666 = true := by
  decide

def missing24667 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 48856738296382881792
theorem maskCheck24667 :
    checkMaskFor missing24667 StrongPackedBucketN12A4Shard192.record24667 = true := by
  decide

def missing24668 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 49036882281477701632
theorem maskCheck24668 :
    checkMaskFor missing24668 StrongPackedBucketN12A4Shard192.record24668 = true := by
  decide

def missing24669 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 49072911078496665600
theorem maskCheck24669 :
    checkMaskFor missing24669 StrongPackedBucketN12A4Shard192.record24669 = true := by
  decide

def missing24670 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 49144968672534593536
theorem maskCheck24670 :
    checkMaskFor missing24670 StrongPackedBucketN12A4Shard192.record24670 = true := by
  decide

def missing24671 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 49289083860610449408
theorem maskCheck24671 :
    checkMaskFor missing24671 StrongPackedBucketN12A4Shard192.record24671 = true := by
  decide

def missing24672 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50153774989065584640
theorem maskCheck24672 :
    checkMaskFor missing24672 StrongPackedBucketN12A4Shard192.record24672 = true := by
  decide

def missing24673 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50838322132425900032
theorem maskCheck24673 :
    checkMaskFor missing24673 StrongPackedBucketN12A4Shard192.record24673 = true := by
  decide

def missing24674 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50910379726463827968
theorem maskCheck24674 :
    checkMaskFor missing24674 StrongPackedBucketN12A4Shard192.record24674 = true := by
  decide

def missing24675 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 51054494914539683840
theorem maskCheck24675 :
    checkMaskFor missing24675 StrongPackedBucketN12A4Shard192.record24675 = true := by
  decide

def missing24676 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 51342725290691395584
theorem maskCheck24676 :
    checkMaskFor missing24676 StrongPackedBucketN12A4Shard192.record24676 = true := by
  decide

def missing24677 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 53072107547601666048
theorem maskCheck24677 :
    checkMaskFor missing24677 StrongPackedBucketN12A4Shard192.record24677 = true := by
  decide

def missing24678 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64673380187708063744
theorem maskCheck24678 :
    checkMaskFor missing24678 StrongPackedBucketN12A4Shard192.record24678 = true := by
  decide

def missing24679 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64745437781745991680
theorem maskCheck24679 :
    checkMaskFor missing24679 StrongPackedBucketN12A4Shard192.record24679 = true := by
  decide

def missing24680 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64781466578764955648
theorem maskCheck24680 :
    checkMaskFor missing24680 StrongPackedBucketN12A4Shard192.record24680 = true := by
  decide

def missing24681 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64997639360878739456
theorem maskCheck24681 :
    checkMaskFor missing24681 StrongPackedBucketN12A4Shard192.record24681 = true := by
  decide

def missing24682 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 65177783345973559296
theorem maskCheck24682 :
    checkMaskFor missing24682 StrongPackedBucketN12A4Shard192.record24682 = true := by
  decide

def missing24683 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 65213812142992523264
theorem maskCheck24683 :
    checkMaskFor missing24683 StrongPackedBucketN12A4Shard192.record24683 = true := by
  decide

def missing24684 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 65285869737030451200
theorem maskCheck24684 :
    checkMaskFor missing24684 StrongPackedBucketN12A4Shard192.record24684 = true := by
  decide

def missing24685 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 66294676053561442304
theorem maskCheck24685 :
    checkMaskFor missing24685 StrongPackedBucketN12A4Shard192.record24685 = true := by
  decide

def missing24686 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 66907165602883829760
theorem maskCheck24686 :
    checkMaskFor missing24686 StrongPackedBucketN12A4Shard192.record24686 = true := by
  decide

def missing24687 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 66943194399902793728
theorem maskCheck24687 :
    checkMaskFor missing24687 StrongPackedBucketN12A4Shard192.record24687 = true := by
  decide

def missing24688 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 67015251993940721664
theorem maskCheck24688 :
    checkMaskFor missing24688 StrongPackedBucketN12A4Shard192.record24688 = true := by
  decide

def missing24689 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 67447597558168289280
theorem maskCheck24689 :
    checkMaskFor missing24689 StrongPackedBucketN12A4Shard192.record24689 = true := by
  decide

def missing24690 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 69213008612097523712
theorem maskCheck24690 :
    checkMaskFor missing24690 StrongPackedBucketN12A4Shard192.record24690 = true := by
  decide

def missing24691 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1045082092962054144
theorem maskCheck24691 :
    checkMaskFor missing24691 StrongPackedBucketN12A4Shard192.record24691 = true := by
  decide

def missing24692 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1909773221417189376
theorem maskCheck24692 :
    checkMaskFor missing24692 StrongPackedBucketN12A4Shard192.record24692 = true := by
  decide

def missing24693 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2053888409493045248
theorem maskCheck24693 :
    checkMaskFor missing24693 StrongPackedBucketN12A4Shard192.record24693 = true := by
  decide

def missing24694 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2161974800549937152
theorem maskCheck24694 :
    checkMaskFor missing24694 StrongPackedBucketN12A4Shard192.record24694 = true := by
  decide

def missing24695 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4071501042555027456
theorem maskCheck24695 :
    checkMaskFor missing24695 StrongPackedBucketN12A4Shard192.record24695 = true := by
  decide

def missing24696 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4179587433611919360
theorem maskCheck24696 :
    checkMaskFor missing24696 StrongPackedBucketN12A4Shard192.record24696 = true := by
  decide

def missing24697 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4323702621687775232
theorem maskCheck24697 :
    checkMaskFor missing24697 StrongPackedBucketN12A4Shard192.record24697 = true := by
  decide

def missing24698 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5008249765048090624
theorem maskCheck24698 :
    checkMaskFor missing24698 StrongPackedBucketN12A4Shard192.record24698 = true := by
  decide

def missing24699 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5080307359086018560
theorem maskCheck24699 :
    checkMaskFor missing24699 StrongPackedBucketN12A4Shard192.record24699 = true := by
  decide

def missing24700 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5116336156104982528
theorem maskCheck24700 :
    checkMaskFor missing24700 StrongPackedBucketN12A4Shard192.record24700 = true := by
  decide

def missing24701 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5368537735237730304
theorem maskCheck24701 :
    checkMaskFor missing24701 StrongPackedBucketN12A4Shard192.record24701 = true := by
  decide

def missing24702 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5512652923313586176
theorem maskCheck24702 :
    checkMaskFor missing24702 StrongPackedBucketN12A4Shard192.record24702 = true := by
  decide

def missing24703 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5548681720332550144
theorem maskCheck24703 :
    checkMaskFor missing24703 StrongPackedBucketN12A4Shard192.record24703 = true := by
  decide

def missing24576_24577 : List (BitVec (edgeCount 12)) :=
  [missing24576]
abbrev records24576_24577 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24576]
theorem aligned24576_24577 :
    AlignedValid 12 4 missing24576_24577 records24576_24577 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24576
    maskCheck24576 AlignedValid.nil

def missing24577_24578 : List (BitVec (edgeCount 12)) :=
  [missing24577]
abbrev records24577_24578 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24577]
theorem aligned24577_24578 :
    AlignedValid 12 4 missing24577_24578 records24577_24578 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24577
    maskCheck24577 AlignedValid.nil

def missing24576_24578 : List (BitVec (edgeCount 12)) :=
  missing24576_24577 ++ missing24577_24578
abbrev records24576_24578 : List Blob :=
  records24576_24577 ++ records24577_24578
theorem aligned24576_24578 :
    AlignedValid 12 4 missing24576_24578 records24576_24578 :=
  aligned24576_24577.append aligned24577_24578

def missing24578_24579 : List (BitVec (edgeCount 12)) :=
  [missing24578]
abbrev records24578_24579 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24578]
theorem aligned24578_24579 :
    AlignedValid 12 4 missing24578_24579 records24578_24579 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24578
    maskCheck24578 AlignedValid.nil

def missing24579_24580 : List (BitVec (edgeCount 12)) :=
  [missing24579]
abbrev records24579_24580 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24579]
theorem aligned24579_24580 :
    AlignedValid 12 4 missing24579_24580 records24579_24580 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24579
    maskCheck24579 AlignedValid.nil

def missing24578_24580 : List (BitVec (edgeCount 12)) :=
  missing24578_24579 ++ missing24579_24580
abbrev records24578_24580 : List Blob :=
  records24578_24579 ++ records24579_24580
theorem aligned24578_24580 :
    AlignedValid 12 4 missing24578_24580 records24578_24580 :=
  aligned24578_24579.append aligned24579_24580

def missing24576_24580 : List (BitVec (edgeCount 12)) :=
  missing24576_24578 ++ missing24578_24580
abbrev records24576_24580 : List Blob :=
  records24576_24578 ++ records24578_24580
theorem aligned24576_24580 :
    AlignedValid 12 4 missing24576_24580 records24576_24580 :=
  aligned24576_24578.append aligned24578_24580

def missing24580_24581 : List (BitVec (edgeCount 12)) :=
  [missing24580]
abbrev records24580_24581 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24580]
theorem aligned24580_24581 :
    AlignedValid 12 4 missing24580_24581 records24580_24581 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24580
    maskCheck24580 AlignedValid.nil

def missing24581_24582 : List (BitVec (edgeCount 12)) :=
  [missing24581]
abbrev records24581_24582 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24581]
theorem aligned24581_24582 :
    AlignedValid 12 4 missing24581_24582 records24581_24582 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24581
    maskCheck24581 AlignedValid.nil

def missing24580_24582 : List (BitVec (edgeCount 12)) :=
  missing24580_24581 ++ missing24581_24582
abbrev records24580_24582 : List Blob :=
  records24580_24581 ++ records24581_24582
theorem aligned24580_24582 :
    AlignedValid 12 4 missing24580_24582 records24580_24582 :=
  aligned24580_24581.append aligned24581_24582

def missing24582_24583 : List (BitVec (edgeCount 12)) :=
  [missing24582]
abbrev records24582_24583 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24582]
theorem aligned24582_24583 :
    AlignedValid 12 4 missing24582_24583 records24582_24583 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24582
    maskCheck24582 AlignedValid.nil

def missing24583_24584 : List (BitVec (edgeCount 12)) :=
  [missing24583]
abbrev records24583_24584 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24583]
theorem aligned24583_24584 :
    AlignedValid 12 4 missing24583_24584 records24583_24584 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24583
    maskCheck24583 AlignedValid.nil

def missing24582_24584 : List (BitVec (edgeCount 12)) :=
  missing24582_24583 ++ missing24583_24584
abbrev records24582_24584 : List Blob :=
  records24582_24583 ++ records24583_24584
theorem aligned24582_24584 :
    AlignedValid 12 4 missing24582_24584 records24582_24584 :=
  aligned24582_24583.append aligned24583_24584

def missing24580_24584 : List (BitVec (edgeCount 12)) :=
  missing24580_24582 ++ missing24582_24584
abbrev records24580_24584 : List Blob :=
  records24580_24582 ++ records24582_24584
theorem aligned24580_24584 :
    AlignedValid 12 4 missing24580_24584 records24580_24584 :=
  aligned24580_24582.append aligned24582_24584

def missing24576_24584 : List (BitVec (edgeCount 12)) :=
  missing24576_24580 ++ missing24580_24584
abbrev records24576_24584 : List Blob :=
  records24576_24580 ++ records24580_24584
theorem aligned24576_24584 :
    AlignedValid 12 4 missing24576_24584 records24576_24584 :=
  aligned24576_24580.append aligned24580_24584

def missing24584_24585 : List (BitVec (edgeCount 12)) :=
  [missing24584]
abbrev records24584_24585 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24584]
theorem aligned24584_24585 :
    AlignedValid 12 4 missing24584_24585 records24584_24585 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24584
    maskCheck24584 AlignedValid.nil

def missing24585_24586 : List (BitVec (edgeCount 12)) :=
  [missing24585]
abbrev records24585_24586 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24585]
theorem aligned24585_24586 :
    AlignedValid 12 4 missing24585_24586 records24585_24586 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24585
    maskCheck24585 AlignedValid.nil

def missing24584_24586 : List (BitVec (edgeCount 12)) :=
  missing24584_24585 ++ missing24585_24586
abbrev records24584_24586 : List Blob :=
  records24584_24585 ++ records24585_24586
theorem aligned24584_24586 :
    AlignedValid 12 4 missing24584_24586 records24584_24586 :=
  aligned24584_24585.append aligned24585_24586

def missing24586_24587 : List (BitVec (edgeCount 12)) :=
  [missing24586]
abbrev records24586_24587 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24586]
theorem aligned24586_24587 :
    AlignedValid 12 4 missing24586_24587 records24586_24587 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24586
    maskCheck24586 AlignedValid.nil

def missing24587_24588 : List (BitVec (edgeCount 12)) :=
  [missing24587]
abbrev records24587_24588 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24587]
theorem aligned24587_24588 :
    AlignedValid 12 4 missing24587_24588 records24587_24588 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24587
    maskCheck24587 AlignedValid.nil

def missing24586_24588 : List (BitVec (edgeCount 12)) :=
  missing24586_24587 ++ missing24587_24588
abbrev records24586_24588 : List Blob :=
  records24586_24587 ++ records24587_24588
theorem aligned24586_24588 :
    AlignedValid 12 4 missing24586_24588 records24586_24588 :=
  aligned24586_24587.append aligned24587_24588

def missing24584_24588 : List (BitVec (edgeCount 12)) :=
  missing24584_24586 ++ missing24586_24588
abbrev records24584_24588 : List Blob :=
  records24584_24586 ++ records24586_24588
theorem aligned24584_24588 :
    AlignedValid 12 4 missing24584_24588 records24584_24588 :=
  aligned24584_24586.append aligned24586_24588

def missing24588_24589 : List (BitVec (edgeCount 12)) :=
  [missing24588]
abbrev records24588_24589 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24588]
theorem aligned24588_24589 :
    AlignedValid 12 4 missing24588_24589 records24588_24589 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24588
    maskCheck24588 AlignedValid.nil

def missing24589_24590 : List (BitVec (edgeCount 12)) :=
  [missing24589]
abbrev records24589_24590 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24589]
theorem aligned24589_24590 :
    AlignedValid 12 4 missing24589_24590 records24589_24590 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24589
    maskCheck24589 AlignedValid.nil

def missing24588_24590 : List (BitVec (edgeCount 12)) :=
  missing24588_24589 ++ missing24589_24590
abbrev records24588_24590 : List Blob :=
  records24588_24589 ++ records24589_24590
theorem aligned24588_24590 :
    AlignedValid 12 4 missing24588_24590 records24588_24590 :=
  aligned24588_24589.append aligned24589_24590

def missing24590_24591 : List (BitVec (edgeCount 12)) :=
  [missing24590]
abbrev records24590_24591 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24590]
theorem aligned24590_24591 :
    AlignedValid 12 4 missing24590_24591 records24590_24591 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24590
    maskCheck24590 AlignedValid.nil

def missing24591_24592 : List (BitVec (edgeCount 12)) :=
  [missing24591]
abbrev records24591_24592 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24591]
theorem aligned24591_24592 :
    AlignedValid 12 4 missing24591_24592 records24591_24592 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24591
    maskCheck24591 AlignedValid.nil

def missing24590_24592 : List (BitVec (edgeCount 12)) :=
  missing24590_24591 ++ missing24591_24592
abbrev records24590_24592 : List Blob :=
  records24590_24591 ++ records24591_24592
theorem aligned24590_24592 :
    AlignedValid 12 4 missing24590_24592 records24590_24592 :=
  aligned24590_24591.append aligned24591_24592

def missing24588_24592 : List (BitVec (edgeCount 12)) :=
  missing24588_24590 ++ missing24590_24592
abbrev records24588_24592 : List Blob :=
  records24588_24590 ++ records24590_24592
theorem aligned24588_24592 :
    AlignedValid 12 4 missing24588_24592 records24588_24592 :=
  aligned24588_24590.append aligned24590_24592

def missing24584_24592 : List (BitVec (edgeCount 12)) :=
  missing24584_24588 ++ missing24588_24592
abbrev records24584_24592 : List Blob :=
  records24584_24588 ++ records24588_24592
theorem aligned24584_24592 :
    AlignedValid 12 4 missing24584_24592 records24584_24592 :=
  aligned24584_24588.append aligned24588_24592

def missing24576_24592 : List (BitVec (edgeCount 12)) :=
  missing24576_24584 ++ missing24584_24592
abbrev records24576_24592 : List Blob :=
  records24576_24584 ++ records24584_24592
theorem aligned24576_24592 :
    AlignedValid 12 4 missing24576_24592 records24576_24592 :=
  aligned24576_24584.append aligned24584_24592

def missing24592_24593 : List (BitVec (edgeCount 12)) :=
  [missing24592]
abbrev records24592_24593 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24592]
theorem aligned24592_24593 :
    AlignedValid 12 4 missing24592_24593 records24592_24593 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24592
    maskCheck24592 AlignedValid.nil

def missing24593_24594 : List (BitVec (edgeCount 12)) :=
  [missing24593]
abbrev records24593_24594 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24593]
theorem aligned24593_24594 :
    AlignedValid 12 4 missing24593_24594 records24593_24594 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24593
    maskCheck24593 AlignedValid.nil

def missing24592_24594 : List (BitVec (edgeCount 12)) :=
  missing24592_24593 ++ missing24593_24594
abbrev records24592_24594 : List Blob :=
  records24592_24593 ++ records24593_24594
theorem aligned24592_24594 :
    AlignedValid 12 4 missing24592_24594 records24592_24594 :=
  aligned24592_24593.append aligned24593_24594

def missing24594_24595 : List (BitVec (edgeCount 12)) :=
  [missing24594]
abbrev records24594_24595 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24594]
theorem aligned24594_24595 :
    AlignedValid 12 4 missing24594_24595 records24594_24595 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24594
    maskCheck24594 AlignedValid.nil

def missing24595_24596 : List (BitVec (edgeCount 12)) :=
  [missing24595]
abbrev records24595_24596 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24595]
theorem aligned24595_24596 :
    AlignedValid 12 4 missing24595_24596 records24595_24596 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24595
    maskCheck24595 AlignedValid.nil

def missing24594_24596 : List (BitVec (edgeCount 12)) :=
  missing24594_24595 ++ missing24595_24596
abbrev records24594_24596 : List Blob :=
  records24594_24595 ++ records24595_24596
theorem aligned24594_24596 :
    AlignedValid 12 4 missing24594_24596 records24594_24596 :=
  aligned24594_24595.append aligned24595_24596

def missing24592_24596 : List (BitVec (edgeCount 12)) :=
  missing24592_24594 ++ missing24594_24596
abbrev records24592_24596 : List Blob :=
  records24592_24594 ++ records24594_24596
theorem aligned24592_24596 :
    AlignedValid 12 4 missing24592_24596 records24592_24596 :=
  aligned24592_24594.append aligned24594_24596

def missing24596_24597 : List (BitVec (edgeCount 12)) :=
  [missing24596]
abbrev records24596_24597 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24596]
theorem aligned24596_24597 :
    AlignedValid 12 4 missing24596_24597 records24596_24597 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24596
    maskCheck24596 AlignedValid.nil

def missing24597_24598 : List (BitVec (edgeCount 12)) :=
  [missing24597]
abbrev records24597_24598 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24597]
theorem aligned24597_24598 :
    AlignedValid 12 4 missing24597_24598 records24597_24598 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24597
    maskCheck24597 AlignedValid.nil

def missing24596_24598 : List (BitVec (edgeCount 12)) :=
  missing24596_24597 ++ missing24597_24598
abbrev records24596_24598 : List Blob :=
  records24596_24597 ++ records24597_24598
theorem aligned24596_24598 :
    AlignedValid 12 4 missing24596_24598 records24596_24598 :=
  aligned24596_24597.append aligned24597_24598

def missing24598_24599 : List (BitVec (edgeCount 12)) :=
  [missing24598]
abbrev records24598_24599 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24598]
theorem aligned24598_24599 :
    AlignedValid 12 4 missing24598_24599 records24598_24599 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24598
    maskCheck24598 AlignedValid.nil

def missing24599_24600 : List (BitVec (edgeCount 12)) :=
  [missing24599]
abbrev records24599_24600 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24599]
theorem aligned24599_24600 :
    AlignedValid 12 4 missing24599_24600 records24599_24600 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24599
    maskCheck24599 AlignedValid.nil

def missing24598_24600 : List (BitVec (edgeCount 12)) :=
  missing24598_24599 ++ missing24599_24600
abbrev records24598_24600 : List Blob :=
  records24598_24599 ++ records24599_24600
theorem aligned24598_24600 :
    AlignedValid 12 4 missing24598_24600 records24598_24600 :=
  aligned24598_24599.append aligned24599_24600

def missing24596_24600 : List (BitVec (edgeCount 12)) :=
  missing24596_24598 ++ missing24598_24600
abbrev records24596_24600 : List Blob :=
  records24596_24598 ++ records24598_24600
theorem aligned24596_24600 :
    AlignedValid 12 4 missing24596_24600 records24596_24600 :=
  aligned24596_24598.append aligned24598_24600

def missing24592_24600 : List (BitVec (edgeCount 12)) :=
  missing24592_24596 ++ missing24596_24600
abbrev records24592_24600 : List Blob :=
  records24592_24596 ++ records24596_24600
theorem aligned24592_24600 :
    AlignedValid 12 4 missing24592_24600 records24592_24600 :=
  aligned24592_24596.append aligned24596_24600

def missing24600_24601 : List (BitVec (edgeCount 12)) :=
  [missing24600]
abbrev records24600_24601 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24600]
theorem aligned24600_24601 :
    AlignedValid 12 4 missing24600_24601 records24600_24601 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24600
    maskCheck24600 AlignedValid.nil

def missing24601_24602 : List (BitVec (edgeCount 12)) :=
  [missing24601]
abbrev records24601_24602 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24601]
theorem aligned24601_24602 :
    AlignedValid 12 4 missing24601_24602 records24601_24602 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24601
    maskCheck24601 AlignedValid.nil

def missing24600_24602 : List (BitVec (edgeCount 12)) :=
  missing24600_24601 ++ missing24601_24602
abbrev records24600_24602 : List Blob :=
  records24600_24601 ++ records24601_24602
theorem aligned24600_24602 :
    AlignedValid 12 4 missing24600_24602 records24600_24602 :=
  aligned24600_24601.append aligned24601_24602

def missing24602_24603 : List (BitVec (edgeCount 12)) :=
  [missing24602]
abbrev records24602_24603 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24602]
theorem aligned24602_24603 :
    AlignedValid 12 4 missing24602_24603 records24602_24603 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24602
    maskCheck24602 AlignedValid.nil

def missing24603_24604 : List (BitVec (edgeCount 12)) :=
  [missing24603]
abbrev records24603_24604 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24603]
theorem aligned24603_24604 :
    AlignedValid 12 4 missing24603_24604 records24603_24604 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24603
    maskCheck24603 AlignedValid.nil

def missing24602_24604 : List (BitVec (edgeCount 12)) :=
  missing24602_24603 ++ missing24603_24604
abbrev records24602_24604 : List Blob :=
  records24602_24603 ++ records24603_24604
theorem aligned24602_24604 :
    AlignedValid 12 4 missing24602_24604 records24602_24604 :=
  aligned24602_24603.append aligned24603_24604

def missing24600_24604 : List (BitVec (edgeCount 12)) :=
  missing24600_24602 ++ missing24602_24604
abbrev records24600_24604 : List Blob :=
  records24600_24602 ++ records24602_24604
theorem aligned24600_24604 :
    AlignedValid 12 4 missing24600_24604 records24600_24604 :=
  aligned24600_24602.append aligned24602_24604

def missing24604_24605 : List (BitVec (edgeCount 12)) :=
  [missing24604]
abbrev records24604_24605 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24604]
theorem aligned24604_24605 :
    AlignedValid 12 4 missing24604_24605 records24604_24605 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24604
    maskCheck24604 AlignedValid.nil

def missing24605_24606 : List (BitVec (edgeCount 12)) :=
  [missing24605]
abbrev records24605_24606 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24605]
theorem aligned24605_24606 :
    AlignedValid 12 4 missing24605_24606 records24605_24606 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24605
    maskCheck24605 AlignedValid.nil

def missing24604_24606 : List (BitVec (edgeCount 12)) :=
  missing24604_24605 ++ missing24605_24606
abbrev records24604_24606 : List Blob :=
  records24604_24605 ++ records24605_24606
theorem aligned24604_24606 :
    AlignedValid 12 4 missing24604_24606 records24604_24606 :=
  aligned24604_24605.append aligned24605_24606

def missing24606_24607 : List (BitVec (edgeCount 12)) :=
  [missing24606]
abbrev records24606_24607 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24606]
theorem aligned24606_24607 :
    AlignedValid 12 4 missing24606_24607 records24606_24607 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24606
    maskCheck24606 AlignedValid.nil

def missing24607_24608 : List (BitVec (edgeCount 12)) :=
  [missing24607]
abbrev records24607_24608 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24607]
theorem aligned24607_24608 :
    AlignedValid 12 4 missing24607_24608 records24607_24608 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24607
    maskCheck24607 AlignedValid.nil

def missing24606_24608 : List (BitVec (edgeCount 12)) :=
  missing24606_24607 ++ missing24607_24608
abbrev records24606_24608 : List Blob :=
  records24606_24607 ++ records24607_24608
theorem aligned24606_24608 :
    AlignedValid 12 4 missing24606_24608 records24606_24608 :=
  aligned24606_24607.append aligned24607_24608

def missing24604_24608 : List (BitVec (edgeCount 12)) :=
  missing24604_24606 ++ missing24606_24608
abbrev records24604_24608 : List Blob :=
  records24604_24606 ++ records24606_24608
theorem aligned24604_24608 :
    AlignedValid 12 4 missing24604_24608 records24604_24608 :=
  aligned24604_24606.append aligned24606_24608

def missing24600_24608 : List (BitVec (edgeCount 12)) :=
  missing24600_24604 ++ missing24604_24608
abbrev records24600_24608 : List Blob :=
  records24600_24604 ++ records24604_24608
theorem aligned24600_24608 :
    AlignedValid 12 4 missing24600_24608 records24600_24608 :=
  aligned24600_24604.append aligned24604_24608

def missing24592_24608 : List (BitVec (edgeCount 12)) :=
  missing24592_24600 ++ missing24600_24608
abbrev records24592_24608 : List Blob :=
  records24592_24600 ++ records24600_24608
theorem aligned24592_24608 :
    AlignedValid 12 4 missing24592_24608 records24592_24608 :=
  aligned24592_24600.append aligned24600_24608

def missing24576_24608 : List (BitVec (edgeCount 12)) :=
  missing24576_24592 ++ missing24592_24608
abbrev records24576_24608 : List Blob :=
  records24576_24592 ++ records24592_24608
theorem aligned24576_24608 :
    AlignedValid 12 4 missing24576_24608 records24576_24608 :=
  aligned24576_24592.append aligned24592_24608

def missing24608_24609 : List (BitVec (edgeCount 12)) :=
  [missing24608]
abbrev records24608_24609 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24608]
theorem aligned24608_24609 :
    AlignedValid 12 4 missing24608_24609 records24608_24609 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24608
    maskCheck24608 AlignedValid.nil

def missing24609_24610 : List (BitVec (edgeCount 12)) :=
  [missing24609]
abbrev records24609_24610 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24609]
theorem aligned24609_24610 :
    AlignedValid 12 4 missing24609_24610 records24609_24610 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24609
    maskCheck24609 AlignedValid.nil

def missing24608_24610 : List (BitVec (edgeCount 12)) :=
  missing24608_24609 ++ missing24609_24610
abbrev records24608_24610 : List Blob :=
  records24608_24609 ++ records24609_24610
theorem aligned24608_24610 :
    AlignedValid 12 4 missing24608_24610 records24608_24610 :=
  aligned24608_24609.append aligned24609_24610

def missing24610_24611 : List (BitVec (edgeCount 12)) :=
  [missing24610]
abbrev records24610_24611 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24610]
theorem aligned24610_24611 :
    AlignedValid 12 4 missing24610_24611 records24610_24611 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24610
    maskCheck24610 AlignedValid.nil

def missing24611_24612 : List (BitVec (edgeCount 12)) :=
  [missing24611]
abbrev records24611_24612 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24611]
theorem aligned24611_24612 :
    AlignedValid 12 4 missing24611_24612 records24611_24612 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24611
    maskCheck24611 AlignedValid.nil

def missing24610_24612 : List (BitVec (edgeCount 12)) :=
  missing24610_24611 ++ missing24611_24612
abbrev records24610_24612 : List Blob :=
  records24610_24611 ++ records24611_24612
theorem aligned24610_24612 :
    AlignedValid 12 4 missing24610_24612 records24610_24612 :=
  aligned24610_24611.append aligned24611_24612

def missing24608_24612 : List (BitVec (edgeCount 12)) :=
  missing24608_24610 ++ missing24610_24612
abbrev records24608_24612 : List Blob :=
  records24608_24610 ++ records24610_24612
theorem aligned24608_24612 :
    AlignedValid 12 4 missing24608_24612 records24608_24612 :=
  aligned24608_24610.append aligned24610_24612

def missing24612_24613 : List (BitVec (edgeCount 12)) :=
  [missing24612]
abbrev records24612_24613 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24612]
theorem aligned24612_24613 :
    AlignedValid 12 4 missing24612_24613 records24612_24613 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24612
    maskCheck24612 AlignedValid.nil

def missing24613_24614 : List (BitVec (edgeCount 12)) :=
  [missing24613]
abbrev records24613_24614 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24613]
theorem aligned24613_24614 :
    AlignedValid 12 4 missing24613_24614 records24613_24614 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24613
    maskCheck24613 AlignedValid.nil

def missing24612_24614 : List (BitVec (edgeCount 12)) :=
  missing24612_24613 ++ missing24613_24614
abbrev records24612_24614 : List Blob :=
  records24612_24613 ++ records24613_24614
theorem aligned24612_24614 :
    AlignedValid 12 4 missing24612_24614 records24612_24614 :=
  aligned24612_24613.append aligned24613_24614

def missing24614_24615 : List (BitVec (edgeCount 12)) :=
  [missing24614]
abbrev records24614_24615 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24614]
theorem aligned24614_24615 :
    AlignedValid 12 4 missing24614_24615 records24614_24615 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24614
    maskCheck24614 AlignedValid.nil

def missing24615_24616 : List (BitVec (edgeCount 12)) :=
  [missing24615]
abbrev records24615_24616 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24615]
theorem aligned24615_24616 :
    AlignedValid 12 4 missing24615_24616 records24615_24616 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24615
    maskCheck24615 AlignedValid.nil

def missing24614_24616 : List (BitVec (edgeCount 12)) :=
  missing24614_24615 ++ missing24615_24616
abbrev records24614_24616 : List Blob :=
  records24614_24615 ++ records24615_24616
theorem aligned24614_24616 :
    AlignedValid 12 4 missing24614_24616 records24614_24616 :=
  aligned24614_24615.append aligned24615_24616

def missing24612_24616 : List (BitVec (edgeCount 12)) :=
  missing24612_24614 ++ missing24614_24616
abbrev records24612_24616 : List Blob :=
  records24612_24614 ++ records24614_24616
theorem aligned24612_24616 :
    AlignedValid 12 4 missing24612_24616 records24612_24616 :=
  aligned24612_24614.append aligned24614_24616

def missing24608_24616 : List (BitVec (edgeCount 12)) :=
  missing24608_24612 ++ missing24612_24616
abbrev records24608_24616 : List Blob :=
  records24608_24612 ++ records24612_24616
theorem aligned24608_24616 :
    AlignedValid 12 4 missing24608_24616 records24608_24616 :=
  aligned24608_24612.append aligned24612_24616

def missing24616_24617 : List (BitVec (edgeCount 12)) :=
  [missing24616]
abbrev records24616_24617 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24616]
theorem aligned24616_24617 :
    AlignedValid 12 4 missing24616_24617 records24616_24617 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24616
    maskCheck24616 AlignedValid.nil

def missing24617_24618 : List (BitVec (edgeCount 12)) :=
  [missing24617]
abbrev records24617_24618 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24617]
theorem aligned24617_24618 :
    AlignedValid 12 4 missing24617_24618 records24617_24618 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24617
    maskCheck24617 AlignedValid.nil

def missing24616_24618 : List (BitVec (edgeCount 12)) :=
  missing24616_24617 ++ missing24617_24618
abbrev records24616_24618 : List Blob :=
  records24616_24617 ++ records24617_24618
theorem aligned24616_24618 :
    AlignedValid 12 4 missing24616_24618 records24616_24618 :=
  aligned24616_24617.append aligned24617_24618

def missing24618_24619 : List (BitVec (edgeCount 12)) :=
  [missing24618]
abbrev records24618_24619 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24618]
theorem aligned24618_24619 :
    AlignedValid 12 4 missing24618_24619 records24618_24619 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24618
    maskCheck24618 AlignedValid.nil

def missing24619_24620 : List (BitVec (edgeCount 12)) :=
  [missing24619]
abbrev records24619_24620 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24619]
theorem aligned24619_24620 :
    AlignedValid 12 4 missing24619_24620 records24619_24620 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24619
    maskCheck24619 AlignedValid.nil

def missing24618_24620 : List (BitVec (edgeCount 12)) :=
  missing24618_24619 ++ missing24619_24620
abbrev records24618_24620 : List Blob :=
  records24618_24619 ++ records24619_24620
theorem aligned24618_24620 :
    AlignedValid 12 4 missing24618_24620 records24618_24620 :=
  aligned24618_24619.append aligned24619_24620

def missing24616_24620 : List (BitVec (edgeCount 12)) :=
  missing24616_24618 ++ missing24618_24620
abbrev records24616_24620 : List Blob :=
  records24616_24618 ++ records24618_24620
theorem aligned24616_24620 :
    AlignedValid 12 4 missing24616_24620 records24616_24620 :=
  aligned24616_24618.append aligned24618_24620

def missing24620_24621 : List (BitVec (edgeCount 12)) :=
  [missing24620]
abbrev records24620_24621 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24620]
theorem aligned24620_24621 :
    AlignedValid 12 4 missing24620_24621 records24620_24621 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24620
    maskCheck24620 AlignedValid.nil

def missing24621_24622 : List (BitVec (edgeCount 12)) :=
  [missing24621]
abbrev records24621_24622 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24621]
theorem aligned24621_24622 :
    AlignedValid 12 4 missing24621_24622 records24621_24622 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24621
    maskCheck24621 AlignedValid.nil

def missing24620_24622 : List (BitVec (edgeCount 12)) :=
  missing24620_24621 ++ missing24621_24622
abbrev records24620_24622 : List Blob :=
  records24620_24621 ++ records24621_24622
theorem aligned24620_24622 :
    AlignedValid 12 4 missing24620_24622 records24620_24622 :=
  aligned24620_24621.append aligned24621_24622

def missing24622_24623 : List (BitVec (edgeCount 12)) :=
  [missing24622]
abbrev records24622_24623 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24622]
theorem aligned24622_24623 :
    AlignedValid 12 4 missing24622_24623 records24622_24623 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24622
    maskCheck24622 AlignedValid.nil

def missing24623_24624 : List (BitVec (edgeCount 12)) :=
  [missing24623]
abbrev records24623_24624 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24623]
theorem aligned24623_24624 :
    AlignedValid 12 4 missing24623_24624 records24623_24624 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24623
    maskCheck24623 AlignedValid.nil

def missing24622_24624 : List (BitVec (edgeCount 12)) :=
  missing24622_24623 ++ missing24623_24624
abbrev records24622_24624 : List Blob :=
  records24622_24623 ++ records24623_24624
theorem aligned24622_24624 :
    AlignedValid 12 4 missing24622_24624 records24622_24624 :=
  aligned24622_24623.append aligned24623_24624

def missing24620_24624 : List (BitVec (edgeCount 12)) :=
  missing24620_24622 ++ missing24622_24624
abbrev records24620_24624 : List Blob :=
  records24620_24622 ++ records24622_24624
theorem aligned24620_24624 :
    AlignedValid 12 4 missing24620_24624 records24620_24624 :=
  aligned24620_24622.append aligned24622_24624

def missing24616_24624 : List (BitVec (edgeCount 12)) :=
  missing24616_24620 ++ missing24620_24624
abbrev records24616_24624 : List Blob :=
  records24616_24620 ++ records24620_24624
theorem aligned24616_24624 :
    AlignedValid 12 4 missing24616_24624 records24616_24624 :=
  aligned24616_24620.append aligned24620_24624

def missing24608_24624 : List (BitVec (edgeCount 12)) :=
  missing24608_24616 ++ missing24616_24624
abbrev records24608_24624 : List Blob :=
  records24608_24616 ++ records24616_24624
theorem aligned24608_24624 :
    AlignedValid 12 4 missing24608_24624 records24608_24624 :=
  aligned24608_24616.append aligned24616_24624

def missing24624_24625 : List (BitVec (edgeCount 12)) :=
  [missing24624]
abbrev records24624_24625 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24624]
theorem aligned24624_24625 :
    AlignedValid 12 4 missing24624_24625 records24624_24625 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24624
    maskCheck24624 AlignedValid.nil

def missing24625_24626 : List (BitVec (edgeCount 12)) :=
  [missing24625]
abbrev records24625_24626 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24625]
theorem aligned24625_24626 :
    AlignedValid 12 4 missing24625_24626 records24625_24626 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24625
    maskCheck24625 AlignedValid.nil

def missing24624_24626 : List (BitVec (edgeCount 12)) :=
  missing24624_24625 ++ missing24625_24626
abbrev records24624_24626 : List Blob :=
  records24624_24625 ++ records24625_24626
theorem aligned24624_24626 :
    AlignedValid 12 4 missing24624_24626 records24624_24626 :=
  aligned24624_24625.append aligned24625_24626

def missing24626_24627 : List (BitVec (edgeCount 12)) :=
  [missing24626]
abbrev records24626_24627 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24626]
theorem aligned24626_24627 :
    AlignedValid 12 4 missing24626_24627 records24626_24627 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24626
    maskCheck24626 AlignedValid.nil

def missing24627_24628 : List (BitVec (edgeCount 12)) :=
  [missing24627]
abbrev records24627_24628 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24627]
theorem aligned24627_24628 :
    AlignedValid 12 4 missing24627_24628 records24627_24628 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24627
    maskCheck24627 AlignedValid.nil

def missing24626_24628 : List (BitVec (edgeCount 12)) :=
  missing24626_24627 ++ missing24627_24628
abbrev records24626_24628 : List Blob :=
  records24626_24627 ++ records24627_24628
theorem aligned24626_24628 :
    AlignedValid 12 4 missing24626_24628 records24626_24628 :=
  aligned24626_24627.append aligned24627_24628

def missing24624_24628 : List (BitVec (edgeCount 12)) :=
  missing24624_24626 ++ missing24626_24628
abbrev records24624_24628 : List Blob :=
  records24624_24626 ++ records24626_24628
theorem aligned24624_24628 :
    AlignedValid 12 4 missing24624_24628 records24624_24628 :=
  aligned24624_24626.append aligned24626_24628

def missing24628_24629 : List (BitVec (edgeCount 12)) :=
  [missing24628]
abbrev records24628_24629 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24628]
theorem aligned24628_24629 :
    AlignedValid 12 4 missing24628_24629 records24628_24629 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24628
    maskCheck24628 AlignedValid.nil

def missing24629_24630 : List (BitVec (edgeCount 12)) :=
  [missing24629]
abbrev records24629_24630 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24629]
theorem aligned24629_24630 :
    AlignedValid 12 4 missing24629_24630 records24629_24630 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24629
    maskCheck24629 AlignedValid.nil

def missing24628_24630 : List (BitVec (edgeCount 12)) :=
  missing24628_24629 ++ missing24629_24630
abbrev records24628_24630 : List Blob :=
  records24628_24629 ++ records24629_24630
theorem aligned24628_24630 :
    AlignedValid 12 4 missing24628_24630 records24628_24630 :=
  aligned24628_24629.append aligned24629_24630

def missing24630_24631 : List (BitVec (edgeCount 12)) :=
  [missing24630]
abbrev records24630_24631 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24630]
theorem aligned24630_24631 :
    AlignedValid 12 4 missing24630_24631 records24630_24631 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24630
    maskCheck24630 AlignedValid.nil

def missing24631_24632 : List (BitVec (edgeCount 12)) :=
  [missing24631]
abbrev records24631_24632 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24631]
theorem aligned24631_24632 :
    AlignedValid 12 4 missing24631_24632 records24631_24632 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24631
    maskCheck24631 AlignedValid.nil

def missing24630_24632 : List (BitVec (edgeCount 12)) :=
  missing24630_24631 ++ missing24631_24632
abbrev records24630_24632 : List Blob :=
  records24630_24631 ++ records24631_24632
theorem aligned24630_24632 :
    AlignedValid 12 4 missing24630_24632 records24630_24632 :=
  aligned24630_24631.append aligned24631_24632

def missing24628_24632 : List (BitVec (edgeCount 12)) :=
  missing24628_24630 ++ missing24630_24632
abbrev records24628_24632 : List Blob :=
  records24628_24630 ++ records24630_24632
theorem aligned24628_24632 :
    AlignedValid 12 4 missing24628_24632 records24628_24632 :=
  aligned24628_24630.append aligned24630_24632

def missing24624_24632 : List (BitVec (edgeCount 12)) :=
  missing24624_24628 ++ missing24628_24632
abbrev records24624_24632 : List Blob :=
  records24624_24628 ++ records24628_24632
theorem aligned24624_24632 :
    AlignedValid 12 4 missing24624_24632 records24624_24632 :=
  aligned24624_24628.append aligned24628_24632

def missing24632_24633 : List (BitVec (edgeCount 12)) :=
  [missing24632]
abbrev records24632_24633 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24632]
theorem aligned24632_24633 :
    AlignedValid 12 4 missing24632_24633 records24632_24633 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24632
    maskCheck24632 AlignedValid.nil

def missing24633_24634 : List (BitVec (edgeCount 12)) :=
  [missing24633]
abbrev records24633_24634 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24633]
theorem aligned24633_24634 :
    AlignedValid 12 4 missing24633_24634 records24633_24634 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24633
    maskCheck24633 AlignedValid.nil

def missing24632_24634 : List (BitVec (edgeCount 12)) :=
  missing24632_24633 ++ missing24633_24634
abbrev records24632_24634 : List Blob :=
  records24632_24633 ++ records24633_24634
theorem aligned24632_24634 :
    AlignedValid 12 4 missing24632_24634 records24632_24634 :=
  aligned24632_24633.append aligned24633_24634

def missing24634_24635 : List (BitVec (edgeCount 12)) :=
  [missing24634]
abbrev records24634_24635 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24634]
theorem aligned24634_24635 :
    AlignedValid 12 4 missing24634_24635 records24634_24635 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24634
    maskCheck24634 AlignedValid.nil

def missing24635_24636 : List (BitVec (edgeCount 12)) :=
  [missing24635]
abbrev records24635_24636 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24635]
theorem aligned24635_24636 :
    AlignedValid 12 4 missing24635_24636 records24635_24636 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24635
    maskCheck24635 AlignedValid.nil

def missing24634_24636 : List (BitVec (edgeCount 12)) :=
  missing24634_24635 ++ missing24635_24636
abbrev records24634_24636 : List Blob :=
  records24634_24635 ++ records24635_24636
theorem aligned24634_24636 :
    AlignedValid 12 4 missing24634_24636 records24634_24636 :=
  aligned24634_24635.append aligned24635_24636

def missing24632_24636 : List (BitVec (edgeCount 12)) :=
  missing24632_24634 ++ missing24634_24636
abbrev records24632_24636 : List Blob :=
  records24632_24634 ++ records24634_24636
theorem aligned24632_24636 :
    AlignedValid 12 4 missing24632_24636 records24632_24636 :=
  aligned24632_24634.append aligned24634_24636

def missing24636_24637 : List (BitVec (edgeCount 12)) :=
  [missing24636]
abbrev records24636_24637 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24636]
theorem aligned24636_24637 :
    AlignedValid 12 4 missing24636_24637 records24636_24637 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24636
    maskCheck24636 AlignedValid.nil

def missing24637_24638 : List (BitVec (edgeCount 12)) :=
  [missing24637]
abbrev records24637_24638 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24637]
theorem aligned24637_24638 :
    AlignedValid 12 4 missing24637_24638 records24637_24638 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24637
    maskCheck24637 AlignedValid.nil

def missing24636_24638 : List (BitVec (edgeCount 12)) :=
  missing24636_24637 ++ missing24637_24638
abbrev records24636_24638 : List Blob :=
  records24636_24637 ++ records24637_24638
theorem aligned24636_24638 :
    AlignedValid 12 4 missing24636_24638 records24636_24638 :=
  aligned24636_24637.append aligned24637_24638

def missing24638_24639 : List (BitVec (edgeCount 12)) :=
  [missing24638]
abbrev records24638_24639 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24638]
theorem aligned24638_24639 :
    AlignedValid 12 4 missing24638_24639 records24638_24639 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24638
    maskCheck24638 AlignedValid.nil

def missing24639_24640 : List (BitVec (edgeCount 12)) :=
  [missing24639]
abbrev records24639_24640 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24639]
theorem aligned24639_24640 :
    AlignedValid 12 4 missing24639_24640 records24639_24640 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24639
    maskCheck24639 AlignedValid.nil

def missing24638_24640 : List (BitVec (edgeCount 12)) :=
  missing24638_24639 ++ missing24639_24640
abbrev records24638_24640 : List Blob :=
  records24638_24639 ++ records24639_24640
theorem aligned24638_24640 :
    AlignedValid 12 4 missing24638_24640 records24638_24640 :=
  aligned24638_24639.append aligned24639_24640

def missing24636_24640 : List (BitVec (edgeCount 12)) :=
  missing24636_24638 ++ missing24638_24640
abbrev records24636_24640 : List Blob :=
  records24636_24638 ++ records24638_24640
theorem aligned24636_24640 :
    AlignedValid 12 4 missing24636_24640 records24636_24640 :=
  aligned24636_24638.append aligned24638_24640

def missing24632_24640 : List (BitVec (edgeCount 12)) :=
  missing24632_24636 ++ missing24636_24640
abbrev records24632_24640 : List Blob :=
  records24632_24636 ++ records24636_24640
theorem aligned24632_24640 :
    AlignedValid 12 4 missing24632_24640 records24632_24640 :=
  aligned24632_24636.append aligned24636_24640

def missing24624_24640 : List (BitVec (edgeCount 12)) :=
  missing24624_24632 ++ missing24632_24640
abbrev records24624_24640 : List Blob :=
  records24624_24632 ++ records24632_24640
theorem aligned24624_24640 :
    AlignedValid 12 4 missing24624_24640 records24624_24640 :=
  aligned24624_24632.append aligned24632_24640

def missing24608_24640 : List (BitVec (edgeCount 12)) :=
  missing24608_24624 ++ missing24624_24640
abbrev records24608_24640 : List Blob :=
  records24608_24624 ++ records24624_24640
theorem aligned24608_24640 :
    AlignedValid 12 4 missing24608_24640 records24608_24640 :=
  aligned24608_24624.append aligned24624_24640

def missing24576_24640 : List (BitVec (edgeCount 12)) :=
  missing24576_24608 ++ missing24608_24640
abbrev records24576_24640 : List Blob :=
  records24576_24608 ++ records24608_24640
theorem aligned24576_24640 :
    AlignedValid 12 4 missing24576_24640 records24576_24640 :=
  aligned24576_24608.append aligned24608_24640

def missing24640_24641 : List (BitVec (edgeCount 12)) :=
  [missing24640]
abbrev records24640_24641 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24640]
theorem aligned24640_24641 :
    AlignedValid 12 4 missing24640_24641 records24640_24641 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24640
    maskCheck24640 AlignedValid.nil

def missing24641_24642 : List (BitVec (edgeCount 12)) :=
  [missing24641]
abbrev records24641_24642 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24641]
theorem aligned24641_24642 :
    AlignedValid 12 4 missing24641_24642 records24641_24642 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24641
    maskCheck24641 AlignedValid.nil

def missing24640_24642 : List (BitVec (edgeCount 12)) :=
  missing24640_24641 ++ missing24641_24642
abbrev records24640_24642 : List Blob :=
  records24640_24641 ++ records24641_24642
theorem aligned24640_24642 :
    AlignedValid 12 4 missing24640_24642 records24640_24642 :=
  aligned24640_24641.append aligned24641_24642

def missing24642_24643 : List (BitVec (edgeCount 12)) :=
  [missing24642]
abbrev records24642_24643 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24642]
theorem aligned24642_24643 :
    AlignedValid 12 4 missing24642_24643 records24642_24643 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24642
    maskCheck24642 AlignedValid.nil

def missing24643_24644 : List (BitVec (edgeCount 12)) :=
  [missing24643]
abbrev records24643_24644 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24643]
theorem aligned24643_24644 :
    AlignedValid 12 4 missing24643_24644 records24643_24644 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24643
    maskCheck24643 AlignedValid.nil

def missing24642_24644 : List (BitVec (edgeCount 12)) :=
  missing24642_24643 ++ missing24643_24644
abbrev records24642_24644 : List Blob :=
  records24642_24643 ++ records24643_24644
theorem aligned24642_24644 :
    AlignedValid 12 4 missing24642_24644 records24642_24644 :=
  aligned24642_24643.append aligned24643_24644

def missing24640_24644 : List (BitVec (edgeCount 12)) :=
  missing24640_24642 ++ missing24642_24644
abbrev records24640_24644 : List Blob :=
  records24640_24642 ++ records24642_24644
theorem aligned24640_24644 :
    AlignedValid 12 4 missing24640_24644 records24640_24644 :=
  aligned24640_24642.append aligned24642_24644

def missing24644_24645 : List (BitVec (edgeCount 12)) :=
  [missing24644]
abbrev records24644_24645 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24644]
theorem aligned24644_24645 :
    AlignedValid 12 4 missing24644_24645 records24644_24645 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24644
    maskCheck24644 AlignedValid.nil

def missing24645_24646 : List (BitVec (edgeCount 12)) :=
  [missing24645]
abbrev records24645_24646 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24645]
theorem aligned24645_24646 :
    AlignedValid 12 4 missing24645_24646 records24645_24646 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24645
    maskCheck24645 AlignedValid.nil

def missing24644_24646 : List (BitVec (edgeCount 12)) :=
  missing24644_24645 ++ missing24645_24646
abbrev records24644_24646 : List Blob :=
  records24644_24645 ++ records24645_24646
theorem aligned24644_24646 :
    AlignedValid 12 4 missing24644_24646 records24644_24646 :=
  aligned24644_24645.append aligned24645_24646

def missing24646_24647 : List (BitVec (edgeCount 12)) :=
  [missing24646]
abbrev records24646_24647 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24646]
theorem aligned24646_24647 :
    AlignedValid 12 4 missing24646_24647 records24646_24647 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24646
    maskCheck24646 AlignedValid.nil

def missing24647_24648 : List (BitVec (edgeCount 12)) :=
  [missing24647]
abbrev records24647_24648 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24647]
theorem aligned24647_24648 :
    AlignedValid 12 4 missing24647_24648 records24647_24648 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24647
    maskCheck24647 AlignedValid.nil

def missing24646_24648 : List (BitVec (edgeCount 12)) :=
  missing24646_24647 ++ missing24647_24648
abbrev records24646_24648 : List Blob :=
  records24646_24647 ++ records24647_24648
theorem aligned24646_24648 :
    AlignedValid 12 4 missing24646_24648 records24646_24648 :=
  aligned24646_24647.append aligned24647_24648

def missing24644_24648 : List (BitVec (edgeCount 12)) :=
  missing24644_24646 ++ missing24646_24648
abbrev records24644_24648 : List Blob :=
  records24644_24646 ++ records24646_24648
theorem aligned24644_24648 :
    AlignedValid 12 4 missing24644_24648 records24644_24648 :=
  aligned24644_24646.append aligned24646_24648

def missing24640_24648 : List (BitVec (edgeCount 12)) :=
  missing24640_24644 ++ missing24644_24648
abbrev records24640_24648 : List Blob :=
  records24640_24644 ++ records24644_24648
theorem aligned24640_24648 :
    AlignedValid 12 4 missing24640_24648 records24640_24648 :=
  aligned24640_24644.append aligned24644_24648

def missing24648_24649 : List (BitVec (edgeCount 12)) :=
  [missing24648]
abbrev records24648_24649 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24648]
theorem aligned24648_24649 :
    AlignedValid 12 4 missing24648_24649 records24648_24649 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24648
    maskCheck24648 AlignedValid.nil

def missing24649_24650 : List (BitVec (edgeCount 12)) :=
  [missing24649]
abbrev records24649_24650 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24649]
theorem aligned24649_24650 :
    AlignedValid 12 4 missing24649_24650 records24649_24650 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24649
    maskCheck24649 AlignedValid.nil

def missing24648_24650 : List (BitVec (edgeCount 12)) :=
  missing24648_24649 ++ missing24649_24650
abbrev records24648_24650 : List Blob :=
  records24648_24649 ++ records24649_24650
theorem aligned24648_24650 :
    AlignedValid 12 4 missing24648_24650 records24648_24650 :=
  aligned24648_24649.append aligned24649_24650

def missing24650_24651 : List (BitVec (edgeCount 12)) :=
  [missing24650]
abbrev records24650_24651 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24650]
theorem aligned24650_24651 :
    AlignedValid 12 4 missing24650_24651 records24650_24651 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24650
    maskCheck24650 AlignedValid.nil

def missing24651_24652 : List (BitVec (edgeCount 12)) :=
  [missing24651]
abbrev records24651_24652 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24651]
theorem aligned24651_24652 :
    AlignedValid 12 4 missing24651_24652 records24651_24652 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24651
    maskCheck24651 AlignedValid.nil

def missing24650_24652 : List (BitVec (edgeCount 12)) :=
  missing24650_24651 ++ missing24651_24652
abbrev records24650_24652 : List Blob :=
  records24650_24651 ++ records24651_24652
theorem aligned24650_24652 :
    AlignedValid 12 4 missing24650_24652 records24650_24652 :=
  aligned24650_24651.append aligned24651_24652

def missing24648_24652 : List (BitVec (edgeCount 12)) :=
  missing24648_24650 ++ missing24650_24652
abbrev records24648_24652 : List Blob :=
  records24648_24650 ++ records24650_24652
theorem aligned24648_24652 :
    AlignedValid 12 4 missing24648_24652 records24648_24652 :=
  aligned24648_24650.append aligned24650_24652

def missing24652_24653 : List (BitVec (edgeCount 12)) :=
  [missing24652]
abbrev records24652_24653 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24652]
theorem aligned24652_24653 :
    AlignedValid 12 4 missing24652_24653 records24652_24653 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24652
    maskCheck24652 AlignedValid.nil

def missing24653_24654 : List (BitVec (edgeCount 12)) :=
  [missing24653]
abbrev records24653_24654 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24653]
theorem aligned24653_24654 :
    AlignedValid 12 4 missing24653_24654 records24653_24654 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24653
    maskCheck24653 AlignedValid.nil

def missing24652_24654 : List (BitVec (edgeCount 12)) :=
  missing24652_24653 ++ missing24653_24654
abbrev records24652_24654 : List Blob :=
  records24652_24653 ++ records24653_24654
theorem aligned24652_24654 :
    AlignedValid 12 4 missing24652_24654 records24652_24654 :=
  aligned24652_24653.append aligned24653_24654

def missing24654_24655 : List (BitVec (edgeCount 12)) :=
  [missing24654]
abbrev records24654_24655 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24654]
theorem aligned24654_24655 :
    AlignedValid 12 4 missing24654_24655 records24654_24655 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24654
    maskCheck24654 AlignedValid.nil

def missing24655_24656 : List (BitVec (edgeCount 12)) :=
  [missing24655]
abbrev records24655_24656 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24655]
theorem aligned24655_24656 :
    AlignedValid 12 4 missing24655_24656 records24655_24656 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24655
    maskCheck24655 AlignedValid.nil

def missing24654_24656 : List (BitVec (edgeCount 12)) :=
  missing24654_24655 ++ missing24655_24656
abbrev records24654_24656 : List Blob :=
  records24654_24655 ++ records24655_24656
theorem aligned24654_24656 :
    AlignedValid 12 4 missing24654_24656 records24654_24656 :=
  aligned24654_24655.append aligned24655_24656

def missing24652_24656 : List (BitVec (edgeCount 12)) :=
  missing24652_24654 ++ missing24654_24656
abbrev records24652_24656 : List Blob :=
  records24652_24654 ++ records24654_24656
theorem aligned24652_24656 :
    AlignedValid 12 4 missing24652_24656 records24652_24656 :=
  aligned24652_24654.append aligned24654_24656

def missing24648_24656 : List (BitVec (edgeCount 12)) :=
  missing24648_24652 ++ missing24652_24656
abbrev records24648_24656 : List Blob :=
  records24648_24652 ++ records24652_24656
theorem aligned24648_24656 :
    AlignedValid 12 4 missing24648_24656 records24648_24656 :=
  aligned24648_24652.append aligned24652_24656

def missing24640_24656 : List (BitVec (edgeCount 12)) :=
  missing24640_24648 ++ missing24648_24656
abbrev records24640_24656 : List Blob :=
  records24640_24648 ++ records24648_24656
theorem aligned24640_24656 :
    AlignedValid 12 4 missing24640_24656 records24640_24656 :=
  aligned24640_24648.append aligned24648_24656

def missing24656_24657 : List (BitVec (edgeCount 12)) :=
  [missing24656]
abbrev records24656_24657 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24656]
theorem aligned24656_24657 :
    AlignedValid 12 4 missing24656_24657 records24656_24657 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24656
    maskCheck24656 AlignedValid.nil

def missing24657_24658 : List (BitVec (edgeCount 12)) :=
  [missing24657]
abbrev records24657_24658 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24657]
theorem aligned24657_24658 :
    AlignedValid 12 4 missing24657_24658 records24657_24658 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24657
    maskCheck24657 AlignedValid.nil

def missing24656_24658 : List (BitVec (edgeCount 12)) :=
  missing24656_24657 ++ missing24657_24658
abbrev records24656_24658 : List Blob :=
  records24656_24657 ++ records24657_24658
theorem aligned24656_24658 :
    AlignedValid 12 4 missing24656_24658 records24656_24658 :=
  aligned24656_24657.append aligned24657_24658

def missing24658_24659 : List (BitVec (edgeCount 12)) :=
  [missing24658]
abbrev records24658_24659 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24658]
theorem aligned24658_24659 :
    AlignedValid 12 4 missing24658_24659 records24658_24659 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24658
    maskCheck24658 AlignedValid.nil

def missing24659_24660 : List (BitVec (edgeCount 12)) :=
  [missing24659]
abbrev records24659_24660 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24659]
theorem aligned24659_24660 :
    AlignedValid 12 4 missing24659_24660 records24659_24660 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24659
    maskCheck24659 AlignedValid.nil

def missing24658_24660 : List (BitVec (edgeCount 12)) :=
  missing24658_24659 ++ missing24659_24660
abbrev records24658_24660 : List Blob :=
  records24658_24659 ++ records24659_24660
theorem aligned24658_24660 :
    AlignedValid 12 4 missing24658_24660 records24658_24660 :=
  aligned24658_24659.append aligned24659_24660

def missing24656_24660 : List (BitVec (edgeCount 12)) :=
  missing24656_24658 ++ missing24658_24660
abbrev records24656_24660 : List Blob :=
  records24656_24658 ++ records24658_24660
theorem aligned24656_24660 :
    AlignedValid 12 4 missing24656_24660 records24656_24660 :=
  aligned24656_24658.append aligned24658_24660

def missing24660_24661 : List (BitVec (edgeCount 12)) :=
  [missing24660]
abbrev records24660_24661 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24660]
theorem aligned24660_24661 :
    AlignedValid 12 4 missing24660_24661 records24660_24661 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24660
    maskCheck24660 AlignedValid.nil

def missing24661_24662 : List (BitVec (edgeCount 12)) :=
  [missing24661]
abbrev records24661_24662 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24661]
theorem aligned24661_24662 :
    AlignedValid 12 4 missing24661_24662 records24661_24662 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24661
    maskCheck24661 AlignedValid.nil

def missing24660_24662 : List (BitVec (edgeCount 12)) :=
  missing24660_24661 ++ missing24661_24662
abbrev records24660_24662 : List Blob :=
  records24660_24661 ++ records24661_24662
theorem aligned24660_24662 :
    AlignedValid 12 4 missing24660_24662 records24660_24662 :=
  aligned24660_24661.append aligned24661_24662

def missing24662_24663 : List (BitVec (edgeCount 12)) :=
  [missing24662]
abbrev records24662_24663 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24662]
theorem aligned24662_24663 :
    AlignedValid 12 4 missing24662_24663 records24662_24663 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24662
    maskCheck24662 AlignedValid.nil

def missing24663_24664 : List (BitVec (edgeCount 12)) :=
  [missing24663]
abbrev records24663_24664 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24663]
theorem aligned24663_24664 :
    AlignedValid 12 4 missing24663_24664 records24663_24664 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24663
    maskCheck24663 AlignedValid.nil

def missing24662_24664 : List (BitVec (edgeCount 12)) :=
  missing24662_24663 ++ missing24663_24664
abbrev records24662_24664 : List Blob :=
  records24662_24663 ++ records24663_24664
theorem aligned24662_24664 :
    AlignedValid 12 4 missing24662_24664 records24662_24664 :=
  aligned24662_24663.append aligned24663_24664

def missing24660_24664 : List (BitVec (edgeCount 12)) :=
  missing24660_24662 ++ missing24662_24664
abbrev records24660_24664 : List Blob :=
  records24660_24662 ++ records24662_24664
theorem aligned24660_24664 :
    AlignedValid 12 4 missing24660_24664 records24660_24664 :=
  aligned24660_24662.append aligned24662_24664

def missing24656_24664 : List (BitVec (edgeCount 12)) :=
  missing24656_24660 ++ missing24660_24664
abbrev records24656_24664 : List Blob :=
  records24656_24660 ++ records24660_24664
theorem aligned24656_24664 :
    AlignedValid 12 4 missing24656_24664 records24656_24664 :=
  aligned24656_24660.append aligned24660_24664

def missing24664_24665 : List (BitVec (edgeCount 12)) :=
  [missing24664]
abbrev records24664_24665 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24664]
theorem aligned24664_24665 :
    AlignedValid 12 4 missing24664_24665 records24664_24665 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24664
    maskCheck24664 AlignedValid.nil

def missing24665_24666 : List (BitVec (edgeCount 12)) :=
  [missing24665]
abbrev records24665_24666 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24665]
theorem aligned24665_24666 :
    AlignedValid 12 4 missing24665_24666 records24665_24666 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24665
    maskCheck24665 AlignedValid.nil

def missing24664_24666 : List (BitVec (edgeCount 12)) :=
  missing24664_24665 ++ missing24665_24666
abbrev records24664_24666 : List Blob :=
  records24664_24665 ++ records24665_24666
theorem aligned24664_24666 :
    AlignedValid 12 4 missing24664_24666 records24664_24666 :=
  aligned24664_24665.append aligned24665_24666

def missing24666_24667 : List (BitVec (edgeCount 12)) :=
  [missing24666]
abbrev records24666_24667 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24666]
theorem aligned24666_24667 :
    AlignedValid 12 4 missing24666_24667 records24666_24667 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24666
    maskCheck24666 AlignedValid.nil

def missing24667_24668 : List (BitVec (edgeCount 12)) :=
  [missing24667]
abbrev records24667_24668 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24667]
theorem aligned24667_24668 :
    AlignedValid 12 4 missing24667_24668 records24667_24668 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24667
    maskCheck24667 AlignedValid.nil

def missing24666_24668 : List (BitVec (edgeCount 12)) :=
  missing24666_24667 ++ missing24667_24668
abbrev records24666_24668 : List Blob :=
  records24666_24667 ++ records24667_24668
theorem aligned24666_24668 :
    AlignedValid 12 4 missing24666_24668 records24666_24668 :=
  aligned24666_24667.append aligned24667_24668

def missing24664_24668 : List (BitVec (edgeCount 12)) :=
  missing24664_24666 ++ missing24666_24668
abbrev records24664_24668 : List Blob :=
  records24664_24666 ++ records24666_24668
theorem aligned24664_24668 :
    AlignedValid 12 4 missing24664_24668 records24664_24668 :=
  aligned24664_24666.append aligned24666_24668

def missing24668_24669 : List (BitVec (edgeCount 12)) :=
  [missing24668]
abbrev records24668_24669 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24668]
theorem aligned24668_24669 :
    AlignedValid 12 4 missing24668_24669 records24668_24669 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24668
    maskCheck24668 AlignedValid.nil

def missing24669_24670 : List (BitVec (edgeCount 12)) :=
  [missing24669]
abbrev records24669_24670 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24669]
theorem aligned24669_24670 :
    AlignedValid 12 4 missing24669_24670 records24669_24670 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24669
    maskCheck24669 AlignedValid.nil

def missing24668_24670 : List (BitVec (edgeCount 12)) :=
  missing24668_24669 ++ missing24669_24670
abbrev records24668_24670 : List Blob :=
  records24668_24669 ++ records24669_24670
theorem aligned24668_24670 :
    AlignedValid 12 4 missing24668_24670 records24668_24670 :=
  aligned24668_24669.append aligned24669_24670

def missing24670_24671 : List (BitVec (edgeCount 12)) :=
  [missing24670]
abbrev records24670_24671 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24670]
theorem aligned24670_24671 :
    AlignedValid 12 4 missing24670_24671 records24670_24671 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24670
    maskCheck24670 AlignedValid.nil

def missing24671_24672 : List (BitVec (edgeCount 12)) :=
  [missing24671]
abbrev records24671_24672 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24671]
theorem aligned24671_24672 :
    AlignedValid 12 4 missing24671_24672 records24671_24672 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24671
    maskCheck24671 AlignedValid.nil

def missing24670_24672 : List (BitVec (edgeCount 12)) :=
  missing24670_24671 ++ missing24671_24672
abbrev records24670_24672 : List Blob :=
  records24670_24671 ++ records24671_24672
theorem aligned24670_24672 :
    AlignedValid 12 4 missing24670_24672 records24670_24672 :=
  aligned24670_24671.append aligned24671_24672

def missing24668_24672 : List (BitVec (edgeCount 12)) :=
  missing24668_24670 ++ missing24670_24672
abbrev records24668_24672 : List Blob :=
  records24668_24670 ++ records24670_24672
theorem aligned24668_24672 :
    AlignedValid 12 4 missing24668_24672 records24668_24672 :=
  aligned24668_24670.append aligned24670_24672

def missing24664_24672 : List (BitVec (edgeCount 12)) :=
  missing24664_24668 ++ missing24668_24672
abbrev records24664_24672 : List Blob :=
  records24664_24668 ++ records24668_24672
theorem aligned24664_24672 :
    AlignedValid 12 4 missing24664_24672 records24664_24672 :=
  aligned24664_24668.append aligned24668_24672

def missing24656_24672 : List (BitVec (edgeCount 12)) :=
  missing24656_24664 ++ missing24664_24672
abbrev records24656_24672 : List Blob :=
  records24656_24664 ++ records24664_24672
theorem aligned24656_24672 :
    AlignedValid 12 4 missing24656_24672 records24656_24672 :=
  aligned24656_24664.append aligned24664_24672

def missing24640_24672 : List (BitVec (edgeCount 12)) :=
  missing24640_24656 ++ missing24656_24672
abbrev records24640_24672 : List Blob :=
  records24640_24656 ++ records24656_24672
theorem aligned24640_24672 :
    AlignedValid 12 4 missing24640_24672 records24640_24672 :=
  aligned24640_24656.append aligned24656_24672

def missing24672_24673 : List (BitVec (edgeCount 12)) :=
  [missing24672]
abbrev records24672_24673 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24672]
theorem aligned24672_24673 :
    AlignedValid 12 4 missing24672_24673 records24672_24673 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24672
    maskCheck24672 AlignedValid.nil

def missing24673_24674 : List (BitVec (edgeCount 12)) :=
  [missing24673]
abbrev records24673_24674 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24673]
theorem aligned24673_24674 :
    AlignedValid 12 4 missing24673_24674 records24673_24674 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24673
    maskCheck24673 AlignedValid.nil

def missing24672_24674 : List (BitVec (edgeCount 12)) :=
  missing24672_24673 ++ missing24673_24674
abbrev records24672_24674 : List Blob :=
  records24672_24673 ++ records24673_24674
theorem aligned24672_24674 :
    AlignedValid 12 4 missing24672_24674 records24672_24674 :=
  aligned24672_24673.append aligned24673_24674

def missing24674_24675 : List (BitVec (edgeCount 12)) :=
  [missing24674]
abbrev records24674_24675 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24674]
theorem aligned24674_24675 :
    AlignedValid 12 4 missing24674_24675 records24674_24675 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24674
    maskCheck24674 AlignedValid.nil

def missing24675_24676 : List (BitVec (edgeCount 12)) :=
  [missing24675]
abbrev records24675_24676 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24675]
theorem aligned24675_24676 :
    AlignedValid 12 4 missing24675_24676 records24675_24676 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24675
    maskCheck24675 AlignedValid.nil

def missing24674_24676 : List (BitVec (edgeCount 12)) :=
  missing24674_24675 ++ missing24675_24676
abbrev records24674_24676 : List Blob :=
  records24674_24675 ++ records24675_24676
theorem aligned24674_24676 :
    AlignedValid 12 4 missing24674_24676 records24674_24676 :=
  aligned24674_24675.append aligned24675_24676

def missing24672_24676 : List (BitVec (edgeCount 12)) :=
  missing24672_24674 ++ missing24674_24676
abbrev records24672_24676 : List Blob :=
  records24672_24674 ++ records24674_24676
theorem aligned24672_24676 :
    AlignedValid 12 4 missing24672_24676 records24672_24676 :=
  aligned24672_24674.append aligned24674_24676

def missing24676_24677 : List (BitVec (edgeCount 12)) :=
  [missing24676]
abbrev records24676_24677 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24676]
theorem aligned24676_24677 :
    AlignedValid 12 4 missing24676_24677 records24676_24677 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24676
    maskCheck24676 AlignedValid.nil

def missing24677_24678 : List (BitVec (edgeCount 12)) :=
  [missing24677]
abbrev records24677_24678 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24677]
theorem aligned24677_24678 :
    AlignedValid 12 4 missing24677_24678 records24677_24678 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24677
    maskCheck24677 AlignedValid.nil

def missing24676_24678 : List (BitVec (edgeCount 12)) :=
  missing24676_24677 ++ missing24677_24678
abbrev records24676_24678 : List Blob :=
  records24676_24677 ++ records24677_24678
theorem aligned24676_24678 :
    AlignedValid 12 4 missing24676_24678 records24676_24678 :=
  aligned24676_24677.append aligned24677_24678

def missing24678_24679 : List (BitVec (edgeCount 12)) :=
  [missing24678]
abbrev records24678_24679 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24678]
theorem aligned24678_24679 :
    AlignedValid 12 4 missing24678_24679 records24678_24679 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24678
    maskCheck24678 AlignedValid.nil

def missing24679_24680 : List (BitVec (edgeCount 12)) :=
  [missing24679]
abbrev records24679_24680 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24679]
theorem aligned24679_24680 :
    AlignedValid 12 4 missing24679_24680 records24679_24680 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24679
    maskCheck24679 AlignedValid.nil

def missing24678_24680 : List (BitVec (edgeCount 12)) :=
  missing24678_24679 ++ missing24679_24680
abbrev records24678_24680 : List Blob :=
  records24678_24679 ++ records24679_24680
theorem aligned24678_24680 :
    AlignedValid 12 4 missing24678_24680 records24678_24680 :=
  aligned24678_24679.append aligned24679_24680

def missing24676_24680 : List (BitVec (edgeCount 12)) :=
  missing24676_24678 ++ missing24678_24680
abbrev records24676_24680 : List Blob :=
  records24676_24678 ++ records24678_24680
theorem aligned24676_24680 :
    AlignedValid 12 4 missing24676_24680 records24676_24680 :=
  aligned24676_24678.append aligned24678_24680

def missing24672_24680 : List (BitVec (edgeCount 12)) :=
  missing24672_24676 ++ missing24676_24680
abbrev records24672_24680 : List Blob :=
  records24672_24676 ++ records24676_24680
theorem aligned24672_24680 :
    AlignedValid 12 4 missing24672_24680 records24672_24680 :=
  aligned24672_24676.append aligned24676_24680

def missing24680_24681 : List (BitVec (edgeCount 12)) :=
  [missing24680]
abbrev records24680_24681 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24680]
theorem aligned24680_24681 :
    AlignedValid 12 4 missing24680_24681 records24680_24681 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24680
    maskCheck24680 AlignedValid.nil

def missing24681_24682 : List (BitVec (edgeCount 12)) :=
  [missing24681]
abbrev records24681_24682 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24681]
theorem aligned24681_24682 :
    AlignedValid 12 4 missing24681_24682 records24681_24682 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24681
    maskCheck24681 AlignedValid.nil

def missing24680_24682 : List (BitVec (edgeCount 12)) :=
  missing24680_24681 ++ missing24681_24682
abbrev records24680_24682 : List Blob :=
  records24680_24681 ++ records24681_24682
theorem aligned24680_24682 :
    AlignedValid 12 4 missing24680_24682 records24680_24682 :=
  aligned24680_24681.append aligned24681_24682

def missing24682_24683 : List (BitVec (edgeCount 12)) :=
  [missing24682]
abbrev records24682_24683 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24682]
theorem aligned24682_24683 :
    AlignedValid 12 4 missing24682_24683 records24682_24683 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24682
    maskCheck24682 AlignedValid.nil

def missing24683_24684 : List (BitVec (edgeCount 12)) :=
  [missing24683]
abbrev records24683_24684 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24683]
theorem aligned24683_24684 :
    AlignedValid 12 4 missing24683_24684 records24683_24684 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24683
    maskCheck24683 AlignedValid.nil

def missing24682_24684 : List (BitVec (edgeCount 12)) :=
  missing24682_24683 ++ missing24683_24684
abbrev records24682_24684 : List Blob :=
  records24682_24683 ++ records24683_24684
theorem aligned24682_24684 :
    AlignedValid 12 4 missing24682_24684 records24682_24684 :=
  aligned24682_24683.append aligned24683_24684

def missing24680_24684 : List (BitVec (edgeCount 12)) :=
  missing24680_24682 ++ missing24682_24684
abbrev records24680_24684 : List Blob :=
  records24680_24682 ++ records24682_24684
theorem aligned24680_24684 :
    AlignedValid 12 4 missing24680_24684 records24680_24684 :=
  aligned24680_24682.append aligned24682_24684

def missing24684_24685 : List (BitVec (edgeCount 12)) :=
  [missing24684]
abbrev records24684_24685 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24684]
theorem aligned24684_24685 :
    AlignedValid 12 4 missing24684_24685 records24684_24685 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24684
    maskCheck24684 AlignedValid.nil

def missing24685_24686 : List (BitVec (edgeCount 12)) :=
  [missing24685]
abbrev records24685_24686 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24685]
theorem aligned24685_24686 :
    AlignedValid 12 4 missing24685_24686 records24685_24686 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24685
    maskCheck24685 AlignedValid.nil

def missing24684_24686 : List (BitVec (edgeCount 12)) :=
  missing24684_24685 ++ missing24685_24686
abbrev records24684_24686 : List Blob :=
  records24684_24685 ++ records24685_24686
theorem aligned24684_24686 :
    AlignedValid 12 4 missing24684_24686 records24684_24686 :=
  aligned24684_24685.append aligned24685_24686

def missing24686_24687 : List (BitVec (edgeCount 12)) :=
  [missing24686]
abbrev records24686_24687 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24686]
theorem aligned24686_24687 :
    AlignedValid 12 4 missing24686_24687 records24686_24687 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24686
    maskCheck24686 AlignedValid.nil

def missing24687_24688 : List (BitVec (edgeCount 12)) :=
  [missing24687]
abbrev records24687_24688 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24687]
theorem aligned24687_24688 :
    AlignedValid 12 4 missing24687_24688 records24687_24688 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24687
    maskCheck24687 AlignedValid.nil

def missing24686_24688 : List (BitVec (edgeCount 12)) :=
  missing24686_24687 ++ missing24687_24688
abbrev records24686_24688 : List Blob :=
  records24686_24687 ++ records24687_24688
theorem aligned24686_24688 :
    AlignedValid 12 4 missing24686_24688 records24686_24688 :=
  aligned24686_24687.append aligned24687_24688

def missing24684_24688 : List (BitVec (edgeCount 12)) :=
  missing24684_24686 ++ missing24686_24688
abbrev records24684_24688 : List Blob :=
  records24684_24686 ++ records24686_24688
theorem aligned24684_24688 :
    AlignedValid 12 4 missing24684_24688 records24684_24688 :=
  aligned24684_24686.append aligned24686_24688

def missing24680_24688 : List (BitVec (edgeCount 12)) :=
  missing24680_24684 ++ missing24684_24688
abbrev records24680_24688 : List Blob :=
  records24680_24684 ++ records24684_24688
theorem aligned24680_24688 :
    AlignedValid 12 4 missing24680_24688 records24680_24688 :=
  aligned24680_24684.append aligned24684_24688

def missing24672_24688 : List (BitVec (edgeCount 12)) :=
  missing24672_24680 ++ missing24680_24688
abbrev records24672_24688 : List Blob :=
  records24672_24680 ++ records24680_24688
theorem aligned24672_24688 :
    AlignedValid 12 4 missing24672_24688 records24672_24688 :=
  aligned24672_24680.append aligned24680_24688

def missing24688_24689 : List (BitVec (edgeCount 12)) :=
  [missing24688]
abbrev records24688_24689 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24688]
theorem aligned24688_24689 :
    AlignedValid 12 4 missing24688_24689 records24688_24689 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24688
    maskCheck24688 AlignedValid.nil

def missing24689_24690 : List (BitVec (edgeCount 12)) :=
  [missing24689]
abbrev records24689_24690 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24689]
theorem aligned24689_24690 :
    AlignedValid 12 4 missing24689_24690 records24689_24690 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24689
    maskCheck24689 AlignedValid.nil

def missing24688_24690 : List (BitVec (edgeCount 12)) :=
  missing24688_24689 ++ missing24689_24690
abbrev records24688_24690 : List Blob :=
  records24688_24689 ++ records24689_24690
theorem aligned24688_24690 :
    AlignedValid 12 4 missing24688_24690 records24688_24690 :=
  aligned24688_24689.append aligned24689_24690

def missing24690_24691 : List (BitVec (edgeCount 12)) :=
  [missing24690]
abbrev records24690_24691 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24690]
theorem aligned24690_24691 :
    AlignedValid 12 4 missing24690_24691 records24690_24691 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24690
    maskCheck24690 AlignedValid.nil

def missing24691_24692 : List (BitVec (edgeCount 12)) :=
  [missing24691]
abbrev records24691_24692 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24691]
theorem aligned24691_24692 :
    AlignedValid 12 4 missing24691_24692 records24691_24692 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24691
    maskCheck24691 AlignedValid.nil

def missing24690_24692 : List (BitVec (edgeCount 12)) :=
  missing24690_24691 ++ missing24691_24692
abbrev records24690_24692 : List Blob :=
  records24690_24691 ++ records24691_24692
theorem aligned24690_24692 :
    AlignedValid 12 4 missing24690_24692 records24690_24692 :=
  aligned24690_24691.append aligned24691_24692

def missing24688_24692 : List (BitVec (edgeCount 12)) :=
  missing24688_24690 ++ missing24690_24692
abbrev records24688_24692 : List Blob :=
  records24688_24690 ++ records24690_24692
theorem aligned24688_24692 :
    AlignedValid 12 4 missing24688_24692 records24688_24692 :=
  aligned24688_24690.append aligned24690_24692

def missing24692_24693 : List (BitVec (edgeCount 12)) :=
  [missing24692]
abbrev records24692_24693 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24692]
theorem aligned24692_24693 :
    AlignedValid 12 4 missing24692_24693 records24692_24693 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24692
    maskCheck24692 AlignedValid.nil

def missing24693_24694 : List (BitVec (edgeCount 12)) :=
  [missing24693]
abbrev records24693_24694 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24693]
theorem aligned24693_24694 :
    AlignedValid 12 4 missing24693_24694 records24693_24694 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24693
    maskCheck24693 AlignedValid.nil

def missing24692_24694 : List (BitVec (edgeCount 12)) :=
  missing24692_24693 ++ missing24693_24694
abbrev records24692_24694 : List Blob :=
  records24692_24693 ++ records24693_24694
theorem aligned24692_24694 :
    AlignedValid 12 4 missing24692_24694 records24692_24694 :=
  aligned24692_24693.append aligned24693_24694

def missing24694_24695 : List (BitVec (edgeCount 12)) :=
  [missing24694]
abbrev records24694_24695 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24694]
theorem aligned24694_24695 :
    AlignedValid 12 4 missing24694_24695 records24694_24695 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24694
    maskCheck24694 AlignedValid.nil

def missing24695_24696 : List (BitVec (edgeCount 12)) :=
  [missing24695]
abbrev records24695_24696 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24695]
theorem aligned24695_24696 :
    AlignedValid 12 4 missing24695_24696 records24695_24696 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24695
    maskCheck24695 AlignedValid.nil

def missing24694_24696 : List (BitVec (edgeCount 12)) :=
  missing24694_24695 ++ missing24695_24696
abbrev records24694_24696 : List Blob :=
  records24694_24695 ++ records24695_24696
theorem aligned24694_24696 :
    AlignedValid 12 4 missing24694_24696 records24694_24696 :=
  aligned24694_24695.append aligned24695_24696

def missing24692_24696 : List (BitVec (edgeCount 12)) :=
  missing24692_24694 ++ missing24694_24696
abbrev records24692_24696 : List Blob :=
  records24692_24694 ++ records24694_24696
theorem aligned24692_24696 :
    AlignedValid 12 4 missing24692_24696 records24692_24696 :=
  aligned24692_24694.append aligned24694_24696

def missing24688_24696 : List (BitVec (edgeCount 12)) :=
  missing24688_24692 ++ missing24692_24696
abbrev records24688_24696 : List Blob :=
  records24688_24692 ++ records24692_24696
theorem aligned24688_24696 :
    AlignedValid 12 4 missing24688_24696 records24688_24696 :=
  aligned24688_24692.append aligned24692_24696

def missing24696_24697 : List (BitVec (edgeCount 12)) :=
  [missing24696]
abbrev records24696_24697 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24696]
theorem aligned24696_24697 :
    AlignedValid 12 4 missing24696_24697 records24696_24697 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24696
    maskCheck24696 AlignedValid.nil

def missing24697_24698 : List (BitVec (edgeCount 12)) :=
  [missing24697]
abbrev records24697_24698 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24697]
theorem aligned24697_24698 :
    AlignedValid 12 4 missing24697_24698 records24697_24698 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24697
    maskCheck24697 AlignedValid.nil

def missing24696_24698 : List (BitVec (edgeCount 12)) :=
  missing24696_24697 ++ missing24697_24698
abbrev records24696_24698 : List Blob :=
  records24696_24697 ++ records24697_24698
theorem aligned24696_24698 :
    AlignedValid 12 4 missing24696_24698 records24696_24698 :=
  aligned24696_24697.append aligned24697_24698

def missing24698_24699 : List (BitVec (edgeCount 12)) :=
  [missing24698]
abbrev records24698_24699 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24698]
theorem aligned24698_24699 :
    AlignedValid 12 4 missing24698_24699 records24698_24699 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24698
    maskCheck24698 AlignedValid.nil

def missing24699_24700 : List (BitVec (edgeCount 12)) :=
  [missing24699]
abbrev records24699_24700 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24699]
theorem aligned24699_24700 :
    AlignedValid 12 4 missing24699_24700 records24699_24700 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24699
    maskCheck24699 AlignedValid.nil

def missing24698_24700 : List (BitVec (edgeCount 12)) :=
  missing24698_24699 ++ missing24699_24700
abbrev records24698_24700 : List Blob :=
  records24698_24699 ++ records24699_24700
theorem aligned24698_24700 :
    AlignedValid 12 4 missing24698_24700 records24698_24700 :=
  aligned24698_24699.append aligned24699_24700

def missing24696_24700 : List (BitVec (edgeCount 12)) :=
  missing24696_24698 ++ missing24698_24700
abbrev records24696_24700 : List Blob :=
  records24696_24698 ++ records24698_24700
theorem aligned24696_24700 :
    AlignedValid 12 4 missing24696_24700 records24696_24700 :=
  aligned24696_24698.append aligned24698_24700

def missing24700_24701 : List (BitVec (edgeCount 12)) :=
  [missing24700]
abbrev records24700_24701 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24700]
theorem aligned24700_24701 :
    AlignedValid 12 4 missing24700_24701 records24700_24701 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24700
    maskCheck24700 AlignedValid.nil

def missing24701_24702 : List (BitVec (edgeCount 12)) :=
  [missing24701]
abbrev records24701_24702 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24701]
theorem aligned24701_24702 :
    AlignedValid 12 4 missing24701_24702 records24701_24702 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24701
    maskCheck24701 AlignedValid.nil

def missing24700_24702 : List (BitVec (edgeCount 12)) :=
  missing24700_24701 ++ missing24701_24702
abbrev records24700_24702 : List Blob :=
  records24700_24701 ++ records24701_24702
theorem aligned24700_24702 :
    AlignedValid 12 4 missing24700_24702 records24700_24702 :=
  aligned24700_24701.append aligned24701_24702

def missing24702_24703 : List (BitVec (edgeCount 12)) :=
  [missing24702]
abbrev records24702_24703 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24702]
theorem aligned24702_24703 :
    AlignedValid 12 4 missing24702_24703 records24702_24703 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24702
    maskCheck24702 AlignedValid.nil

def missing24703_24704 : List (BitVec (edgeCount 12)) :=
  [missing24703]
abbrev records24703_24704 : List Blob :=
  [StrongPackedBucketN12A4Shard192.record24703]
theorem aligned24703_24704 :
    AlignedValid 12 4 missing24703_24704 records24703_24704 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard192.check24703
    maskCheck24703 AlignedValid.nil

def missing24702_24704 : List (BitVec (edgeCount 12)) :=
  missing24702_24703 ++ missing24703_24704
abbrev records24702_24704 : List Blob :=
  records24702_24703 ++ records24703_24704
theorem aligned24702_24704 :
    AlignedValid 12 4 missing24702_24704 records24702_24704 :=
  aligned24702_24703.append aligned24703_24704

def missing24700_24704 : List (BitVec (edgeCount 12)) :=
  missing24700_24702 ++ missing24702_24704
abbrev records24700_24704 : List Blob :=
  records24700_24702 ++ records24702_24704
theorem aligned24700_24704 :
    AlignedValid 12 4 missing24700_24704 records24700_24704 :=
  aligned24700_24702.append aligned24702_24704

def missing24696_24704 : List (BitVec (edgeCount 12)) :=
  missing24696_24700 ++ missing24700_24704
abbrev records24696_24704 : List Blob :=
  records24696_24700 ++ records24700_24704
theorem aligned24696_24704 :
    AlignedValid 12 4 missing24696_24704 records24696_24704 :=
  aligned24696_24700.append aligned24700_24704

def missing24688_24704 : List (BitVec (edgeCount 12)) :=
  missing24688_24696 ++ missing24696_24704
abbrev records24688_24704 : List Blob :=
  records24688_24696 ++ records24696_24704
theorem aligned24688_24704 :
    AlignedValid 12 4 missing24688_24704 records24688_24704 :=
  aligned24688_24696.append aligned24696_24704

def missing24672_24704 : List (BitVec (edgeCount 12)) :=
  missing24672_24688 ++ missing24688_24704
abbrev records24672_24704 : List Blob :=
  records24672_24688 ++ records24688_24704
theorem aligned24672_24704 :
    AlignedValid 12 4 missing24672_24704 records24672_24704 :=
  aligned24672_24688.append aligned24688_24704

def missing24640_24704 : List (BitVec (edgeCount 12)) :=
  missing24640_24672 ++ missing24672_24704
abbrev records24640_24704 : List Blob :=
  records24640_24672 ++ records24672_24704
theorem aligned24640_24704 :
    AlignedValid 12 4 missing24640_24704 records24640_24704 :=
  aligned24640_24672.append aligned24672_24704

def missing24576_24704 : List (BitVec (edgeCount 12)) :=
  missing24576_24640 ++ missing24640_24704
abbrev records24576_24704 : List Blob :=
  records24576_24640 ++ records24640_24704
theorem aligned24576_24704 :
    AlignedValid 12 4 missing24576_24704 records24576_24704 :=
  aligned24576_24640.append aligned24640_24704

abbrev missing : List (BitVec (edgeCount 12)) := missing24576_24704
abbrev records : List Blob := records24576_24704
theorem aligned : AlignedValid 12 4 missing records := aligned24576_24704

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard192
