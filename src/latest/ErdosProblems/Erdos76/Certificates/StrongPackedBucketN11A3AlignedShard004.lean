/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A3Shard004

/-! Decode-only alignment checks for a=3, records 512--639. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN11A3AlignedShard004

open PackedBucketCertificate

def missing512 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 6685374833229824
theorem maskCheck512 :
    checkMaskFor missing512 StrongPackedBucketN11A3Shard004.record512 = true := by
  decide

def missing513 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 8761252786470912
theorem maskCheck513 :
    checkMaskFor missing513 StrongPackedBucketN11A3Shard004.record513 = true := by
  decide

def missing514 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 8866805902737408
theorem maskCheck514 :
    checkMaskFor missing514 StrongPackedBucketN11A3Shard004.record514 = true := by
  decide

def missing515 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 10098258925846528
theorem maskCheck515 :
    checkMaskFor missing515 StrongPackedBucketN11A3Shard004.record515 = true := by
  decide

def missing516 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 11083421344333824
theorem maskCheck516 :
    checkMaskFor missing516 StrongPackedBucketN11A3Shard004.record516 = true := by
  decide

def missing517 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 11188974460600320
theorem maskCheck517 :
    checkMaskFor missing517 StrongPackedBucketN11A3Shard004.record517 = true := by
  decide

def missing518 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 13300036785930240
theorem maskCheck518 :
    checkMaskFor missing518 StrongPackedBucketN11A3Shard004.record518 = true := by
  decide

def missing519 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 14038908599795712
theorem maskCheck519 :
    checkMaskFor missing519 StrongPackedBucketN11A3Shard004.record519 = true := by
  decide

def missing520 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 14461121064861696
theorem maskCheck520 :
    checkMaskFor missing520 StrongPackedBucketN11A3Shard004.record520 = true := by
  decide

def missing521 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 14566674181128192
theorem maskCheck521 :
    checkMaskFor missing521 StrongPackedBucketN11A3Shard004.record521 = true := by
  decide

def missing522 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 19105458180587520
theorem maskCheck522 :
    checkMaskFor missing522 StrongPackedBucketN11A3Shard004.record522 = true := by
  decide

def missing523 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 20090620599074816
theorem maskCheck523 :
    checkMaskFor missing523 StrongPackedBucketN11A3Shard004.record523 = true := by
  decide

def missing524 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 20160989343252480
theorem maskCheck524 :
    checkMaskFor missing524 StrongPackedBucketN11A3Shard004.record524 = true := by
  decide

def missing525 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 22272051668582400
theorem maskCheck525 :
    checkMaskFor missing525 StrongPackedBucketN11A3Shard004.record525 = true := by
  decide

def missing526 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 23046107854536704
theorem maskCheck526 :
    checkMaskFor missing526 StrongPackedBucketN11A3Shard004.record526 = true := by
  decide

def missing527 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 23538689063780352
theorem maskCheck527 :
    checkMaskFor missing527 StrongPackedBucketN11A3Shard004.record527 = true := by
  decide

def missing528 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 27549707481907200
theorem maskCheck528 :
    checkMaskFor missing528 StrongPackedBucketN11A3Shard004.record528 = true := by
  decide

def missing529 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 27971919946973184
theorem maskCheck529 :
    checkMaskFor missing529 StrongPackedBucketN11A3Shard004.record529 = true := by
  decide

def missing530 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 31771832132567040
theorem maskCheck530 :
    checkMaskFor missing530 StrongPackedBucketN11A3Shard004.record530 = true := by
  decide

def missing531 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 2217440614285312
theorem maskCheck531 :
    checkMaskFor missing531 StrongPackedBucketN11A3Shard004.record531 = true := by
  decide

def missing532 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 4187765451259904
theorem maskCheck532 :
    checkMaskFor missing532 StrongPackedBucketN11A3Shard004.record532 = true := by
  decide

def missing533 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 4398871683792896
theorem maskCheck533 :
    checkMaskFor missing533 StrongPackedBucketN11A3Shard004.record533 = true := by
  decide

def missing534 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 5595140334813184
theorem maskCheck534 :
    checkMaskFor missing534 StrongPackedBucketN11A3Shard004.record534 = true := by
  decide

def missing535 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 6439565264945152
theorem maskCheck535 :
    checkMaskFor missing535 StrongPackedBucketN11A3Shard004.record535 = true := by
  decide

def missing536 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 6650671497478144
theorem maskCheck536 :
    checkMaskFor missing536 StrongPackedBucketN11A3Shard004.record536 = true := by
  decide

def missing537 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 8550627590275072
theorem maskCheck537 :
    checkMaskFor missing537 StrongPackedBucketN11A3Shard004.record537 = true := by
  decide

def missing538 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 8620996334452736
theorem maskCheck538 :
    checkMaskFor missing538 StrongPackedBucketN11A3Shard004.record538 = true := by
  decide

def missing539 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 14039389636132864
theorem maskCheck539 :
    checkMaskFor missing539 StrongPackedBucketN11A3Shard004.record539 = true := by
  decide

def missing540 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 14320864612843520
theorem maskCheck540 :
    checkMaskFor missing540 StrongPackedBucketN11A3Shard004.record540 = true := by
  decide

def missing541 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 15306027031330816
theorem maskCheck541 :
    checkMaskFor missing541 StrongPackedBucketN11A3Shard004.record541 = true := by
  decide

def missing542 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 19105939216924672
theorem maskCheck542 :
    checkMaskFor missing542 StrongPackedBucketN11A3Shard004.record542 = true := by
  decide

def missing543 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 19950364147056640
theorem maskCheck543 :
    checkMaskFor missing543 StrongPackedBucketN11A3Shard004.record543 = true := by
  decide

def missing544 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 20161470379589632
theorem maskCheck544 :
    checkMaskFor missing544 StrongPackedBucketN11A3Shard004.record544 = true := by
  decide

def missing545 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 22061426472386560
theorem maskCheck545 :
    checkMaskFor missing545 StrongPackedBucketN11A3Shard004.record545 = true := by
  decide

def missing546 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 22131795216564224
theorem maskCheck546 :
    checkMaskFor missing546 StrongPackedBucketN11A3Shard004.record546 = true := by
  decide

def missing547 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 22378085821186048
theorem maskCheck547 :
    checkMaskFor missing547 StrongPackedBucketN11A3Shard004.record547 = true := by
  decide

def missing548 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 23046588890873856
theorem maskCheck548 :
    checkMaskFor missing548 StrongPackedBucketN11A3Shard004.record548 = true := by
  decide

def missing549 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 23328063867584512
theorem maskCheck549 :
    checkMaskFor missing549 StrongPackedBucketN11A3Shard004.record549 = true := by
  decide

def missing550 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 23539170100117504
theorem maskCheck550 :
    checkMaskFor missing550 StrongPackedBucketN11A3Shard004.record550 = true := by
  decide

def missing551 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 24313226286071808
theorem maskCheck551 :
    checkMaskFor missing551 StrongPackedBucketN11A3Shard004.record551 = true := by
  decide

def missing552 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 24383595030249472
theorem maskCheck552 :
    checkMaskFor missing552 StrongPackedBucketN11A3Shard004.record552 = true := by
  decide

def missing553 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 26494657355579392
theorem maskCheck553 :
    checkMaskFor missing553 StrongPackedBucketN11A3Shard004.record553 = true := by
  decide

def missing554 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 31772313168904192
theorem maskCheck554 :
    checkMaskFor missing554 StrongPackedBucketN11A3Shard004.record554 = true := by
  decide

def missing555 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 32194525633970176
theorem maskCheck555 :
    checkMaskFor missing555 StrongPackedBucketN11A3Shard004.record555 = true := by
  decide

def missing556 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 2225480793063424
theorem maskCheck556 :
    checkMaskFor missing556 StrongPackedBucketN11A3Shard004.record556 = true := by
  decide

def missing557 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 4406911862571008
theorem maskCheck557 :
    checkMaskFor missing557 StrongPackedBucketN11A3Shard004.record557 = true := by
  decide

def missing558 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 4442096234659840
theorem maskCheck558 :
    checkMaskFor missing558 StrongPackedBucketN11A3Shard004.record558 = true := by
  decide

def missing559 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 5603180513591296
theorem maskCheck559 :
    checkMaskFor missing559 StrongPackedBucketN11A3Shard004.record559 = true := by
  decide

def missing560 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 6658711676256256
theorem maskCheck560 :
    checkMaskFor missing560 StrongPackedBucketN11A3Shard004.record560 = true := by
  decide

def missing561 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 10106780140961792
theorem maskCheck561 :
    checkMaskFor missing561 StrongPackedBucketN11A3Shard004.record561 = true := by
  decide

def missing562 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 11197495675715584
theorem maskCheck562 :
    checkMaskFor missing562 StrongPackedBucketN11A3Shard004.record562 = true := by
  decide

def missing563 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 14047429814910976
theorem maskCheck563 :
    checkMaskFor missing563 StrongPackedBucketN11A3Shard004.record563 = true := by
  decide

def missing564 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 23054629069651968
theorem maskCheck564 :
    checkMaskFor missing564 StrongPackedBucketN11A3Shard004.record564 = true := by
  decide

def missing565 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 23547210278895616
theorem maskCheck565 :
    checkMaskFor missing565 StrongPackedBucketN11A3Shard004.record565 = true := by
  decide

def missing566 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 31780353347682304
theorem maskCheck566 :
    checkMaskFor missing566 StrongPackedBucketN11A3Shard004.record566 = true := by
  decide

def missing567 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 1091197110059008
theorem maskCheck567 :
    checkMaskFor missing567 StrongPackedBucketN11A3Shard004.record567 = true := by
  decide

def missing568 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 2076359528546304
theorem maskCheck568 :
    checkMaskFor missing568 StrongPackedBucketN11A3Shard004.record568 = true := by
  decide

def missing569 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 2146728272723968
theorem maskCheck569 :
    checkMaskFor missing569 StrongPackedBucketN11A3Shard004.record569 = true := by
  decide

def missing570 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 4257790598053888
theorem maskCheck570 :
    checkMaskFor missing570 StrongPackedBucketN11A3Shard004.record570 = true := by
  decide

def missing571 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 4363343714320384
theorem maskCheck571 :
    checkMaskFor missing571 StrongPackedBucketN11A3Shard004.record571 = true := by
  decide

def missing572 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 5031846784008192
theorem maskCheck572 :
    checkMaskFor missing572 StrongPackedBucketN11A3Shard004.record572 = true := by
  decide

def missing573 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 5454059249074176
theorem maskCheck573 :
    checkMaskFor missing573 StrongPackedBucketN11A3Shard004.record573 = true := by
  decide

def missing574 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 5524427993251840
theorem maskCheck574 :
    checkMaskFor missing574 StrongPackedBucketN11A3Shard004.record574 = true := by
  decide

def missing575 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 5559612365340672
theorem maskCheck575 :
    checkMaskFor missing575 StrongPackedBucketN11A3Shard004.record575 = true := by
  decide

def missing576 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 6509590411739136
theorem maskCheck576 :
    checkMaskFor missing576 StrongPackedBucketN11A3Shard004.record576 = true := by
  decide

def missing577 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 6544774783827968
theorem maskCheck577 :
    checkMaskFor missing577 StrongPackedBucketN11A3Shard004.record577 = true := by
  decide

def missing578 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 6615143528005632
theorem maskCheck578 :
    checkMaskFor missing578 StrongPackedBucketN11A3Shard004.record578 = true := by
  decide

def missing579 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 8726205853335552
theorem maskCheck579 :
    checkMaskFor missing579 StrongPackedBucketN11A3Shard004.record579 = true := by
  decide

def missing580 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 13757571062038528
theorem maskCheck580 :
    checkMaskFor missing580 StrongPackedBucketN11A3Shard004.record580 = true := by
  decide

def missing581 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 13898308550393856
theorem maskCheck581 :
    checkMaskFor missing581 StrongPackedBucketN11A3Shard004.record581 = true := by
  decide

def missing582 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 13968677294571520
theorem maskCheck582 :
    checkMaskFor missing582 StrongPackedBucketN11A3Shard004.record582 = true := by
  decide

def missing583 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 14390889759637504
theorem maskCheck583 :
    checkMaskFor missing583 StrongPackedBucketN11A3Shard004.record583 = true := by
  decide

def missing584 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 14496442875904000
theorem maskCheck584 :
    checkMaskFor missing584 StrongPackedBucketN11A3Shard004.record584 = true := by
  decide

def missing585 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 15481605294391296
theorem maskCheck585 :
    checkMaskFor missing585 StrongPackedBucketN11A3Shard004.record585 = true := by
  decide

def missing586 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 18542645666119680
theorem maskCheck586 :
    checkMaskFor missing586 StrongPackedBucketN11A3Shard004.record586 = true := by
  decide

def missing587 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 18964858131185664
theorem maskCheck587 :
    checkMaskFor missing587 StrongPackedBucketN11A3Shard004.record587 = true := by
  decide

def missing588 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 19035226875363328
theorem maskCheck588 :
    checkMaskFor missing588 StrongPackedBucketN11A3Shard004.record588 = true := by
  decide

def missing589 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 20020389293850624
theorem maskCheck589 :
    checkMaskFor missing589 StrongPackedBucketN11A3Shard004.record589 = true := by
  decide

def missing590 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 20125942410117120
theorem maskCheck590 :
    checkMaskFor missing590 StrongPackedBucketN11A3Shard004.record590 = true := by
  decide

def missing591 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 22237004735447040
theorem maskCheck591 :
    checkMaskFor missing591 StrongPackedBucketN11A3Shard004.record591 = true := by
  decide

def missing592 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 22764770316779520
theorem maskCheck592 :
    checkMaskFor missing592 StrongPackedBucketN11A3Shard004.record592 = true := by
  decide

def missing593 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 22905507805134848
theorem maskCheck593 :
    checkMaskFor missing593 StrongPackedBucketN11A3Shard004.record593 = true := by
  decide

def missing594 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 22975876549312512
theorem maskCheck594 :
    checkMaskFor missing594 StrongPackedBucketN11A3Shard004.record594 = true := by
  decide

def missing595 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 23011060921401344
theorem maskCheck595 :
    checkMaskFor missing595 StrongPackedBucketN11A3Shard004.record595 = true := by
  decide

def missing596 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 23398089014378496
theorem maskCheck596 :
    checkMaskFor missing596 StrongPackedBucketN11A3Shard004.record596 = true := by
  decide

def missing597 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 23433273386467328
theorem maskCheck597 :
    checkMaskFor missing597 StrongPackedBucketN11A3Shard004.record597 = true := by
  decide

def missing598 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 23503642130644992
theorem maskCheck598 :
    checkMaskFor missing598 StrongPackedBucketN11A3Shard004.record598 = true := by
  decide

def missing599 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 24488804549132288
theorem maskCheck599 :
    checkMaskFor missing599 StrongPackedBucketN11A3Shard004.record599 = true := by
  decide

def missing600 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 31631232083165184
theorem maskCheck600 :
    checkMaskFor missing600 StrongPackedBucketN11A3Shard004.record600 = true := by
  decide

def missing601 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 31701600827342848
theorem maskCheck601 :
    checkMaskFor missing601 StrongPackedBucketN11A3Shard004.record601 = true := by
  decide

def missing602 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 31842338315698176
theorem maskCheck602 :
    checkMaskFor missing602 StrongPackedBucketN11A3Shard004.record602 = true := by
  decide

def missing603 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 31947891431964672
theorem maskCheck603 :
    checkMaskFor missing603 StrongPackedBucketN11A3Shard004.record603 = true := by
  decide

def missing604 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 32370103897030656
theorem maskCheck604 :
    checkMaskFor missing604 StrongPackedBucketN11A3Shard004.record604 = true := by
  decide

def missing605 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 1091609426919424
theorem maskCheck605 :
    checkMaskFor missing605 StrongPackedBucketN11A3Shard004.record605 = true := by
  decide

def missing606 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 1936034357051392
theorem maskCheck606 :
    checkMaskFor missing606 StrongPackedBucketN11A3Shard004.record606 = true := by
  decide

def missing607 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 2147140589584384
theorem maskCheck607 :
    checkMaskFor missing607 StrongPackedBucketN11A3Shard004.record607 = true := by
  decide

def missing608 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 2182324961673216
theorem maskCheck608 :
    checkMaskFor missing608 StrongPackedBucketN11A3Shard004.record608 = true := by
  decide

def missing609 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 4047096682381312
theorem maskCheck609 :
    checkMaskFor missing609 StrongPackedBucketN11A3Shard004.record609 = true := by
  decide

def missing610 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 4117465426558976
theorem maskCheck610 :
    checkMaskFor missing610 StrongPackedBucketN11A3Shard004.record610 = true := by
  decide

def missing611 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 4152649798647808
theorem maskCheck611 :
    checkMaskFor missing611 StrongPackedBucketN11A3Shard004.record611 = true := by
  decide

def missing612 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 4363756031180800
theorem maskCheck612 :
    checkMaskFor missing612 StrongPackedBucketN11A3Shard004.record612 = true := by
  decide

def missing613 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 5032259100868608
theorem maskCheck613 :
    checkMaskFor missing613 StrongPackedBucketN11A3Shard004.record613 = true := by
  decide

def missing614 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 5313734077579264
theorem maskCheck614 :
    checkMaskFor missing614 StrongPackedBucketN11A3Shard004.record614 = true := by
  decide

def missing615 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 5524840310112256
theorem maskCheck615 :
    checkMaskFor missing615 StrongPackedBucketN11A3Shard004.record615 = true := by
  decide

def missing616 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 5560024682201088
theorem maskCheck616 :
    checkMaskFor missing616 StrongPackedBucketN11A3Shard004.record616 = true := by
  decide

def missing617 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 6298896496066560
theorem maskCheck617 :
    checkMaskFor missing617 StrongPackedBucketN11A3Shard004.record617 = true := by
  decide

def missing618 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 6369265240244224
theorem maskCheck618 :
    checkMaskFor missing618 StrongPackedBucketN11A3Shard004.record618 = true := by
  decide

def missing619 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 6404449612333056
theorem maskCheck619 :
    checkMaskFor missing619 StrongPackedBucketN11A3Shard004.record619 = true := by
  decide

def missing620 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 6615555844866048
theorem maskCheck620 :
    checkMaskFor missing620 StrongPackedBucketN11A3Shard004.record620 = true := by
  decide

def missing621 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 8480327565574144
theorem maskCheck621 :
    checkMaskFor missing621 StrongPackedBucketN11A3Shard004.record621 = true := by
  decide

def missing622 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 8515511937662976
theorem maskCheck622 :
    checkMaskFor missing622 StrongPackedBucketN11A3Shard004.record622 = true := by
  decide

def missing623 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 8585880681840640
theorem maskCheck623 :
    checkMaskFor missing623 StrongPackedBucketN11A3Shard004.record623 = true := by
  decide

def missing624 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 9535858728239104
theorem maskCheck624 :
    checkMaskFor missing624 StrongPackedBucketN11A3Shard004.record624 = true := by
  decide

def missing625 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 9817333704949760
theorem maskCheck625 :
    checkMaskFor missing625 StrongPackedBucketN11A3Shard004.record625 = true := by
  decide

def missing626 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 10063624309571584
theorem maskCheck626 :
    checkMaskFor missing626 StrongPackedBucketN11A3Shard004.record626 = true := by
  decide

def missing627 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 10802496123437056
theorem maskCheck627 :
    checkMaskFor missing627 StrongPackedBucketN11A3Shard004.record627 = true := by
  decide

def missing628 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 10908049239703552
theorem maskCheck628 :
    checkMaskFor missing628 StrongPackedBucketN11A3Shard004.record628 = true := by
  decide

def missing629 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 13019111565033472
theorem maskCheck629 :
    checkMaskFor missing629 StrongPackedBucketN11A3Shard004.record629 = true := by
  decide

def missing630 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 13757983378898944
theorem maskCheck630 :
    checkMaskFor missing630 StrongPackedBucketN11A3Shard004.record630 = true := by
  decide

def missing631 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 14004273983520768
theorem maskCheck631 :
    checkMaskFor missing631 StrongPackedBucketN11A3Shard004.record631 = true := by
  decide

def missing632 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 14180195843964928
theorem maskCheck632 :
    checkMaskFor missing632 StrongPackedBucketN11A3Shard004.record632 = true := by
  decide

def missing633 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 14285748960231424
theorem maskCheck633 :
    checkMaskFor missing633 StrongPackedBucketN11A3Shard004.record633 = true := by
  decide

def missing634 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 15270911378718720
theorem maskCheck634 :
    checkMaskFor missing634 StrongPackedBucketN11A3Shard004.record634 = true := by
  decide

def missing635 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 18543057982980096
theorem maskCheck635 :
    checkMaskFor missing635 StrongPackedBucketN11A3Shard004.record635 = true := by
  decide

def missing636 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 18824532959690752
theorem maskCheck636 :
    checkMaskFor missing636 StrongPackedBucketN11A3Shard004.record636 = true := by
  decide

def missing637 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 19035639192223744
theorem maskCheck637 :
    checkMaskFor missing637 StrongPackedBucketN11A3Shard004.record637 = true := by
  decide

def missing638 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 19070823564312576
theorem maskCheck638 :
    checkMaskFor missing638 StrongPackedBucketN11A3Shard004.record638 = true := by
  decide

def missing639 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 19809695378178048
theorem maskCheck639 :
    checkMaskFor missing639 StrongPackedBucketN11A3Shard004.record639 = true := by
  decide

def missing512_513 : List (BitVec (edgeCount 11)) :=
  [missing512]
abbrev records512_513 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record512]
theorem aligned512_513 :
    AlignedValid 11 3 missing512_513 records512_513 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check512
    maskCheck512 AlignedValid.nil

def missing513_514 : List (BitVec (edgeCount 11)) :=
  [missing513]
abbrev records513_514 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record513]
theorem aligned513_514 :
    AlignedValid 11 3 missing513_514 records513_514 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check513
    maskCheck513 AlignedValid.nil

def missing512_514 : List (BitVec (edgeCount 11)) :=
  missing512_513 ++ missing513_514
abbrev records512_514 : List Blob :=
  records512_513 ++ records513_514
theorem aligned512_514 :
    AlignedValid 11 3 missing512_514 records512_514 :=
  aligned512_513.append aligned513_514

def missing514_515 : List (BitVec (edgeCount 11)) :=
  [missing514]
abbrev records514_515 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record514]
theorem aligned514_515 :
    AlignedValid 11 3 missing514_515 records514_515 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check514
    maskCheck514 AlignedValid.nil

def missing515_516 : List (BitVec (edgeCount 11)) :=
  [missing515]
abbrev records515_516 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record515]
theorem aligned515_516 :
    AlignedValid 11 3 missing515_516 records515_516 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check515
    maskCheck515 AlignedValid.nil

def missing514_516 : List (BitVec (edgeCount 11)) :=
  missing514_515 ++ missing515_516
abbrev records514_516 : List Blob :=
  records514_515 ++ records515_516
theorem aligned514_516 :
    AlignedValid 11 3 missing514_516 records514_516 :=
  aligned514_515.append aligned515_516

def missing512_516 : List (BitVec (edgeCount 11)) :=
  missing512_514 ++ missing514_516
abbrev records512_516 : List Blob :=
  records512_514 ++ records514_516
theorem aligned512_516 :
    AlignedValid 11 3 missing512_516 records512_516 :=
  aligned512_514.append aligned514_516

def missing516_517 : List (BitVec (edgeCount 11)) :=
  [missing516]
abbrev records516_517 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record516]
theorem aligned516_517 :
    AlignedValid 11 3 missing516_517 records516_517 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check516
    maskCheck516 AlignedValid.nil

def missing517_518 : List (BitVec (edgeCount 11)) :=
  [missing517]
abbrev records517_518 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record517]
theorem aligned517_518 :
    AlignedValid 11 3 missing517_518 records517_518 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check517
    maskCheck517 AlignedValid.nil

def missing516_518 : List (BitVec (edgeCount 11)) :=
  missing516_517 ++ missing517_518
abbrev records516_518 : List Blob :=
  records516_517 ++ records517_518
theorem aligned516_518 :
    AlignedValid 11 3 missing516_518 records516_518 :=
  aligned516_517.append aligned517_518

def missing518_519 : List (BitVec (edgeCount 11)) :=
  [missing518]
abbrev records518_519 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record518]
theorem aligned518_519 :
    AlignedValid 11 3 missing518_519 records518_519 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check518
    maskCheck518 AlignedValid.nil

def missing519_520 : List (BitVec (edgeCount 11)) :=
  [missing519]
abbrev records519_520 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record519]
theorem aligned519_520 :
    AlignedValid 11 3 missing519_520 records519_520 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check519
    maskCheck519 AlignedValid.nil

def missing518_520 : List (BitVec (edgeCount 11)) :=
  missing518_519 ++ missing519_520
abbrev records518_520 : List Blob :=
  records518_519 ++ records519_520
theorem aligned518_520 :
    AlignedValid 11 3 missing518_520 records518_520 :=
  aligned518_519.append aligned519_520

def missing516_520 : List (BitVec (edgeCount 11)) :=
  missing516_518 ++ missing518_520
abbrev records516_520 : List Blob :=
  records516_518 ++ records518_520
theorem aligned516_520 :
    AlignedValid 11 3 missing516_520 records516_520 :=
  aligned516_518.append aligned518_520

def missing512_520 : List (BitVec (edgeCount 11)) :=
  missing512_516 ++ missing516_520
abbrev records512_520 : List Blob :=
  records512_516 ++ records516_520
theorem aligned512_520 :
    AlignedValid 11 3 missing512_520 records512_520 :=
  aligned512_516.append aligned516_520

def missing520_521 : List (BitVec (edgeCount 11)) :=
  [missing520]
abbrev records520_521 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record520]
theorem aligned520_521 :
    AlignedValid 11 3 missing520_521 records520_521 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check520
    maskCheck520 AlignedValid.nil

def missing521_522 : List (BitVec (edgeCount 11)) :=
  [missing521]
abbrev records521_522 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record521]
theorem aligned521_522 :
    AlignedValid 11 3 missing521_522 records521_522 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check521
    maskCheck521 AlignedValid.nil

def missing520_522 : List (BitVec (edgeCount 11)) :=
  missing520_521 ++ missing521_522
abbrev records520_522 : List Blob :=
  records520_521 ++ records521_522
theorem aligned520_522 :
    AlignedValid 11 3 missing520_522 records520_522 :=
  aligned520_521.append aligned521_522

def missing522_523 : List (BitVec (edgeCount 11)) :=
  [missing522]
abbrev records522_523 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record522]
theorem aligned522_523 :
    AlignedValid 11 3 missing522_523 records522_523 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check522
    maskCheck522 AlignedValid.nil

def missing523_524 : List (BitVec (edgeCount 11)) :=
  [missing523]
abbrev records523_524 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record523]
theorem aligned523_524 :
    AlignedValid 11 3 missing523_524 records523_524 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check523
    maskCheck523 AlignedValid.nil

def missing522_524 : List (BitVec (edgeCount 11)) :=
  missing522_523 ++ missing523_524
abbrev records522_524 : List Blob :=
  records522_523 ++ records523_524
theorem aligned522_524 :
    AlignedValid 11 3 missing522_524 records522_524 :=
  aligned522_523.append aligned523_524

def missing520_524 : List (BitVec (edgeCount 11)) :=
  missing520_522 ++ missing522_524
abbrev records520_524 : List Blob :=
  records520_522 ++ records522_524
theorem aligned520_524 :
    AlignedValid 11 3 missing520_524 records520_524 :=
  aligned520_522.append aligned522_524

def missing524_525 : List (BitVec (edgeCount 11)) :=
  [missing524]
abbrev records524_525 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record524]
theorem aligned524_525 :
    AlignedValid 11 3 missing524_525 records524_525 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check524
    maskCheck524 AlignedValid.nil

def missing525_526 : List (BitVec (edgeCount 11)) :=
  [missing525]
abbrev records525_526 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record525]
theorem aligned525_526 :
    AlignedValid 11 3 missing525_526 records525_526 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check525
    maskCheck525 AlignedValid.nil

def missing524_526 : List (BitVec (edgeCount 11)) :=
  missing524_525 ++ missing525_526
abbrev records524_526 : List Blob :=
  records524_525 ++ records525_526
theorem aligned524_526 :
    AlignedValid 11 3 missing524_526 records524_526 :=
  aligned524_525.append aligned525_526

def missing526_527 : List (BitVec (edgeCount 11)) :=
  [missing526]
abbrev records526_527 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record526]
theorem aligned526_527 :
    AlignedValid 11 3 missing526_527 records526_527 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check526
    maskCheck526 AlignedValid.nil

def missing527_528 : List (BitVec (edgeCount 11)) :=
  [missing527]
abbrev records527_528 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record527]
theorem aligned527_528 :
    AlignedValid 11 3 missing527_528 records527_528 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check527
    maskCheck527 AlignedValid.nil

def missing526_528 : List (BitVec (edgeCount 11)) :=
  missing526_527 ++ missing527_528
abbrev records526_528 : List Blob :=
  records526_527 ++ records527_528
theorem aligned526_528 :
    AlignedValid 11 3 missing526_528 records526_528 :=
  aligned526_527.append aligned527_528

def missing524_528 : List (BitVec (edgeCount 11)) :=
  missing524_526 ++ missing526_528
abbrev records524_528 : List Blob :=
  records524_526 ++ records526_528
theorem aligned524_528 :
    AlignedValid 11 3 missing524_528 records524_528 :=
  aligned524_526.append aligned526_528

def missing520_528 : List (BitVec (edgeCount 11)) :=
  missing520_524 ++ missing524_528
abbrev records520_528 : List Blob :=
  records520_524 ++ records524_528
theorem aligned520_528 :
    AlignedValid 11 3 missing520_528 records520_528 :=
  aligned520_524.append aligned524_528

def missing512_528 : List (BitVec (edgeCount 11)) :=
  missing512_520 ++ missing520_528
abbrev records512_528 : List Blob :=
  records512_520 ++ records520_528
theorem aligned512_528 :
    AlignedValid 11 3 missing512_528 records512_528 :=
  aligned512_520.append aligned520_528

def missing528_529 : List (BitVec (edgeCount 11)) :=
  [missing528]
abbrev records528_529 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record528]
theorem aligned528_529 :
    AlignedValid 11 3 missing528_529 records528_529 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check528
    maskCheck528 AlignedValid.nil

def missing529_530 : List (BitVec (edgeCount 11)) :=
  [missing529]
abbrev records529_530 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record529]
theorem aligned529_530 :
    AlignedValid 11 3 missing529_530 records529_530 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check529
    maskCheck529 AlignedValid.nil

def missing528_530 : List (BitVec (edgeCount 11)) :=
  missing528_529 ++ missing529_530
abbrev records528_530 : List Blob :=
  records528_529 ++ records529_530
theorem aligned528_530 :
    AlignedValid 11 3 missing528_530 records528_530 :=
  aligned528_529.append aligned529_530

def missing530_531 : List (BitVec (edgeCount 11)) :=
  [missing530]
abbrev records530_531 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record530]
theorem aligned530_531 :
    AlignedValid 11 3 missing530_531 records530_531 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check530
    maskCheck530 AlignedValid.nil

def missing531_532 : List (BitVec (edgeCount 11)) :=
  [missing531]
abbrev records531_532 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record531]
theorem aligned531_532 :
    AlignedValid 11 3 missing531_532 records531_532 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check531
    maskCheck531 AlignedValid.nil

def missing530_532 : List (BitVec (edgeCount 11)) :=
  missing530_531 ++ missing531_532
abbrev records530_532 : List Blob :=
  records530_531 ++ records531_532
theorem aligned530_532 :
    AlignedValid 11 3 missing530_532 records530_532 :=
  aligned530_531.append aligned531_532

def missing528_532 : List (BitVec (edgeCount 11)) :=
  missing528_530 ++ missing530_532
abbrev records528_532 : List Blob :=
  records528_530 ++ records530_532
theorem aligned528_532 :
    AlignedValid 11 3 missing528_532 records528_532 :=
  aligned528_530.append aligned530_532

def missing532_533 : List (BitVec (edgeCount 11)) :=
  [missing532]
abbrev records532_533 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record532]
theorem aligned532_533 :
    AlignedValid 11 3 missing532_533 records532_533 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check532
    maskCheck532 AlignedValid.nil

def missing533_534 : List (BitVec (edgeCount 11)) :=
  [missing533]
abbrev records533_534 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record533]
theorem aligned533_534 :
    AlignedValid 11 3 missing533_534 records533_534 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check533
    maskCheck533 AlignedValid.nil

def missing532_534 : List (BitVec (edgeCount 11)) :=
  missing532_533 ++ missing533_534
abbrev records532_534 : List Blob :=
  records532_533 ++ records533_534
theorem aligned532_534 :
    AlignedValid 11 3 missing532_534 records532_534 :=
  aligned532_533.append aligned533_534

def missing534_535 : List (BitVec (edgeCount 11)) :=
  [missing534]
abbrev records534_535 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record534]
theorem aligned534_535 :
    AlignedValid 11 3 missing534_535 records534_535 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check534
    maskCheck534 AlignedValid.nil

def missing535_536 : List (BitVec (edgeCount 11)) :=
  [missing535]
abbrev records535_536 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record535]
theorem aligned535_536 :
    AlignedValid 11 3 missing535_536 records535_536 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check535
    maskCheck535 AlignedValid.nil

def missing534_536 : List (BitVec (edgeCount 11)) :=
  missing534_535 ++ missing535_536
abbrev records534_536 : List Blob :=
  records534_535 ++ records535_536
theorem aligned534_536 :
    AlignedValid 11 3 missing534_536 records534_536 :=
  aligned534_535.append aligned535_536

def missing532_536 : List (BitVec (edgeCount 11)) :=
  missing532_534 ++ missing534_536
abbrev records532_536 : List Blob :=
  records532_534 ++ records534_536
theorem aligned532_536 :
    AlignedValid 11 3 missing532_536 records532_536 :=
  aligned532_534.append aligned534_536

def missing528_536 : List (BitVec (edgeCount 11)) :=
  missing528_532 ++ missing532_536
abbrev records528_536 : List Blob :=
  records528_532 ++ records532_536
theorem aligned528_536 :
    AlignedValid 11 3 missing528_536 records528_536 :=
  aligned528_532.append aligned532_536

def missing536_537 : List (BitVec (edgeCount 11)) :=
  [missing536]
abbrev records536_537 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record536]
theorem aligned536_537 :
    AlignedValid 11 3 missing536_537 records536_537 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check536
    maskCheck536 AlignedValid.nil

def missing537_538 : List (BitVec (edgeCount 11)) :=
  [missing537]
abbrev records537_538 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record537]
theorem aligned537_538 :
    AlignedValid 11 3 missing537_538 records537_538 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check537
    maskCheck537 AlignedValid.nil

def missing536_538 : List (BitVec (edgeCount 11)) :=
  missing536_537 ++ missing537_538
abbrev records536_538 : List Blob :=
  records536_537 ++ records537_538
theorem aligned536_538 :
    AlignedValid 11 3 missing536_538 records536_538 :=
  aligned536_537.append aligned537_538

def missing538_539 : List (BitVec (edgeCount 11)) :=
  [missing538]
abbrev records538_539 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record538]
theorem aligned538_539 :
    AlignedValid 11 3 missing538_539 records538_539 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check538
    maskCheck538 AlignedValid.nil

def missing539_540 : List (BitVec (edgeCount 11)) :=
  [missing539]
abbrev records539_540 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record539]
theorem aligned539_540 :
    AlignedValid 11 3 missing539_540 records539_540 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check539
    maskCheck539 AlignedValid.nil

def missing538_540 : List (BitVec (edgeCount 11)) :=
  missing538_539 ++ missing539_540
abbrev records538_540 : List Blob :=
  records538_539 ++ records539_540
theorem aligned538_540 :
    AlignedValid 11 3 missing538_540 records538_540 :=
  aligned538_539.append aligned539_540

def missing536_540 : List (BitVec (edgeCount 11)) :=
  missing536_538 ++ missing538_540
abbrev records536_540 : List Blob :=
  records536_538 ++ records538_540
theorem aligned536_540 :
    AlignedValid 11 3 missing536_540 records536_540 :=
  aligned536_538.append aligned538_540

def missing540_541 : List (BitVec (edgeCount 11)) :=
  [missing540]
abbrev records540_541 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record540]
theorem aligned540_541 :
    AlignedValid 11 3 missing540_541 records540_541 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check540
    maskCheck540 AlignedValid.nil

def missing541_542 : List (BitVec (edgeCount 11)) :=
  [missing541]
abbrev records541_542 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record541]
theorem aligned541_542 :
    AlignedValid 11 3 missing541_542 records541_542 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check541
    maskCheck541 AlignedValid.nil

def missing540_542 : List (BitVec (edgeCount 11)) :=
  missing540_541 ++ missing541_542
abbrev records540_542 : List Blob :=
  records540_541 ++ records541_542
theorem aligned540_542 :
    AlignedValid 11 3 missing540_542 records540_542 :=
  aligned540_541.append aligned541_542

def missing542_543 : List (BitVec (edgeCount 11)) :=
  [missing542]
abbrev records542_543 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record542]
theorem aligned542_543 :
    AlignedValid 11 3 missing542_543 records542_543 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check542
    maskCheck542 AlignedValid.nil

def missing543_544 : List (BitVec (edgeCount 11)) :=
  [missing543]
abbrev records543_544 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record543]
theorem aligned543_544 :
    AlignedValid 11 3 missing543_544 records543_544 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check543
    maskCheck543 AlignedValid.nil

def missing542_544 : List (BitVec (edgeCount 11)) :=
  missing542_543 ++ missing543_544
abbrev records542_544 : List Blob :=
  records542_543 ++ records543_544
theorem aligned542_544 :
    AlignedValid 11 3 missing542_544 records542_544 :=
  aligned542_543.append aligned543_544

def missing540_544 : List (BitVec (edgeCount 11)) :=
  missing540_542 ++ missing542_544
abbrev records540_544 : List Blob :=
  records540_542 ++ records542_544
theorem aligned540_544 :
    AlignedValid 11 3 missing540_544 records540_544 :=
  aligned540_542.append aligned542_544

def missing536_544 : List (BitVec (edgeCount 11)) :=
  missing536_540 ++ missing540_544
abbrev records536_544 : List Blob :=
  records536_540 ++ records540_544
theorem aligned536_544 :
    AlignedValid 11 3 missing536_544 records536_544 :=
  aligned536_540.append aligned540_544

def missing528_544 : List (BitVec (edgeCount 11)) :=
  missing528_536 ++ missing536_544
abbrev records528_544 : List Blob :=
  records528_536 ++ records536_544
theorem aligned528_544 :
    AlignedValid 11 3 missing528_544 records528_544 :=
  aligned528_536.append aligned536_544

def missing512_544 : List (BitVec (edgeCount 11)) :=
  missing512_528 ++ missing528_544
abbrev records512_544 : List Blob :=
  records512_528 ++ records528_544
theorem aligned512_544 :
    AlignedValid 11 3 missing512_544 records512_544 :=
  aligned512_528.append aligned528_544

def missing544_545 : List (BitVec (edgeCount 11)) :=
  [missing544]
abbrev records544_545 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record544]
theorem aligned544_545 :
    AlignedValid 11 3 missing544_545 records544_545 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check544
    maskCheck544 AlignedValid.nil

def missing545_546 : List (BitVec (edgeCount 11)) :=
  [missing545]
abbrev records545_546 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record545]
theorem aligned545_546 :
    AlignedValid 11 3 missing545_546 records545_546 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check545
    maskCheck545 AlignedValid.nil

def missing544_546 : List (BitVec (edgeCount 11)) :=
  missing544_545 ++ missing545_546
abbrev records544_546 : List Blob :=
  records544_545 ++ records545_546
theorem aligned544_546 :
    AlignedValid 11 3 missing544_546 records544_546 :=
  aligned544_545.append aligned545_546

def missing546_547 : List (BitVec (edgeCount 11)) :=
  [missing546]
abbrev records546_547 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record546]
theorem aligned546_547 :
    AlignedValid 11 3 missing546_547 records546_547 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check546
    maskCheck546 AlignedValid.nil

def missing547_548 : List (BitVec (edgeCount 11)) :=
  [missing547]
abbrev records547_548 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record547]
theorem aligned547_548 :
    AlignedValid 11 3 missing547_548 records547_548 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check547
    maskCheck547 AlignedValid.nil

def missing546_548 : List (BitVec (edgeCount 11)) :=
  missing546_547 ++ missing547_548
abbrev records546_548 : List Blob :=
  records546_547 ++ records547_548
theorem aligned546_548 :
    AlignedValid 11 3 missing546_548 records546_548 :=
  aligned546_547.append aligned547_548

def missing544_548 : List (BitVec (edgeCount 11)) :=
  missing544_546 ++ missing546_548
abbrev records544_548 : List Blob :=
  records544_546 ++ records546_548
theorem aligned544_548 :
    AlignedValid 11 3 missing544_548 records544_548 :=
  aligned544_546.append aligned546_548

def missing548_549 : List (BitVec (edgeCount 11)) :=
  [missing548]
abbrev records548_549 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record548]
theorem aligned548_549 :
    AlignedValid 11 3 missing548_549 records548_549 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check548
    maskCheck548 AlignedValid.nil

def missing549_550 : List (BitVec (edgeCount 11)) :=
  [missing549]
abbrev records549_550 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record549]
theorem aligned549_550 :
    AlignedValid 11 3 missing549_550 records549_550 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check549
    maskCheck549 AlignedValid.nil

def missing548_550 : List (BitVec (edgeCount 11)) :=
  missing548_549 ++ missing549_550
abbrev records548_550 : List Blob :=
  records548_549 ++ records549_550
theorem aligned548_550 :
    AlignedValid 11 3 missing548_550 records548_550 :=
  aligned548_549.append aligned549_550

def missing550_551 : List (BitVec (edgeCount 11)) :=
  [missing550]
abbrev records550_551 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record550]
theorem aligned550_551 :
    AlignedValid 11 3 missing550_551 records550_551 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check550
    maskCheck550 AlignedValid.nil

def missing551_552 : List (BitVec (edgeCount 11)) :=
  [missing551]
abbrev records551_552 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record551]
theorem aligned551_552 :
    AlignedValid 11 3 missing551_552 records551_552 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check551
    maskCheck551 AlignedValid.nil

def missing550_552 : List (BitVec (edgeCount 11)) :=
  missing550_551 ++ missing551_552
abbrev records550_552 : List Blob :=
  records550_551 ++ records551_552
theorem aligned550_552 :
    AlignedValid 11 3 missing550_552 records550_552 :=
  aligned550_551.append aligned551_552

def missing548_552 : List (BitVec (edgeCount 11)) :=
  missing548_550 ++ missing550_552
abbrev records548_552 : List Blob :=
  records548_550 ++ records550_552
theorem aligned548_552 :
    AlignedValid 11 3 missing548_552 records548_552 :=
  aligned548_550.append aligned550_552

def missing544_552 : List (BitVec (edgeCount 11)) :=
  missing544_548 ++ missing548_552
abbrev records544_552 : List Blob :=
  records544_548 ++ records548_552
theorem aligned544_552 :
    AlignedValid 11 3 missing544_552 records544_552 :=
  aligned544_548.append aligned548_552

def missing552_553 : List (BitVec (edgeCount 11)) :=
  [missing552]
abbrev records552_553 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record552]
theorem aligned552_553 :
    AlignedValid 11 3 missing552_553 records552_553 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check552
    maskCheck552 AlignedValid.nil

def missing553_554 : List (BitVec (edgeCount 11)) :=
  [missing553]
abbrev records553_554 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record553]
theorem aligned553_554 :
    AlignedValid 11 3 missing553_554 records553_554 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check553
    maskCheck553 AlignedValid.nil

def missing552_554 : List (BitVec (edgeCount 11)) :=
  missing552_553 ++ missing553_554
abbrev records552_554 : List Blob :=
  records552_553 ++ records553_554
theorem aligned552_554 :
    AlignedValid 11 3 missing552_554 records552_554 :=
  aligned552_553.append aligned553_554

def missing554_555 : List (BitVec (edgeCount 11)) :=
  [missing554]
abbrev records554_555 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record554]
theorem aligned554_555 :
    AlignedValid 11 3 missing554_555 records554_555 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check554
    maskCheck554 AlignedValid.nil

def missing555_556 : List (BitVec (edgeCount 11)) :=
  [missing555]
abbrev records555_556 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record555]
theorem aligned555_556 :
    AlignedValid 11 3 missing555_556 records555_556 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check555
    maskCheck555 AlignedValid.nil

def missing554_556 : List (BitVec (edgeCount 11)) :=
  missing554_555 ++ missing555_556
abbrev records554_556 : List Blob :=
  records554_555 ++ records555_556
theorem aligned554_556 :
    AlignedValid 11 3 missing554_556 records554_556 :=
  aligned554_555.append aligned555_556

def missing552_556 : List (BitVec (edgeCount 11)) :=
  missing552_554 ++ missing554_556
abbrev records552_556 : List Blob :=
  records552_554 ++ records554_556
theorem aligned552_556 :
    AlignedValid 11 3 missing552_556 records552_556 :=
  aligned552_554.append aligned554_556

def missing556_557 : List (BitVec (edgeCount 11)) :=
  [missing556]
abbrev records556_557 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record556]
theorem aligned556_557 :
    AlignedValid 11 3 missing556_557 records556_557 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check556
    maskCheck556 AlignedValid.nil

def missing557_558 : List (BitVec (edgeCount 11)) :=
  [missing557]
abbrev records557_558 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record557]
theorem aligned557_558 :
    AlignedValid 11 3 missing557_558 records557_558 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check557
    maskCheck557 AlignedValid.nil

def missing556_558 : List (BitVec (edgeCount 11)) :=
  missing556_557 ++ missing557_558
abbrev records556_558 : List Blob :=
  records556_557 ++ records557_558
theorem aligned556_558 :
    AlignedValid 11 3 missing556_558 records556_558 :=
  aligned556_557.append aligned557_558

def missing558_559 : List (BitVec (edgeCount 11)) :=
  [missing558]
abbrev records558_559 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record558]
theorem aligned558_559 :
    AlignedValid 11 3 missing558_559 records558_559 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check558
    maskCheck558 AlignedValid.nil

def missing559_560 : List (BitVec (edgeCount 11)) :=
  [missing559]
abbrev records559_560 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record559]
theorem aligned559_560 :
    AlignedValid 11 3 missing559_560 records559_560 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check559
    maskCheck559 AlignedValid.nil

def missing558_560 : List (BitVec (edgeCount 11)) :=
  missing558_559 ++ missing559_560
abbrev records558_560 : List Blob :=
  records558_559 ++ records559_560
theorem aligned558_560 :
    AlignedValid 11 3 missing558_560 records558_560 :=
  aligned558_559.append aligned559_560

def missing556_560 : List (BitVec (edgeCount 11)) :=
  missing556_558 ++ missing558_560
abbrev records556_560 : List Blob :=
  records556_558 ++ records558_560
theorem aligned556_560 :
    AlignedValid 11 3 missing556_560 records556_560 :=
  aligned556_558.append aligned558_560

def missing552_560 : List (BitVec (edgeCount 11)) :=
  missing552_556 ++ missing556_560
abbrev records552_560 : List Blob :=
  records552_556 ++ records556_560
theorem aligned552_560 :
    AlignedValid 11 3 missing552_560 records552_560 :=
  aligned552_556.append aligned556_560

def missing544_560 : List (BitVec (edgeCount 11)) :=
  missing544_552 ++ missing552_560
abbrev records544_560 : List Blob :=
  records544_552 ++ records552_560
theorem aligned544_560 :
    AlignedValid 11 3 missing544_560 records544_560 :=
  aligned544_552.append aligned552_560

def missing560_561 : List (BitVec (edgeCount 11)) :=
  [missing560]
abbrev records560_561 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record560]
theorem aligned560_561 :
    AlignedValid 11 3 missing560_561 records560_561 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check560
    maskCheck560 AlignedValid.nil

def missing561_562 : List (BitVec (edgeCount 11)) :=
  [missing561]
abbrev records561_562 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record561]
theorem aligned561_562 :
    AlignedValid 11 3 missing561_562 records561_562 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check561
    maskCheck561 AlignedValid.nil

def missing560_562 : List (BitVec (edgeCount 11)) :=
  missing560_561 ++ missing561_562
abbrev records560_562 : List Blob :=
  records560_561 ++ records561_562
theorem aligned560_562 :
    AlignedValid 11 3 missing560_562 records560_562 :=
  aligned560_561.append aligned561_562

def missing562_563 : List (BitVec (edgeCount 11)) :=
  [missing562]
abbrev records562_563 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record562]
theorem aligned562_563 :
    AlignedValid 11 3 missing562_563 records562_563 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check562
    maskCheck562 AlignedValid.nil

def missing563_564 : List (BitVec (edgeCount 11)) :=
  [missing563]
abbrev records563_564 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record563]
theorem aligned563_564 :
    AlignedValid 11 3 missing563_564 records563_564 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check563
    maskCheck563 AlignedValid.nil

def missing562_564 : List (BitVec (edgeCount 11)) :=
  missing562_563 ++ missing563_564
abbrev records562_564 : List Blob :=
  records562_563 ++ records563_564
theorem aligned562_564 :
    AlignedValid 11 3 missing562_564 records562_564 :=
  aligned562_563.append aligned563_564

def missing560_564 : List (BitVec (edgeCount 11)) :=
  missing560_562 ++ missing562_564
abbrev records560_564 : List Blob :=
  records560_562 ++ records562_564
theorem aligned560_564 :
    AlignedValid 11 3 missing560_564 records560_564 :=
  aligned560_562.append aligned562_564

def missing564_565 : List (BitVec (edgeCount 11)) :=
  [missing564]
abbrev records564_565 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record564]
theorem aligned564_565 :
    AlignedValid 11 3 missing564_565 records564_565 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check564
    maskCheck564 AlignedValid.nil

def missing565_566 : List (BitVec (edgeCount 11)) :=
  [missing565]
abbrev records565_566 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record565]
theorem aligned565_566 :
    AlignedValid 11 3 missing565_566 records565_566 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check565
    maskCheck565 AlignedValid.nil

def missing564_566 : List (BitVec (edgeCount 11)) :=
  missing564_565 ++ missing565_566
abbrev records564_566 : List Blob :=
  records564_565 ++ records565_566
theorem aligned564_566 :
    AlignedValid 11 3 missing564_566 records564_566 :=
  aligned564_565.append aligned565_566

def missing566_567 : List (BitVec (edgeCount 11)) :=
  [missing566]
abbrev records566_567 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record566]
theorem aligned566_567 :
    AlignedValid 11 3 missing566_567 records566_567 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check566
    maskCheck566 AlignedValid.nil

def missing567_568 : List (BitVec (edgeCount 11)) :=
  [missing567]
abbrev records567_568 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record567]
theorem aligned567_568 :
    AlignedValid 11 3 missing567_568 records567_568 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check567
    maskCheck567 AlignedValid.nil

def missing566_568 : List (BitVec (edgeCount 11)) :=
  missing566_567 ++ missing567_568
abbrev records566_568 : List Blob :=
  records566_567 ++ records567_568
theorem aligned566_568 :
    AlignedValid 11 3 missing566_568 records566_568 :=
  aligned566_567.append aligned567_568

def missing564_568 : List (BitVec (edgeCount 11)) :=
  missing564_566 ++ missing566_568
abbrev records564_568 : List Blob :=
  records564_566 ++ records566_568
theorem aligned564_568 :
    AlignedValid 11 3 missing564_568 records564_568 :=
  aligned564_566.append aligned566_568

def missing560_568 : List (BitVec (edgeCount 11)) :=
  missing560_564 ++ missing564_568
abbrev records560_568 : List Blob :=
  records560_564 ++ records564_568
theorem aligned560_568 :
    AlignedValid 11 3 missing560_568 records560_568 :=
  aligned560_564.append aligned564_568

def missing568_569 : List (BitVec (edgeCount 11)) :=
  [missing568]
abbrev records568_569 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record568]
theorem aligned568_569 :
    AlignedValid 11 3 missing568_569 records568_569 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check568
    maskCheck568 AlignedValid.nil

def missing569_570 : List (BitVec (edgeCount 11)) :=
  [missing569]
abbrev records569_570 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record569]
theorem aligned569_570 :
    AlignedValid 11 3 missing569_570 records569_570 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check569
    maskCheck569 AlignedValid.nil

def missing568_570 : List (BitVec (edgeCount 11)) :=
  missing568_569 ++ missing569_570
abbrev records568_570 : List Blob :=
  records568_569 ++ records569_570
theorem aligned568_570 :
    AlignedValid 11 3 missing568_570 records568_570 :=
  aligned568_569.append aligned569_570

def missing570_571 : List (BitVec (edgeCount 11)) :=
  [missing570]
abbrev records570_571 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record570]
theorem aligned570_571 :
    AlignedValid 11 3 missing570_571 records570_571 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check570
    maskCheck570 AlignedValid.nil

def missing571_572 : List (BitVec (edgeCount 11)) :=
  [missing571]
abbrev records571_572 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record571]
theorem aligned571_572 :
    AlignedValid 11 3 missing571_572 records571_572 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check571
    maskCheck571 AlignedValid.nil

def missing570_572 : List (BitVec (edgeCount 11)) :=
  missing570_571 ++ missing571_572
abbrev records570_572 : List Blob :=
  records570_571 ++ records571_572
theorem aligned570_572 :
    AlignedValid 11 3 missing570_572 records570_572 :=
  aligned570_571.append aligned571_572

def missing568_572 : List (BitVec (edgeCount 11)) :=
  missing568_570 ++ missing570_572
abbrev records568_572 : List Blob :=
  records568_570 ++ records570_572
theorem aligned568_572 :
    AlignedValid 11 3 missing568_572 records568_572 :=
  aligned568_570.append aligned570_572

def missing572_573 : List (BitVec (edgeCount 11)) :=
  [missing572]
abbrev records572_573 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record572]
theorem aligned572_573 :
    AlignedValid 11 3 missing572_573 records572_573 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check572
    maskCheck572 AlignedValid.nil

def missing573_574 : List (BitVec (edgeCount 11)) :=
  [missing573]
abbrev records573_574 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record573]
theorem aligned573_574 :
    AlignedValid 11 3 missing573_574 records573_574 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check573
    maskCheck573 AlignedValid.nil

def missing572_574 : List (BitVec (edgeCount 11)) :=
  missing572_573 ++ missing573_574
abbrev records572_574 : List Blob :=
  records572_573 ++ records573_574
theorem aligned572_574 :
    AlignedValid 11 3 missing572_574 records572_574 :=
  aligned572_573.append aligned573_574

def missing574_575 : List (BitVec (edgeCount 11)) :=
  [missing574]
abbrev records574_575 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record574]
theorem aligned574_575 :
    AlignedValid 11 3 missing574_575 records574_575 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check574
    maskCheck574 AlignedValid.nil

def missing575_576 : List (BitVec (edgeCount 11)) :=
  [missing575]
abbrev records575_576 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record575]
theorem aligned575_576 :
    AlignedValid 11 3 missing575_576 records575_576 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check575
    maskCheck575 AlignedValid.nil

def missing574_576 : List (BitVec (edgeCount 11)) :=
  missing574_575 ++ missing575_576
abbrev records574_576 : List Blob :=
  records574_575 ++ records575_576
theorem aligned574_576 :
    AlignedValid 11 3 missing574_576 records574_576 :=
  aligned574_575.append aligned575_576

def missing572_576 : List (BitVec (edgeCount 11)) :=
  missing572_574 ++ missing574_576
abbrev records572_576 : List Blob :=
  records572_574 ++ records574_576
theorem aligned572_576 :
    AlignedValid 11 3 missing572_576 records572_576 :=
  aligned572_574.append aligned574_576

def missing568_576 : List (BitVec (edgeCount 11)) :=
  missing568_572 ++ missing572_576
abbrev records568_576 : List Blob :=
  records568_572 ++ records572_576
theorem aligned568_576 :
    AlignedValid 11 3 missing568_576 records568_576 :=
  aligned568_572.append aligned572_576

def missing560_576 : List (BitVec (edgeCount 11)) :=
  missing560_568 ++ missing568_576
abbrev records560_576 : List Blob :=
  records560_568 ++ records568_576
theorem aligned560_576 :
    AlignedValid 11 3 missing560_576 records560_576 :=
  aligned560_568.append aligned568_576

def missing544_576 : List (BitVec (edgeCount 11)) :=
  missing544_560 ++ missing560_576
abbrev records544_576 : List Blob :=
  records544_560 ++ records560_576
theorem aligned544_576 :
    AlignedValid 11 3 missing544_576 records544_576 :=
  aligned544_560.append aligned560_576

def missing512_576 : List (BitVec (edgeCount 11)) :=
  missing512_544 ++ missing544_576
abbrev records512_576 : List Blob :=
  records512_544 ++ records544_576
theorem aligned512_576 :
    AlignedValid 11 3 missing512_576 records512_576 :=
  aligned512_544.append aligned544_576

def missing576_577 : List (BitVec (edgeCount 11)) :=
  [missing576]
abbrev records576_577 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record576]
theorem aligned576_577 :
    AlignedValid 11 3 missing576_577 records576_577 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check576
    maskCheck576 AlignedValid.nil

def missing577_578 : List (BitVec (edgeCount 11)) :=
  [missing577]
abbrev records577_578 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record577]
theorem aligned577_578 :
    AlignedValid 11 3 missing577_578 records577_578 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check577
    maskCheck577 AlignedValid.nil

def missing576_578 : List (BitVec (edgeCount 11)) :=
  missing576_577 ++ missing577_578
abbrev records576_578 : List Blob :=
  records576_577 ++ records577_578
theorem aligned576_578 :
    AlignedValid 11 3 missing576_578 records576_578 :=
  aligned576_577.append aligned577_578

def missing578_579 : List (BitVec (edgeCount 11)) :=
  [missing578]
abbrev records578_579 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record578]
theorem aligned578_579 :
    AlignedValid 11 3 missing578_579 records578_579 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check578
    maskCheck578 AlignedValid.nil

def missing579_580 : List (BitVec (edgeCount 11)) :=
  [missing579]
abbrev records579_580 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record579]
theorem aligned579_580 :
    AlignedValid 11 3 missing579_580 records579_580 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check579
    maskCheck579 AlignedValid.nil

def missing578_580 : List (BitVec (edgeCount 11)) :=
  missing578_579 ++ missing579_580
abbrev records578_580 : List Blob :=
  records578_579 ++ records579_580
theorem aligned578_580 :
    AlignedValid 11 3 missing578_580 records578_580 :=
  aligned578_579.append aligned579_580

def missing576_580 : List (BitVec (edgeCount 11)) :=
  missing576_578 ++ missing578_580
abbrev records576_580 : List Blob :=
  records576_578 ++ records578_580
theorem aligned576_580 :
    AlignedValid 11 3 missing576_580 records576_580 :=
  aligned576_578.append aligned578_580

def missing580_581 : List (BitVec (edgeCount 11)) :=
  [missing580]
abbrev records580_581 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record580]
theorem aligned580_581 :
    AlignedValid 11 3 missing580_581 records580_581 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check580
    maskCheck580 AlignedValid.nil

def missing581_582 : List (BitVec (edgeCount 11)) :=
  [missing581]
abbrev records581_582 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record581]
theorem aligned581_582 :
    AlignedValid 11 3 missing581_582 records581_582 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check581
    maskCheck581 AlignedValid.nil

def missing580_582 : List (BitVec (edgeCount 11)) :=
  missing580_581 ++ missing581_582
abbrev records580_582 : List Blob :=
  records580_581 ++ records581_582
theorem aligned580_582 :
    AlignedValid 11 3 missing580_582 records580_582 :=
  aligned580_581.append aligned581_582

def missing582_583 : List (BitVec (edgeCount 11)) :=
  [missing582]
abbrev records582_583 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record582]
theorem aligned582_583 :
    AlignedValid 11 3 missing582_583 records582_583 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check582
    maskCheck582 AlignedValid.nil

def missing583_584 : List (BitVec (edgeCount 11)) :=
  [missing583]
abbrev records583_584 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record583]
theorem aligned583_584 :
    AlignedValid 11 3 missing583_584 records583_584 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check583
    maskCheck583 AlignedValid.nil

def missing582_584 : List (BitVec (edgeCount 11)) :=
  missing582_583 ++ missing583_584
abbrev records582_584 : List Blob :=
  records582_583 ++ records583_584
theorem aligned582_584 :
    AlignedValid 11 3 missing582_584 records582_584 :=
  aligned582_583.append aligned583_584

def missing580_584 : List (BitVec (edgeCount 11)) :=
  missing580_582 ++ missing582_584
abbrev records580_584 : List Blob :=
  records580_582 ++ records582_584
theorem aligned580_584 :
    AlignedValid 11 3 missing580_584 records580_584 :=
  aligned580_582.append aligned582_584

def missing576_584 : List (BitVec (edgeCount 11)) :=
  missing576_580 ++ missing580_584
abbrev records576_584 : List Blob :=
  records576_580 ++ records580_584
theorem aligned576_584 :
    AlignedValid 11 3 missing576_584 records576_584 :=
  aligned576_580.append aligned580_584

def missing584_585 : List (BitVec (edgeCount 11)) :=
  [missing584]
abbrev records584_585 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record584]
theorem aligned584_585 :
    AlignedValid 11 3 missing584_585 records584_585 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check584
    maskCheck584 AlignedValid.nil

def missing585_586 : List (BitVec (edgeCount 11)) :=
  [missing585]
abbrev records585_586 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record585]
theorem aligned585_586 :
    AlignedValid 11 3 missing585_586 records585_586 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check585
    maskCheck585 AlignedValid.nil

def missing584_586 : List (BitVec (edgeCount 11)) :=
  missing584_585 ++ missing585_586
abbrev records584_586 : List Blob :=
  records584_585 ++ records585_586
theorem aligned584_586 :
    AlignedValid 11 3 missing584_586 records584_586 :=
  aligned584_585.append aligned585_586

def missing586_587 : List (BitVec (edgeCount 11)) :=
  [missing586]
abbrev records586_587 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record586]
theorem aligned586_587 :
    AlignedValid 11 3 missing586_587 records586_587 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check586
    maskCheck586 AlignedValid.nil

def missing587_588 : List (BitVec (edgeCount 11)) :=
  [missing587]
abbrev records587_588 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record587]
theorem aligned587_588 :
    AlignedValid 11 3 missing587_588 records587_588 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check587
    maskCheck587 AlignedValid.nil

def missing586_588 : List (BitVec (edgeCount 11)) :=
  missing586_587 ++ missing587_588
abbrev records586_588 : List Blob :=
  records586_587 ++ records587_588
theorem aligned586_588 :
    AlignedValid 11 3 missing586_588 records586_588 :=
  aligned586_587.append aligned587_588

def missing584_588 : List (BitVec (edgeCount 11)) :=
  missing584_586 ++ missing586_588
abbrev records584_588 : List Blob :=
  records584_586 ++ records586_588
theorem aligned584_588 :
    AlignedValid 11 3 missing584_588 records584_588 :=
  aligned584_586.append aligned586_588

def missing588_589 : List (BitVec (edgeCount 11)) :=
  [missing588]
abbrev records588_589 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record588]
theorem aligned588_589 :
    AlignedValid 11 3 missing588_589 records588_589 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check588
    maskCheck588 AlignedValid.nil

def missing589_590 : List (BitVec (edgeCount 11)) :=
  [missing589]
abbrev records589_590 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record589]
theorem aligned589_590 :
    AlignedValid 11 3 missing589_590 records589_590 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check589
    maskCheck589 AlignedValid.nil

def missing588_590 : List (BitVec (edgeCount 11)) :=
  missing588_589 ++ missing589_590
abbrev records588_590 : List Blob :=
  records588_589 ++ records589_590
theorem aligned588_590 :
    AlignedValid 11 3 missing588_590 records588_590 :=
  aligned588_589.append aligned589_590

def missing590_591 : List (BitVec (edgeCount 11)) :=
  [missing590]
abbrev records590_591 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record590]
theorem aligned590_591 :
    AlignedValid 11 3 missing590_591 records590_591 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check590
    maskCheck590 AlignedValid.nil

def missing591_592 : List (BitVec (edgeCount 11)) :=
  [missing591]
abbrev records591_592 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record591]
theorem aligned591_592 :
    AlignedValid 11 3 missing591_592 records591_592 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check591
    maskCheck591 AlignedValid.nil

def missing590_592 : List (BitVec (edgeCount 11)) :=
  missing590_591 ++ missing591_592
abbrev records590_592 : List Blob :=
  records590_591 ++ records591_592
theorem aligned590_592 :
    AlignedValid 11 3 missing590_592 records590_592 :=
  aligned590_591.append aligned591_592

def missing588_592 : List (BitVec (edgeCount 11)) :=
  missing588_590 ++ missing590_592
abbrev records588_592 : List Blob :=
  records588_590 ++ records590_592
theorem aligned588_592 :
    AlignedValid 11 3 missing588_592 records588_592 :=
  aligned588_590.append aligned590_592

def missing584_592 : List (BitVec (edgeCount 11)) :=
  missing584_588 ++ missing588_592
abbrev records584_592 : List Blob :=
  records584_588 ++ records588_592
theorem aligned584_592 :
    AlignedValid 11 3 missing584_592 records584_592 :=
  aligned584_588.append aligned588_592

def missing576_592 : List (BitVec (edgeCount 11)) :=
  missing576_584 ++ missing584_592
abbrev records576_592 : List Blob :=
  records576_584 ++ records584_592
theorem aligned576_592 :
    AlignedValid 11 3 missing576_592 records576_592 :=
  aligned576_584.append aligned584_592

def missing592_593 : List (BitVec (edgeCount 11)) :=
  [missing592]
abbrev records592_593 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record592]
theorem aligned592_593 :
    AlignedValid 11 3 missing592_593 records592_593 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check592
    maskCheck592 AlignedValid.nil

def missing593_594 : List (BitVec (edgeCount 11)) :=
  [missing593]
abbrev records593_594 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record593]
theorem aligned593_594 :
    AlignedValid 11 3 missing593_594 records593_594 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check593
    maskCheck593 AlignedValid.nil

def missing592_594 : List (BitVec (edgeCount 11)) :=
  missing592_593 ++ missing593_594
abbrev records592_594 : List Blob :=
  records592_593 ++ records593_594
theorem aligned592_594 :
    AlignedValid 11 3 missing592_594 records592_594 :=
  aligned592_593.append aligned593_594

def missing594_595 : List (BitVec (edgeCount 11)) :=
  [missing594]
abbrev records594_595 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record594]
theorem aligned594_595 :
    AlignedValid 11 3 missing594_595 records594_595 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check594
    maskCheck594 AlignedValid.nil

def missing595_596 : List (BitVec (edgeCount 11)) :=
  [missing595]
abbrev records595_596 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record595]
theorem aligned595_596 :
    AlignedValid 11 3 missing595_596 records595_596 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check595
    maskCheck595 AlignedValid.nil

def missing594_596 : List (BitVec (edgeCount 11)) :=
  missing594_595 ++ missing595_596
abbrev records594_596 : List Blob :=
  records594_595 ++ records595_596
theorem aligned594_596 :
    AlignedValid 11 3 missing594_596 records594_596 :=
  aligned594_595.append aligned595_596

def missing592_596 : List (BitVec (edgeCount 11)) :=
  missing592_594 ++ missing594_596
abbrev records592_596 : List Blob :=
  records592_594 ++ records594_596
theorem aligned592_596 :
    AlignedValid 11 3 missing592_596 records592_596 :=
  aligned592_594.append aligned594_596

def missing596_597 : List (BitVec (edgeCount 11)) :=
  [missing596]
abbrev records596_597 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record596]
theorem aligned596_597 :
    AlignedValid 11 3 missing596_597 records596_597 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check596
    maskCheck596 AlignedValid.nil

def missing597_598 : List (BitVec (edgeCount 11)) :=
  [missing597]
abbrev records597_598 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record597]
theorem aligned597_598 :
    AlignedValid 11 3 missing597_598 records597_598 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check597
    maskCheck597 AlignedValid.nil

def missing596_598 : List (BitVec (edgeCount 11)) :=
  missing596_597 ++ missing597_598
abbrev records596_598 : List Blob :=
  records596_597 ++ records597_598
theorem aligned596_598 :
    AlignedValid 11 3 missing596_598 records596_598 :=
  aligned596_597.append aligned597_598

def missing598_599 : List (BitVec (edgeCount 11)) :=
  [missing598]
abbrev records598_599 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record598]
theorem aligned598_599 :
    AlignedValid 11 3 missing598_599 records598_599 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check598
    maskCheck598 AlignedValid.nil

def missing599_600 : List (BitVec (edgeCount 11)) :=
  [missing599]
abbrev records599_600 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record599]
theorem aligned599_600 :
    AlignedValid 11 3 missing599_600 records599_600 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check599
    maskCheck599 AlignedValid.nil

def missing598_600 : List (BitVec (edgeCount 11)) :=
  missing598_599 ++ missing599_600
abbrev records598_600 : List Blob :=
  records598_599 ++ records599_600
theorem aligned598_600 :
    AlignedValid 11 3 missing598_600 records598_600 :=
  aligned598_599.append aligned599_600

def missing596_600 : List (BitVec (edgeCount 11)) :=
  missing596_598 ++ missing598_600
abbrev records596_600 : List Blob :=
  records596_598 ++ records598_600
theorem aligned596_600 :
    AlignedValid 11 3 missing596_600 records596_600 :=
  aligned596_598.append aligned598_600

def missing592_600 : List (BitVec (edgeCount 11)) :=
  missing592_596 ++ missing596_600
abbrev records592_600 : List Blob :=
  records592_596 ++ records596_600
theorem aligned592_600 :
    AlignedValid 11 3 missing592_600 records592_600 :=
  aligned592_596.append aligned596_600

def missing600_601 : List (BitVec (edgeCount 11)) :=
  [missing600]
abbrev records600_601 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record600]
theorem aligned600_601 :
    AlignedValid 11 3 missing600_601 records600_601 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check600
    maskCheck600 AlignedValid.nil

def missing601_602 : List (BitVec (edgeCount 11)) :=
  [missing601]
abbrev records601_602 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record601]
theorem aligned601_602 :
    AlignedValid 11 3 missing601_602 records601_602 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check601
    maskCheck601 AlignedValid.nil

def missing600_602 : List (BitVec (edgeCount 11)) :=
  missing600_601 ++ missing601_602
abbrev records600_602 : List Blob :=
  records600_601 ++ records601_602
theorem aligned600_602 :
    AlignedValid 11 3 missing600_602 records600_602 :=
  aligned600_601.append aligned601_602

def missing602_603 : List (BitVec (edgeCount 11)) :=
  [missing602]
abbrev records602_603 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record602]
theorem aligned602_603 :
    AlignedValid 11 3 missing602_603 records602_603 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check602
    maskCheck602 AlignedValid.nil

def missing603_604 : List (BitVec (edgeCount 11)) :=
  [missing603]
abbrev records603_604 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record603]
theorem aligned603_604 :
    AlignedValid 11 3 missing603_604 records603_604 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check603
    maskCheck603 AlignedValid.nil

def missing602_604 : List (BitVec (edgeCount 11)) :=
  missing602_603 ++ missing603_604
abbrev records602_604 : List Blob :=
  records602_603 ++ records603_604
theorem aligned602_604 :
    AlignedValid 11 3 missing602_604 records602_604 :=
  aligned602_603.append aligned603_604

def missing600_604 : List (BitVec (edgeCount 11)) :=
  missing600_602 ++ missing602_604
abbrev records600_604 : List Blob :=
  records600_602 ++ records602_604
theorem aligned600_604 :
    AlignedValid 11 3 missing600_604 records600_604 :=
  aligned600_602.append aligned602_604

def missing604_605 : List (BitVec (edgeCount 11)) :=
  [missing604]
abbrev records604_605 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record604]
theorem aligned604_605 :
    AlignedValid 11 3 missing604_605 records604_605 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check604
    maskCheck604 AlignedValid.nil

def missing605_606 : List (BitVec (edgeCount 11)) :=
  [missing605]
abbrev records605_606 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record605]
theorem aligned605_606 :
    AlignedValid 11 3 missing605_606 records605_606 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check605
    maskCheck605 AlignedValid.nil

def missing604_606 : List (BitVec (edgeCount 11)) :=
  missing604_605 ++ missing605_606
abbrev records604_606 : List Blob :=
  records604_605 ++ records605_606
theorem aligned604_606 :
    AlignedValid 11 3 missing604_606 records604_606 :=
  aligned604_605.append aligned605_606

def missing606_607 : List (BitVec (edgeCount 11)) :=
  [missing606]
abbrev records606_607 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record606]
theorem aligned606_607 :
    AlignedValid 11 3 missing606_607 records606_607 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check606
    maskCheck606 AlignedValid.nil

def missing607_608 : List (BitVec (edgeCount 11)) :=
  [missing607]
abbrev records607_608 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record607]
theorem aligned607_608 :
    AlignedValid 11 3 missing607_608 records607_608 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check607
    maskCheck607 AlignedValid.nil

def missing606_608 : List (BitVec (edgeCount 11)) :=
  missing606_607 ++ missing607_608
abbrev records606_608 : List Blob :=
  records606_607 ++ records607_608
theorem aligned606_608 :
    AlignedValid 11 3 missing606_608 records606_608 :=
  aligned606_607.append aligned607_608

def missing604_608 : List (BitVec (edgeCount 11)) :=
  missing604_606 ++ missing606_608
abbrev records604_608 : List Blob :=
  records604_606 ++ records606_608
theorem aligned604_608 :
    AlignedValid 11 3 missing604_608 records604_608 :=
  aligned604_606.append aligned606_608

def missing600_608 : List (BitVec (edgeCount 11)) :=
  missing600_604 ++ missing604_608
abbrev records600_608 : List Blob :=
  records600_604 ++ records604_608
theorem aligned600_608 :
    AlignedValid 11 3 missing600_608 records600_608 :=
  aligned600_604.append aligned604_608

def missing592_608 : List (BitVec (edgeCount 11)) :=
  missing592_600 ++ missing600_608
abbrev records592_608 : List Blob :=
  records592_600 ++ records600_608
theorem aligned592_608 :
    AlignedValid 11 3 missing592_608 records592_608 :=
  aligned592_600.append aligned600_608

def missing576_608 : List (BitVec (edgeCount 11)) :=
  missing576_592 ++ missing592_608
abbrev records576_608 : List Blob :=
  records576_592 ++ records592_608
theorem aligned576_608 :
    AlignedValid 11 3 missing576_608 records576_608 :=
  aligned576_592.append aligned592_608

def missing608_609 : List (BitVec (edgeCount 11)) :=
  [missing608]
abbrev records608_609 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record608]
theorem aligned608_609 :
    AlignedValid 11 3 missing608_609 records608_609 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check608
    maskCheck608 AlignedValid.nil

def missing609_610 : List (BitVec (edgeCount 11)) :=
  [missing609]
abbrev records609_610 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record609]
theorem aligned609_610 :
    AlignedValid 11 3 missing609_610 records609_610 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check609
    maskCheck609 AlignedValid.nil

def missing608_610 : List (BitVec (edgeCount 11)) :=
  missing608_609 ++ missing609_610
abbrev records608_610 : List Blob :=
  records608_609 ++ records609_610
theorem aligned608_610 :
    AlignedValid 11 3 missing608_610 records608_610 :=
  aligned608_609.append aligned609_610

def missing610_611 : List (BitVec (edgeCount 11)) :=
  [missing610]
abbrev records610_611 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record610]
theorem aligned610_611 :
    AlignedValid 11 3 missing610_611 records610_611 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check610
    maskCheck610 AlignedValid.nil

def missing611_612 : List (BitVec (edgeCount 11)) :=
  [missing611]
abbrev records611_612 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record611]
theorem aligned611_612 :
    AlignedValid 11 3 missing611_612 records611_612 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check611
    maskCheck611 AlignedValid.nil

def missing610_612 : List (BitVec (edgeCount 11)) :=
  missing610_611 ++ missing611_612
abbrev records610_612 : List Blob :=
  records610_611 ++ records611_612
theorem aligned610_612 :
    AlignedValid 11 3 missing610_612 records610_612 :=
  aligned610_611.append aligned611_612

def missing608_612 : List (BitVec (edgeCount 11)) :=
  missing608_610 ++ missing610_612
abbrev records608_612 : List Blob :=
  records608_610 ++ records610_612
theorem aligned608_612 :
    AlignedValid 11 3 missing608_612 records608_612 :=
  aligned608_610.append aligned610_612

def missing612_613 : List (BitVec (edgeCount 11)) :=
  [missing612]
abbrev records612_613 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record612]
theorem aligned612_613 :
    AlignedValid 11 3 missing612_613 records612_613 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check612
    maskCheck612 AlignedValid.nil

def missing613_614 : List (BitVec (edgeCount 11)) :=
  [missing613]
abbrev records613_614 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record613]
theorem aligned613_614 :
    AlignedValid 11 3 missing613_614 records613_614 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check613
    maskCheck613 AlignedValid.nil

def missing612_614 : List (BitVec (edgeCount 11)) :=
  missing612_613 ++ missing613_614
abbrev records612_614 : List Blob :=
  records612_613 ++ records613_614
theorem aligned612_614 :
    AlignedValid 11 3 missing612_614 records612_614 :=
  aligned612_613.append aligned613_614

def missing614_615 : List (BitVec (edgeCount 11)) :=
  [missing614]
abbrev records614_615 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record614]
theorem aligned614_615 :
    AlignedValid 11 3 missing614_615 records614_615 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check614
    maskCheck614 AlignedValid.nil

def missing615_616 : List (BitVec (edgeCount 11)) :=
  [missing615]
abbrev records615_616 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record615]
theorem aligned615_616 :
    AlignedValid 11 3 missing615_616 records615_616 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check615
    maskCheck615 AlignedValid.nil

def missing614_616 : List (BitVec (edgeCount 11)) :=
  missing614_615 ++ missing615_616
abbrev records614_616 : List Blob :=
  records614_615 ++ records615_616
theorem aligned614_616 :
    AlignedValid 11 3 missing614_616 records614_616 :=
  aligned614_615.append aligned615_616

def missing612_616 : List (BitVec (edgeCount 11)) :=
  missing612_614 ++ missing614_616
abbrev records612_616 : List Blob :=
  records612_614 ++ records614_616
theorem aligned612_616 :
    AlignedValid 11 3 missing612_616 records612_616 :=
  aligned612_614.append aligned614_616

def missing608_616 : List (BitVec (edgeCount 11)) :=
  missing608_612 ++ missing612_616
abbrev records608_616 : List Blob :=
  records608_612 ++ records612_616
theorem aligned608_616 :
    AlignedValid 11 3 missing608_616 records608_616 :=
  aligned608_612.append aligned612_616

def missing616_617 : List (BitVec (edgeCount 11)) :=
  [missing616]
abbrev records616_617 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record616]
theorem aligned616_617 :
    AlignedValid 11 3 missing616_617 records616_617 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check616
    maskCheck616 AlignedValid.nil

def missing617_618 : List (BitVec (edgeCount 11)) :=
  [missing617]
abbrev records617_618 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record617]
theorem aligned617_618 :
    AlignedValid 11 3 missing617_618 records617_618 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check617
    maskCheck617 AlignedValid.nil

def missing616_618 : List (BitVec (edgeCount 11)) :=
  missing616_617 ++ missing617_618
abbrev records616_618 : List Blob :=
  records616_617 ++ records617_618
theorem aligned616_618 :
    AlignedValid 11 3 missing616_618 records616_618 :=
  aligned616_617.append aligned617_618

def missing618_619 : List (BitVec (edgeCount 11)) :=
  [missing618]
abbrev records618_619 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record618]
theorem aligned618_619 :
    AlignedValid 11 3 missing618_619 records618_619 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check618
    maskCheck618 AlignedValid.nil

def missing619_620 : List (BitVec (edgeCount 11)) :=
  [missing619]
abbrev records619_620 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record619]
theorem aligned619_620 :
    AlignedValid 11 3 missing619_620 records619_620 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check619
    maskCheck619 AlignedValid.nil

def missing618_620 : List (BitVec (edgeCount 11)) :=
  missing618_619 ++ missing619_620
abbrev records618_620 : List Blob :=
  records618_619 ++ records619_620
theorem aligned618_620 :
    AlignedValid 11 3 missing618_620 records618_620 :=
  aligned618_619.append aligned619_620

def missing616_620 : List (BitVec (edgeCount 11)) :=
  missing616_618 ++ missing618_620
abbrev records616_620 : List Blob :=
  records616_618 ++ records618_620
theorem aligned616_620 :
    AlignedValid 11 3 missing616_620 records616_620 :=
  aligned616_618.append aligned618_620

def missing620_621 : List (BitVec (edgeCount 11)) :=
  [missing620]
abbrev records620_621 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record620]
theorem aligned620_621 :
    AlignedValid 11 3 missing620_621 records620_621 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check620
    maskCheck620 AlignedValid.nil

def missing621_622 : List (BitVec (edgeCount 11)) :=
  [missing621]
abbrev records621_622 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record621]
theorem aligned621_622 :
    AlignedValid 11 3 missing621_622 records621_622 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check621
    maskCheck621 AlignedValid.nil

def missing620_622 : List (BitVec (edgeCount 11)) :=
  missing620_621 ++ missing621_622
abbrev records620_622 : List Blob :=
  records620_621 ++ records621_622
theorem aligned620_622 :
    AlignedValid 11 3 missing620_622 records620_622 :=
  aligned620_621.append aligned621_622

def missing622_623 : List (BitVec (edgeCount 11)) :=
  [missing622]
abbrev records622_623 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record622]
theorem aligned622_623 :
    AlignedValid 11 3 missing622_623 records622_623 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check622
    maskCheck622 AlignedValid.nil

def missing623_624 : List (BitVec (edgeCount 11)) :=
  [missing623]
abbrev records623_624 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record623]
theorem aligned623_624 :
    AlignedValid 11 3 missing623_624 records623_624 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check623
    maskCheck623 AlignedValid.nil

def missing622_624 : List (BitVec (edgeCount 11)) :=
  missing622_623 ++ missing623_624
abbrev records622_624 : List Blob :=
  records622_623 ++ records623_624
theorem aligned622_624 :
    AlignedValid 11 3 missing622_624 records622_624 :=
  aligned622_623.append aligned623_624

def missing620_624 : List (BitVec (edgeCount 11)) :=
  missing620_622 ++ missing622_624
abbrev records620_624 : List Blob :=
  records620_622 ++ records622_624
theorem aligned620_624 :
    AlignedValid 11 3 missing620_624 records620_624 :=
  aligned620_622.append aligned622_624

def missing616_624 : List (BitVec (edgeCount 11)) :=
  missing616_620 ++ missing620_624
abbrev records616_624 : List Blob :=
  records616_620 ++ records620_624
theorem aligned616_624 :
    AlignedValid 11 3 missing616_624 records616_624 :=
  aligned616_620.append aligned620_624

def missing608_624 : List (BitVec (edgeCount 11)) :=
  missing608_616 ++ missing616_624
abbrev records608_624 : List Blob :=
  records608_616 ++ records616_624
theorem aligned608_624 :
    AlignedValid 11 3 missing608_624 records608_624 :=
  aligned608_616.append aligned616_624

def missing624_625 : List (BitVec (edgeCount 11)) :=
  [missing624]
abbrev records624_625 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record624]
theorem aligned624_625 :
    AlignedValid 11 3 missing624_625 records624_625 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check624
    maskCheck624 AlignedValid.nil

def missing625_626 : List (BitVec (edgeCount 11)) :=
  [missing625]
abbrev records625_626 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record625]
theorem aligned625_626 :
    AlignedValid 11 3 missing625_626 records625_626 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check625
    maskCheck625 AlignedValid.nil

def missing624_626 : List (BitVec (edgeCount 11)) :=
  missing624_625 ++ missing625_626
abbrev records624_626 : List Blob :=
  records624_625 ++ records625_626
theorem aligned624_626 :
    AlignedValid 11 3 missing624_626 records624_626 :=
  aligned624_625.append aligned625_626

def missing626_627 : List (BitVec (edgeCount 11)) :=
  [missing626]
abbrev records626_627 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record626]
theorem aligned626_627 :
    AlignedValid 11 3 missing626_627 records626_627 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check626
    maskCheck626 AlignedValid.nil

def missing627_628 : List (BitVec (edgeCount 11)) :=
  [missing627]
abbrev records627_628 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record627]
theorem aligned627_628 :
    AlignedValid 11 3 missing627_628 records627_628 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check627
    maskCheck627 AlignedValid.nil

def missing626_628 : List (BitVec (edgeCount 11)) :=
  missing626_627 ++ missing627_628
abbrev records626_628 : List Blob :=
  records626_627 ++ records627_628
theorem aligned626_628 :
    AlignedValid 11 3 missing626_628 records626_628 :=
  aligned626_627.append aligned627_628

def missing624_628 : List (BitVec (edgeCount 11)) :=
  missing624_626 ++ missing626_628
abbrev records624_628 : List Blob :=
  records624_626 ++ records626_628
theorem aligned624_628 :
    AlignedValid 11 3 missing624_628 records624_628 :=
  aligned624_626.append aligned626_628

def missing628_629 : List (BitVec (edgeCount 11)) :=
  [missing628]
abbrev records628_629 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record628]
theorem aligned628_629 :
    AlignedValid 11 3 missing628_629 records628_629 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check628
    maskCheck628 AlignedValid.nil

def missing629_630 : List (BitVec (edgeCount 11)) :=
  [missing629]
abbrev records629_630 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record629]
theorem aligned629_630 :
    AlignedValid 11 3 missing629_630 records629_630 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check629
    maskCheck629 AlignedValid.nil

def missing628_630 : List (BitVec (edgeCount 11)) :=
  missing628_629 ++ missing629_630
abbrev records628_630 : List Blob :=
  records628_629 ++ records629_630
theorem aligned628_630 :
    AlignedValid 11 3 missing628_630 records628_630 :=
  aligned628_629.append aligned629_630

def missing630_631 : List (BitVec (edgeCount 11)) :=
  [missing630]
abbrev records630_631 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record630]
theorem aligned630_631 :
    AlignedValid 11 3 missing630_631 records630_631 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check630
    maskCheck630 AlignedValid.nil

def missing631_632 : List (BitVec (edgeCount 11)) :=
  [missing631]
abbrev records631_632 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record631]
theorem aligned631_632 :
    AlignedValid 11 3 missing631_632 records631_632 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check631
    maskCheck631 AlignedValid.nil

def missing630_632 : List (BitVec (edgeCount 11)) :=
  missing630_631 ++ missing631_632
abbrev records630_632 : List Blob :=
  records630_631 ++ records631_632
theorem aligned630_632 :
    AlignedValid 11 3 missing630_632 records630_632 :=
  aligned630_631.append aligned631_632

def missing628_632 : List (BitVec (edgeCount 11)) :=
  missing628_630 ++ missing630_632
abbrev records628_632 : List Blob :=
  records628_630 ++ records630_632
theorem aligned628_632 :
    AlignedValid 11 3 missing628_632 records628_632 :=
  aligned628_630.append aligned630_632

def missing624_632 : List (BitVec (edgeCount 11)) :=
  missing624_628 ++ missing628_632
abbrev records624_632 : List Blob :=
  records624_628 ++ records628_632
theorem aligned624_632 :
    AlignedValid 11 3 missing624_632 records624_632 :=
  aligned624_628.append aligned628_632

def missing632_633 : List (BitVec (edgeCount 11)) :=
  [missing632]
abbrev records632_633 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record632]
theorem aligned632_633 :
    AlignedValid 11 3 missing632_633 records632_633 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check632
    maskCheck632 AlignedValid.nil

def missing633_634 : List (BitVec (edgeCount 11)) :=
  [missing633]
abbrev records633_634 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record633]
theorem aligned633_634 :
    AlignedValid 11 3 missing633_634 records633_634 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check633
    maskCheck633 AlignedValid.nil

def missing632_634 : List (BitVec (edgeCount 11)) :=
  missing632_633 ++ missing633_634
abbrev records632_634 : List Blob :=
  records632_633 ++ records633_634
theorem aligned632_634 :
    AlignedValid 11 3 missing632_634 records632_634 :=
  aligned632_633.append aligned633_634

def missing634_635 : List (BitVec (edgeCount 11)) :=
  [missing634]
abbrev records634_635 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record634]
theorem aligned634_635 :
    AlignedValid 11 3 missing634_635 records634_635 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check634
    maskCheck634 AlignedValid.nil

def missing635_636 : List (BitVec (edgeCount 11)) :=
  [missing635]
abbrev records635_636 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record635]
theorem aligned635_636 :
    AlignedValid 11 3 missing635_636 records635_636 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check635
    maskCheck635 AlignedValid.nil

def missing634_636 : List (BitVec (edgeCount 11)) :=
  missing634_635 ++ missing635_636
abbrev records634_636 : List Blob :=
  records634_635 ++ records635_636
theorem aligned634_636 :
    AlignedValid 11 3 missing634_636 records634_636 :=
  aligned634_635.append aligned635_636

def missing632_636 : List (BitVec (edgeCount 11)) :=
  missing632_634 ++ missing634_636
abbrev records632_636 : List Blob :=
  records632_634 ++ records634_636
theorem aligned632_636 :
    AlignedValid 11 3 missing632_636 records632_636 :=
  aligned632_634.append aligned634_636

def missing636_637 : List (BitVec (edgeCount 11)) :=
  [missing636]
abbrev records636_637 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record636]
theorem aligned636_637 :
    AlignedValid 11 3 missing636_637 records636_637 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check636
    maskCheck636 AlignedValid.nil

def missing637_638 : List (BitVec (edgeCount 11)) :=
  [missing637]
abbrev records637_638 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record637]
theorem aligned637_638 :
    AlignedValid 11 3 missing637_638 records637_638 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check637
    maskCheck637 AlignedValid.nil

def missing636_638 : List (BitVec (edgeCount 11)) :=
  missing636_637 ++ missing637_638
abbrev records636_638 : List Blob :=
  records636_637 ++ records637_638
theorem aligned636_638 :
    AlignedValid 11 3 missing636_638 records636_638 :=
  aligned636_637.append aligned637_638

def missing638_639 : List (BitVec (edgeCount 11)) :=
  [missing638]
abbrev records638_639 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record638]
theorem aligned638_639 :
    AlignedValid 11 3 missing638_639 records638_639 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check638
    maskCheck638 AlignedValid.nil

def missing639_640 : List (BitVec (edgeCount 11)) :=
  [missing639]
abbrev records639_640 : List Blob :=
  [StrongPackedBucketN11A3Shard004.record639]
theorem aligned639_640 :
    AlignedValid 11 3 missing639_640 records639_640 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A3Shard004.check639
    maskCheck639 AlignedValid.nil

def missing638_640 : List (BitVec (edgeCount 11)) :=
  missing638_639 ++ missing639_640
abbrev records638_640 : List Blob :=
  records638_639 ++ records639_640
theorem aligned638_640 :
    AlignedValid 11 3 missing638_640 records638_640 :=
  aligned638_639.append aligned639_640

def missing636_640 : List (BitVec (edgeCount 11)) :=
  missing636_638 ++ missing638_640
abbrev records636_640 : List Blob :=
  records636_638 ++ records638_640
theorem aligned636_640 :
    AlignedValid 11 3 missing636_640 records636_640 :=
  aligned636_638.append aligned638_640

def missing632_640 : List (BitVec (edgeCount 11)) :=
  missing632_636 ++ missing636_640
abbrev records632_640 : List Blob :=
  records632_636 ++ records636_640
theorem aligned632_640 :
    AlignedValid 11 3 missing632_640 records632_640 :=
  aligned632_636.append aligned636_640

def missing624_640 : List (BitVec (edgeCount 11)) :=
  missing624_632 ++ missing632_640
abbrev records624_640 : List Blob :=
  records624_632 ++ records632_640
theorem aligned624_640 :
    AlignedValid 11 3 missing624_640 records624_640 :=
  aligned624_632.append aligned632_640

def missing608_640 : List (BitVec (edgeCount 11)) :=
  missing608_624 ++ missing624_640
abbrev records608_640 : List Blob :=
  records608_624 ++ records624_640
theorem aligned608_640 :
    AlignedValid 11 3 missing608_640 records608_640 :=
  aligned608_624.append aligned624_640

def missing576_640 : List (BitVec (edgeCount 11)) :=
  missing576_608 ++ missing608_640
abbrev records576_640 : List Blob :=
  records576_608 ++ records608_640
theorem aligned576_640 :
    AlignedValid 11 3 missing576_640 records576_640 :=
  aligned576_608.append aligned608_640

def missing512_640 : List (BitVec (edgeCount 11)) :=
  missing512_576 ++ missing576_640
abbrev records512_640 : List Blob :=
  records512_576 ++ records576_640
theorem aligned512_640 :
    AlignedValid 11 3 missing512_640 records512_640 :=
  aligned512_576.append aligned576_640

abbrev missing : List (BitVec (edgeCount 11)) :=
  missing512_640
abbrev records : List Blob := records512_640
theorem aligned : AlignedValid 11 3 missing records :=
  aligned512_640

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN11A3AlignedShard004

