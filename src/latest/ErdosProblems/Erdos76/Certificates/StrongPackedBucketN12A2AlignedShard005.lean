/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard005

/-! Decode-only alignment checks for n=12, a=2, records 640--767. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A2AlignedShard005

open PackedBucketCertificate

def missing640 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46585480973832421376
theorem maskCheck640 :
    checkMaskFor missing640 StrongPackedBucketN12A2Shard005.record640 = true := by
  decide

def missing641 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46621509770851385344
theorem maskCheck641 :
    checkMaskFor missing641 StrongPackedBucketN12A2Shard005.record641 = true := by
  decide

def missing642 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47017826538059988992
theorem maskCheck642 :
    checkMaskFor missing642 StrongPackedBucketN12A2Shard005.record642 = true := by
  decide

def missing643 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47053855335078952960
theorem maskCheck643 :
    checkMaskFor missing643 StrongPackedBucketN12A2Shard005.record643 = true := by
  decide

def missing644 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47125912929116880896
theorem maskCheck644 :
    checkMaskFor missing644 StrongPackedBucketN12A2Shard005.record644 = true := by
  decide

def missing645 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 48134719245647872000
theorem maskCheck645 :
    checkMaskFor missing645 StrongPackedBucketN12A2Shard005.record645 = true := by
  decide

def missing646 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64671937077352333312
theorem maskCheck646 :
    checkMaskFor missing646 StrongPackedBucketN12A2Shard005.record646 = true := by
  decide

def missing647 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64743994671390261248
theorem maskCheck647 :
    checkMaskFor missing647 StrongPackedBucketN12A2Shard005.record647 = true := by
  decide

def missing648 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64888109859466117120
theorem maskCheck648 :
    checkMaskFor missing648 StrongPackedBucketN12A2Shard005.record648 = true := by
  decide

def missing649 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64996196250523009024
theorem maskCheck649 :
    checkMaskFor missing649 StrongPackedBucketN12A2Shard005.record649 = true := by
  decide

def missing650 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 65428541814750576640
theorem maskCheck650 :
    checkMaskFor missing650 StrongPackedBucketN12A2Shard005.record650 = true := by
  decide

def missing651 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1117350242132426752
theorem maskCheck651 :
    checkMaskFor missing651 StrongPackedBucketN12A2Shard005.record651 = true := by
  decide

def missing652 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1982041370587561984
theorem maskCheck652 :
    checkMaskFor missing652 StrongPackedBucketN12A2Shard005.record652 = true := by
  decide

def missing653 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2198214152701345792
theorem maskCheck653 :
    checkMaskFor missing653 StrongPackedBucketN12A2Shard005.record653 = true := by
  decide

def missing654 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2234242949720309760
theorem maskCheck654 :
    checkMaskFor missing654 StrongPackedBucketN12A2Shard005.record654 = true := by
  decide

def missing655 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4143769191725400064
theorem maskCheck655 :
    checkMaskFor missing655 StrongPackedBucketN12A2Shard005.record655 = true := by
  decide

def missing656 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4215826785763328000
theorem maskCheck656 :
    checkMaskFor missing656 StrongPackedBucketN12A2Shard005.record656 = true := by
  decide

def missing657 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4251855582782291968
theorem maskCheck657 :
    checkMaskFor missing657 StrongPackedBucketN12A2Shard005.record657 = true := by
  decide

def missing658 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4468028364896075776
theorem maskCheck658 :
    checkMaskFor missing658 StrongPackedBucketN12A2Shard005.record658 = true := by
  decide

def missing659 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8683397616114860032
theorem maskCheck659 :
    checkMaskFor missing659 StrongPackedBucketN12A2Shard005.record659 = true := by
  decide

def missing660 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8719426413133824000
theorem maskCheck660 :
    checkMaskFor missing660 StrongPackedBucketN12A2Shard005.record660 = true := by
  decide

def missing661 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8791484007171751936
theorem maskCheck661 :
    checkMaskFor missing661 StrongPackedBucketN12A2Shard005.record661 = true := by
  decide

def missing662 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9764261526683779072
theorem maskCheck662 :
    checkMaskFor missing662 StrongPackedBucketN12A2Shard005.record662 = true := by
  decide

def missing663 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10052491902835490816
theorem maskCheck663 :
    checkMaskFor missing663 StrongPackedBucketN12A2Shard005.record663 = true := by
  decide

def missing664 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10268664684949274624
theorem maskCheck664 :
    checkMaskFor missing664 StrongPackedBucketN12A2Shard005.record664 = true := by
  decide

def missing665 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10304693481968238592
theorem maskCheck665 :
    checkMaskFor missing665 StrongPackedBucketN12A2Shard005.record665 = true := by
  decide

def missing666 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11061298219366481920
theorem maskCheck666 :
    checkMaskFor missing666 StrongPackedBucketN12A2Shard005.record666 = true := by
  decide

def missing667 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11133355813404409856
theorem maskCheck667 :
    checkMaskFor missing667 StrongPackedBucketN12A2Shard005.record667 = true := by
  decide

def missing668 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11169384610423373824
theorem maskCheck668 :
    checkMaskFor missing668 StrongPackedBucketN12A2Shard005.record668 = true := by
  decide

def missing669 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11385557392537157632
theorem maskCheck669 :
    checkMaskFor missing669 StrongPackedBucketN12A2Shard005.record669 = true := by
  decide

def missing670 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13295083634542247936
theorem maskCheck670 :
    checkMaskFor missing670 StrongPackedBucketN12A2Shard005.record670 = true := by
  decide

def missing671 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13331112431561211904
theorem maskCheck671 :
    checkMaskFor missing671 StrongPackedBucketN12A2Shard005.record671 = true := by
  decide

def missing672 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13403170025599139840
theorem maskCheck672 :
    checkMaskFor missing672 StrongPackedBucketN12A2Shard005.record672 = true := by
  decide

def missing673 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 17870740855950671872
theorem maskCheck673 :
    checkMaskFor missing673 StrongPackedBucketN12A2Shard005.record673 = true := by
  decide

def missing674 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18987633563538554880
theorem maskCheck674 :
    checkMaskFor missing674 StrongPackedBucketN12A2Shard005.record674 = true := by
  decide

def missing675 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19275863939690266624
theorem maskCheck675 :
    checkMaskFor missing675 StrongPackedBucketN12A2Shard005.record675 = true := by
  decide

def missing676 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19528065518823014400
theorem maskCheck676 :
    checkMaskFor missing676 StrongPackedBucketN12A2Shard005.record676 = true := by
  decide

def missing677 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20284670256221257728
theorem maskCheck677 :
    checkMaskFor missing677 StrongPackedBucketN12A2Shard005.record677 = true := by
  decide

def missing678 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20392756647278149632
theorem maskCheck678 :
    checkMaskFor missing678 StrongPackedBucketN12A2Shard005.record678 = true := by
  decide

def missing679 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22554484468415987712
theorem maskCheck679 :
    checkMaskFor missing679 StrongPackedBucketN12A2Shard005.record679 = true := by
  decide

def missing680 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27922775224241618944
theorem maskCheck680 :
    checkMaskFor missing680 StrongPackedBucketN12A2Shard005.record680 = true := by
  decide

def missing681 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28174976803374366720
theorem maskCheck681 :
    checkMaskFor missing681 StrongPackedBucketN12A2Shard005.record681 = true := by
  decide

def missing682 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28355120788469186560
theorem maskCheck682 :
    checkMaskFor missing682 StrongPackedBucketN12A2Shard005.record682 = true := by
  decide

def missing683 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28463207179526078464
theorem maskCheck683 :
    checkMaskFor missing683 StrongPackedBucketN12A2Shard005.record683 = true := by
  decide

def missing684 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29472013496057069568
theorem maskCheck684 :
    checkMaskFor missing684 StrongPackedBucketN12A2Shard005.record684 = true := by
  decide

def missing685 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37434377637248106496
theorem maskCheck685 :
    checkMaskFor missing685 StrongPackedBucketN12A2Shard005.record685 = true := by
  decide

def missing686 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37722608013399818240
theorem maskCheck686 :
    checkMaskFor missing686 StrongPackedBucketN12A2Shard005.record686 = true := by
  decide

def missing687 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37938780795513602048
theorem maskCheck687 :
    checkMaskFor missing687 StrongPackedBucketN12A2Shard005.record687 = true := by
  decide

def missing688 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37974809592532566016
theorem maskCheck688 :
    checkMaskFor missing688 StrongPackedBucketN12A2Shard005.record688 = true := by
  decide

def missing689 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38731414329930809344
theorem maskCheck689 :
    checkMaskFor missing689 StrongPackedBucketN12A2Shard005.record689 = true := by
  decide

def missing690 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38803471923968737280
theorem maskCheck690 :
    checkMaskFor missing690 StrongPackedBucketN12A2Shard005.record690 = true := by
  decide

def missing691 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38839500720987701248
theorem maskCheck691 :
    checkMaskFor missing691 StrongPackedBucketN12A2Shard005.record691 = true := by
  decide

def missing692 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39055673503101485056
theorem maskCheck692 :
    checkMaskFor missing692 StrongPackedBucketN12A2Shard005.record692 = true := by
  decide

def missing693 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 40965199745106575360
theorem maskCheck693 :
    checkMaskFor missing693 StrongPackedBucketN12A2Shard005.record693 = true := by
  decide

def missing694 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41001228542125539328
theorem maskCheck694 :
    checkMaskFor missing694 StrongPackedBucketN12A2Shard005.record694 = true := by
  decide

def missing695 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41073286136163467264
theorem maskCheck695 :
    checkMaskFor missing695 StrongPackedBucketN12A2Shard005.record695 = true := by
  decide

def missing696 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 45540856966514999296
theorem maskCheck696 :
    checkMaskFor missing696 StrongPackedBucketN12A2Shard005.record696 = true := by
  decide

def missing697 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46369519297951170560
theorem maskCheck697 :
    checkMaskFor missing697 StrongPackedBucketN12A2Shard005.record697 = true := by
  decide

def missing698 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46585692080064954368
theorem maskCheck698 :
    checkMaskFor missing698 StrongPackedBucketN12A2Shard005.record698 = true := by
  decide

def missing699 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46621720877083918336
theorem maskCheck699 :
    checkMaskFor missing699 StrongPackedBucketN12A2Shard005.record699 = true := by
  decide

def missing700 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46801864862178738176
theorem maskCheck700 :
    checkMaskFor missing700 StrongPackedBucketN12A2Shard005.record700 = true := by
  decide

def missing701 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46873922456216666112
theorem maskCheck701 :
    checkMaskFor missing701 StrongPackedBucketN12A2Shard005.record701 = true := by
  decide

def missing702 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46909951253235630080
theorem maskCheck702 :
    checkMaskFor missing702 StrongPackedBucketN12A2Shard005.record702 = true := by
  decide

def missing703 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47126124035349413888
theorem maskCheck703 :
    checkMaskFor missing703 StrongPackedBucketN12A2Shard005.record703 = true := by
  decide

def missing704 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47882728772747657216
theorem maskCheck704 :
    checkMaskFor missing704 StrongPackedBucketN12A2Shard005.record704 = true := by
  decide

def missing705 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47918757569766621184
theorem maskCheck705 :
    checkMaskFor missing705 StrongPackedBucketN12A2Shard005.record705 = true := by
  decide

def missing706 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47990815163804549120
theorem maskCheck706 :
    checkMaskFor missing706 StrongPackedBucketN12A2Shard005.record706 = true := by
  decide

def missing707 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50152542984942387200
theorem maskCheck707 :
    checkMaskFor missing707 StrongPackedBucketN12A2Shard005.record707 = true := by
  decide

def missing708 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55592891334805946368
theorem maskCheck708 :
    checkMaskFor missing708 StrongPackedBucketN12A2Shard005.record708 = true := by
  decide

def missing709 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55845092913938694144
theorem maskCheck709 :
    checkMaskFor missing709 StrongPackedBucketN12A2Shard005.record709 = true := by
  decide

def missing710 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56025236899033513984
theorem maskCheck710 :
    checkMaskFor missing710 StrongPackedBucketN12A2Shard005.record710 = true := by
  decide

def missing711 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56133323290090405888
theorem maskCheck711 :
    checkMaskFor missing711 StrongPackedBucketN12A2Shard005.record711 = true := by
  decide

def missing712 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57142129606621396992
theorem maskCheck712 :
    checkMaskFor missing712 StrongPackedBucketN12A2Shard005.record712 = true := by
  decide

def missing713 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64672148183584866304
theorem maskCheck713 :
    checkMaskFor missing713 StrongPackedBucketN12A2Shard005.record713 = true := by
  decide

def missing714 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64780234574641758208
theorem maskCheck714 :
    checkMaskFor missing714 StrongPackedBucketN12A2Shard005.record714 = true := by
  decide

def missing715 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 65212580138869325824
theorem maskCheck715 :
    checkMaskFor missing715 StrongPackedBucketN12A2Shard005.record715 = true := by
  decide

def missing716 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1117878007713759232
theorem maskCheck716 :
    checkMaskFor missing716 StrongPackedBucketN12A2Shard005.record716 = true := by
  decide

def missing717 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1694338760017182720
theorem maskCheck717 :
    checkMaskFor missing717 StrongPackedBucketN12A2Shard005.record717 = true := by
  decide

def missing718 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2198741918282678272
theorem maskCheck718 :
    checkMaskFor missing718 StrongPackedBucketN12A2Shard005.record718 = true := by
  decide

def missing719 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3711951393079164928
theorem maskCheck719 :
    checkMaskFor missing719 StrongPackedBucketN12A2Shard005.record719 = true := by
  decide

def missing720 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3928124175192948736
theorem maskCheck720 :
    checkMaskFor missing720 StrongPackedBucketN12A2Shard005.record720 = true := by
  decide

def missing721 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4468556130477408256
theorem maskCheck721 :
    checkMaskFor missing721 StrongPackedBucketN12A2Shard005.record721 = true := by
  decide

def missing722 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8179522223430696960
theorem maskCheck722 :
    checkMaskFor missing722 StrongPackedBucketN12A2Shard005.record722 = true := by
  decide

def missing723 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8251579817468624896
theorem maskCheck723 :
    checkMaskFor missing723 StrongPackedBucketN12A2Shard005.record723 = true := by
  decide

def missing724 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8503781396601372672
theorem maskCheck724 :
    checkMaskFor missing724 StrongPackedBucketN12A2Shard005.record724 = true := by
  decide

def missing725 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9764789292265111552
theorem maskCheck725 :
    checkMaskFor missing725 StrongPackedBucketN12A2Shard005.record725 = true := by
  decide

def missing726 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10269192450530607104
theorem maskCheck726 :
    checkMaskFor missing726 StrongPackedBucketN12A2Shard005.record726 = true := by
  decide

def missing727 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10629480420720246784
theorem maskCheck727 :
    checkMaskFor missing727 StrongPackedBucketN12A2Shard005.record727 = true := by
  decide

def missing728 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10845653202834030592
theorem maskCheck728 :
    checkMaskFor missing728 StrongPackedBucketN12A2Shard005.record728 = true := by
  decide

def missing729 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12791208241858084864
theorem maskCheck729 :
    checkMaskFor missing729 StrongPackedBucketN12A2Shard005.record729 = true := by
  decide

def missing730 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12863265835896012800
theorem maskCheck730 :
    checkMaskFor missing730 StrongPackedBucketN12A2Shard005.record730 = true := by
  decide

def missing731 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 17330836666247544832
theorem maskCheck731 :
    checkMaskFor missing731 StrongPackedBucketN12A2Shard005.record731 = true := by
  decide

def missing732 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27923302989822951424
theorem maskCheck732 :
    checkMaskFor missing732 StrongPackedBucketN12A2Shard005.record732 = true := by
  decide

def missing733 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28932109306353942528
theorem maskCheck733 :
    checkMaskFor missing733 StrongPackedBucketN12A2Shard005.record733 = true := by
  decide

def missing734 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37434905402829438976
theorem maskCheck734 :
    checkMaskFor missing734 StrongPackedBucketN12A2Shard005.record734 = true := by
  decide

def missing735 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37939308561094934528
theorem maskCheck735 :
    checkMaskFor missing735 StrongPackedBucketN12A2Shard005.record735 = true := by
  decide

def missing736 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38299596531284574208
theorem maskCheck736 :
    checkMaskFor missing736 StrongPackedBucketN12A2Shard005.record736 = true := by
  decide

def missing737 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38515769313398358016
theorem maskCheck737 :
    checkMaskFor missing737 StrongPackedBucketN12A2Shard005.record737 = true := by
  decide

def missing738 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39056201268682817536
theorem maskCheck738 :
    checkMaskFor missing738 StrongPackedBucketN12A2Shard005.record738 = true := by
  decide

def missing739 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 40461324352422412288
theorem maskCheck739 :
    checkMaskFor missing739 StrongPackedBucketN12A2Shard005.record739 = true := by
  decide

def missing740 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 40533381946460340224
theorem maskCheck740 :
    checkMaskFor missing740 StrongPackedBucketN12A2Shard005.record740 = true := by
  decide

def missing741 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 40785583525593088000
theorem maskCheck741 :
    checkMaskFor missing741 StrongPackedBucketN12A2Shard005.record741 = true := by
  decide

def missing742 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 45000952776811872256
theorem maskCheck742 :
    checkMaskFor missing742 StrongPackedBucketN12A2Shard005.record742 = true := by
  decide

def missing743 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 45109039167868764160
theorem maskCheck743 :
    checkMaskFor missing743 StrongPackedBucketN12A2Shard005.record743 = true := by
  decide

def missing744 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46370047063532503040
theorem maskCheck744 :
    checkMaskFor missing744 StrongPackedBucketN12A2Shard005.record744 = true := by
  decide

def missing745 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46586219845646286848
theorem maskCheck745 :
    checkMaskFor missing745 StrongPackedBucketN12A2Shard005.record745 = true := by
  decide

def missing746 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47378853380063494144
theorem maskCheck746 :
    checkMaskFor missing746 StrongPackedBucketN12A2Shard005.record746 = true := by
  decide

def missing747 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47450910974101422080
theorem maskCheck747 :
    checkMaskFor missing747 StrongPackedBucketN12A2Shard005.record747 = true := by
  decide

def missing748 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 49612638795239260160
theorem maskCheck748 :
    checkMaskFor missing748 StrongPackedBucketN12A2Shard005.record748 = true := by
  decide

def missing749 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64672675949166198784
theorem maskCheck749 :
    checkMaskFor missing749 StrongPackedBucketN12A2Shard005.record749 = true := by
  decide

def missing750 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1126005597666279424
theorem maskCheck750 :
    checkMaskFor missing750 StrongPackedBucketN12A2Shard005.record750 = true := by
  decide

def missing751 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2206869508235198464
theorem maskCheck751 :
    checkMaskFor missing751 StrongPackedBucketN12A2Shard005.record751 = true := by
  decide

def missing752 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2242898305254162432
theorem maskCheck752 :
    checkMaskFor missing752 StrongPackedBucketN12A2Shard005.record752 = true := by
  decide

def missing753 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4476683720429928448
theorem maskCheck753 :
    checkMaskFor missing753 StrongPackedBucketN12A2Shard005.record753 = true := by
  decide

def missing754 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9772916882217631744
theorem maskCheck754 :
    checkMaskFor missing754 StrongPackedBucketN12A2Shard005.record754 = true := by
  decide

def missing755 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10277320040483127296
theorem maskCheck755 :
    checkMaskFor missing755 StrongPackedBucketN12A2Shard005.record755 = true := by
  decide

def missing756 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18996288919072407552
theorem maskCheck756 :
    checkMaskFor missing756 StrongPackedBucketN12A2Shard005.record756 = true := by
  decide

def missing757 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19500692077337903104
theorem maskCheck757 :
    checkMaskFor missing757 StrongPackedBucketN12A2Shard005.record757 = true := by
  decide

def missing758 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19536720874356867072
theorem maskCheck758 :
    checkMaskFor missing758 StrongPackedBucketN12A2Shard005.record758 = true := by
  decide

def missing759 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20617584784925786112
theorem maskCheck759 :
    checkMaskFor missing759 StrongPackedBucketN12A2Shard005.record759 = true := by
  decide

def missing760 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27931430579775471616
theorem maskCheck760 :
    checkMaskFor missing760 StrongPackedBucketN12A2Shard005.record760 = true := by
  decide

def missing761 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28147603361889255424
theorem maskCheck761 :
    checkMaskFor missing761 StrongPackedBucketN12A2Shard005.record761 = true := by
  decide

def missing762 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37443032992781959168
theorem maskCheck762 :
    checkMaskFor missing762 StrongPackedBucketN12A2Shard005.record762 = true := by
  decide

def missing763 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37947436151047454720
theorem maskCheck763 :
    checkMaskFor missing763 StrongPackedBucketN12A2Shard005.record763 = true := by
  decide

def missing764 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37983464948066418688
theorem maskCheck764 :
    checkMaskFor missing764 StrongPackedBucketN12A2Shard005.record764 = true := by
  decide

def missing765 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39064328858635337728
theorem maskCheck765 :
    checkMaskFor missing765 StrongPackedBucketN12A2Shard005.record765 = true := by
  decide

def missing766 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46378174653485023232
theorem maskCheck766 :
    checkMaskFor missing766 StrongPackedBucketN12A2Shard005.record766 = true := by
  decide

def missing767 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46594347435598807040
theorem maskCheck767 :
    checkMaskFor missing767 StrongPackedBucketN12A2Shard005.record767 = true := by
  decide

def missing640_641 : List (BitVec (edgeCount 12)) :=
  [missing640]
abbrev records640_641 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record640]
theorem aligned640_641 :
    AlignedValid 12 2 missing640_641 records640_641 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check640
    maskCheck640 AlignedValid.nil

def missing641_642 : List (BitVec (edgeCount 12)) :=
  [missing641]
abbrev records641_642 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record641]
theorem aligned641_642 :
    AlignedValid 12 2 missing641_642 records641_642 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check641
    maskCheck641 AlignedValid.nil

def missing640_642 : List (BitVec (edgeCount 12)) :=
  missing640_641 ++ missing641_642
abbrev records640_642 : List Blob :=
  records640_641 ++ records641_642
theorem aligned640_642 :
    AlignedValid 12 2 missing640_642 records640_642 :=
  aligned640_641.append aligned641_642

def missing642_643 : List (BitVec (edgeCount 12)) :=
  [missing642]
abbrev records642_643 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record642]
theorem aligned642_643 :
    AlignedValid 12 2 missing642_643 records642_643 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check642
    maskCheck642 AlignedValid.nil

def missing643_644 : List (BitVec (edgeCount 12)) :=
  [missing643]
abbrev records643_644 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record643]
theorem aligned643_644 :
    AlignedValid 12 2 missing643_644 records643_644 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check643
    maskCheck643 AlignedValid.nil

def missing642_644 : List (BitVec (edgeCount 12)) :=
  missing642_643 ++ missing643_644
abbrev records642_644 : List Blob :=
  records642_643 ++ records643_644
theorem aligned642_644 :
    AlignedValid 12 2 missing642_644 records642_644 :=
  aligned642_643.append aligned643_644

def missing640_644 : List (BitVec (edgeCount 12)) :=
  missing640_642 ++ missing642_644
abbrev records640_644 : List Blob :=
  records640_642 ++ records642_644
theorem aligned640_644 :
    AlignedValid 12 2 missing640_644 records640_644 :=
  aligned640_642.append aligned642_644

def missing644_645 : List (BitVec (edgeCount 12)) :=
  [missing644]
abbrev records644_645 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record644]
theorem aligned644_645 :
    AlignedValid 12 2 missing644_645 records644_645 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check644
    maskCheck644 AlignedValid.nil

def missing645_646 : List (BitVec (edgeCount 12)) :=
  [missing645]
abbrev records645_646 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record645]
theorem aligned645_646 :
    AlignedValid 12 2 missing645_646 records645_646 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check645
    maskCheck645 AlignedValid.nil

def missing644_646 : List (BitVec (edgeCount 12)) :=
  missing644_645 ++ missing645_646
abbrev records644_646 : List Blob :=
  records644_645 ++ records645_646
theorem aligned644_646 :
    AlignedValid 12 2 missing644_646 records644_646 :=
  aligned644_645.append aligned645_646

def missing646_647 : List (BitVec (edgeCount 12)) :=
  [missing646]
abbrev records646_647 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record646]
theorem aligned646_647 :
    AlignedValid 12 2 missing646_647 records646_647 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check646
    maskCheck646 AlignedValid.nil

def missing647_648 : List (BitVec (edgeCount 12)) :=
  [missing647]
abbrev records647_648 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record647]
theorem aligned647_648 :
    AlignedValid 12 2 missing647_648 records647_648 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check647
    maskCheck647 AlignedValid.nil

def missing646_648 : List (BitVec (edgeCount 12)) :=
  missing646_647 ++ missing647_648
abbrev records646_648 : List Blob :=
  records646_647 ++ records647_648
theorem aligned646_648 :
    AlignedValid 12 2 missing646_648 records646_648 :=
  aligned646_647.append aligned647_648

def missing644_648 : List (BitVec (edgeCount 12)) :=
  missing644_646 ++ missing646_648
abbrev records644_648 : List Blob :=
  records644_646 ++ records646_648
theorem aligned644_648 :
    AlignedValid 12 2 missing644_648 records644_648 :=
  aligned644_646.append aligned646_648

def missing640_648 : List (BitVec (edgeCount 12)) :=
  missing640_644 ++ missing644_648
abbrev records640_648 : List Blob :=
  records640_644 ++ records644_648
theorem aligned640_648 :
    AlignedValid 12 2 missing640_648 records640_648 :=
  aligned640_644.append aligned644_648

def missing648_649 : List (BitVec (edgeCount 12)) :=
  [missing648]
abbrev records648_649 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record648]
theorem aligned648_649 :
    AlignedValid 12 2 missing648_649 records648_649 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check648
    maskCheck648 AlignedValid.nil

def missing649_650 : List (BitVec (edgeCount 12)) :=
  [missing649]
abbrev records649_650 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record649]
theorem aligned649_650 :
    AlignedValid 12 2 missing649_650 records649_650 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check649
    maskCheck649 AlignedValid.nil

def missing648_650 : List (BitVec (edgeCount 12)) :=
  missing648_649 ++ missing649_650
abbrev records648_650 : List Blob :=
  records648_649 ++ records649_650
theorem aligned648_650 :
    AlignedValid 12 2 missing648_650 records648_650 :=
  aligned648_649.append aligned649_650

def missing650_651 : List (BitVec (edgeCount 12)) :=
  [missing650]
abbrev records650_651 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record650]
theorem aligned650_651 :
    AlignedValid 12 2 missing650_651 records650_651 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check650
    maskCheck650 AlignedValid.nil

def missing651_652 : List (BitVec (edgeCount 12)) :=
  [missing651]
abbrev records651_652 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record651]
theorem aligned651_652 :
    AlignedValid 12 2 missing651_652 records651_652 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check651
    maskCheck651 AlignedValid.nil

def missing650_652 : List (BitVec (edgeCount 12)) :=
  missing650_651 ++ missing651_652
abbrev records650_652 : List Blob :=
  records650_651 ++ records651_652
theorem aligned650_652 :
    AlignedValid 12 2 missing650_652 records650_652 :=
  aligned650_651.append aligned651_652

def missing648_652 : List (BitVec (edgeCount 12)) :=
  missing648_650 ++ missing650_652
abbrev records648_652 : List Blob :=
  records648_650 ++ records650_652
theorem aligned648_652 :
    AlignedValid 12 2 missing648_652 records648_652 :=
  aligned648_650.append aligned650_652

def missing652_653 : List (BitVec (edgeCount 12)) :=
  [missing652]
abbrev records652_653 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record652]
theorem aligned652_653 :
    AlignedValid 12 2 missing652_653 records652_653 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check652
    maskCheck652 AlignedValid.nil

def missing653_654 : List (BitVec (edgeCount 12)) :=
  [missing653]
abbrev records653_654 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record653]
theorem aligned653_654 :
    AlignedValid 12 2 missing653_654 records653_654 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check653
    maskCheck653 AlignedValid.nil

def missing652_654 : List (BitVec (edgeCount 12)) :=
  missing652_653 ++ missing653_654
abbrev records652_654 : List Blob :=
  records652_653 ++ records653_654
theorem aligned652_654 :
    AlignedValid 12 2 missing652_654 records652_654 :=
  aligned652_653.append aligned653_654

def missing654_655 : List (BitVec (edgeCount 12)) :=
  [missing654]
abbrev records654_655 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record654]
theorem aligned654_655 :
    AlignedValid 12 2 missing654_655 records654_655 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check654
    maskCheck654 AlignedValid.nil

def missing655_656 : List (BitVec (edgeCount 12)) :=
  [missing655]
abbrev records655_656 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record655]
theorem aligned655_656 :
    AlignedValid 12 2 missing655_656 records655_656 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check655
    maskCheck655 AlignedValid.nil

def missing654_656 : List (BitVec (edgeCount 12)) :=
  missing654_655 ++ missing655_656
abbrev records654_656 : List Blob :=
  records654_655 ++ records655_656
theorem aligned654_656 :
    AlignedValid 12 2 missing654_656 records654_656 :=
  aligned654_655.append aligned655_656

def missing652_656 : List (BitVec (edgeCount 12)) :=
  missing652_654 ++ missing654_656
abbrev records652_656 : List Blob :=
  records652_654 ++ records654_656
theorem aligned652_656 :
    AlignedValid 12 2 missing652_656 records652_656 :=
  aligned652_654.append aligned654_656

def missing648_656 : List (BitVec (edgeCount 12)) :=
  missing648_652 ++ missing652_656
abbrev records648_656 : List Blob :=
  records648_652 ++ records652_656
theorem aligned648_656 :
    AlignedValid 12 2 missing648_656 records648_656 :=
  aligned648_652.append aligned652_656

def missing640_656 : List (BitVec (edgeCount 12)) :=
  missing640_648 ++ missing648_656
abbrev records640_656 : List Blob :=
  records640_648 ++ records648_656
theorem aligned640_656 :
    AlignedValid 12 2 missing640_656 records640_656 :=
  aligned640_648.append aligned648_656

def missing656_657 : List (BitVec (edgeCount 12)) :=
  [missing656]
abbrev records656_657 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record656]
theorem aligned656_657 :
    AlignedValid 12 2 missing656_657 records656_657 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check656
    maskCheck656 AlignedValid.nil

def missing657_658 : List (BitVec (edgeCount 12)) :=
  [missing657]
abbrev records657_658 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record657]
theorem aligned657_658 :
    AlignedValid 12 2 missing657_658 records657_658 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check657
    maskCheck657 AlignedValid.nil

def missing656_658 : List (BitVec (edgeCount 12)) :=
  missing656_657 ++ missing657_658
abbrev records656_658 : List Blob :=
  records656_657 ++ records657_658
theorem aligned656_658 :
    AlignedValid 12 2 missing656_658 records656_658 :=
  aligned656_657.append aligned657_658

def missing658_659 : List (BitVec (edgeCount 12)) :=
  [missing658]
abbrev records658_659 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record658]
theorem aligned658_659 :
    AlignedValid 12 2 missing658_659 records658_659 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check658
    maskCheck658 AlignedValid.nil

def missing659_660 : List (BitVec (edgeCount 12)) :=
  [missing659]
abbrev records659_660 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record659]
theorem aligned659_660 :
    AlignedValid 12 2 missing659_660 records659_660 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check659
    maskCheck659 AlignedValid.nil

def missing658_660 : List (BitVec (edgeCount 12)) :=
  missing658_659 ++ missing659_660
abbrev records658_660 : List Blob :=
  records658_659 ++ records659_660
theorem aligned658_660 :
    AlignedValid 12 2 missing658_660 records658_660 :=
  aligned658_659.append aligned659_660

def missing656_660 : List (BitVec (edgeCount 12)) :=
  missing656_658 ++ missing658_660
abbrev records656_660 : List Blob :=
  records656_658 ++ records658_660
theorem aligned656_660 :
    AlignedValid 12 2 missing656_660 records656_660 :=
  aligned656_658.append aligned658_660

def missing660_661 : List (BitVec (edgeCount 12)) :=
  [missing660]
abbrev records660_661 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record660]
theorem aligned660_661 :
    AlignedValid 12 2 missing660_661 records660_661 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check660
    maskCheck660 AlignedValid.nil

def missing661_662 : List (BitVec (edgeCount 12)) :=
  [missing661]
abbrev records661_662 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record661]
theorem aligned661_662 :
    AlignedValid 12 2 missing661_662 records661_662 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check661
    maskCheck661 AlignedValid.nil

def missing660_662 : List (BitVec (edgeCount 12)) :=
  missing660_661 ++ missing661_662
abbrev records660_662 : List Blob :=
  records660_661 ++ records661_662
theorem aligned660_662 :
    AlignedValid 12 2 missing660_662 records660_662 :=
  aligned660_661.append aligned661_662

def missing662_663 : List (BitVec (edgeCount 12)) :=
  [missing662]
abbrev records662_663 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record662]
theorem aligned662_663 :
    AlignedValid 12 2 missing662_663 records662_663 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check662
    maskCheck662 AlignedValid.nil

def missing663_664 : List (BitVec (edgeCount 12)) :=
  [missing663]
abbrev records663_664 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record663]
theorem aligned663_664 :
    AlignedValid 12 2 missing663_664 records663_664 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check663
    maskCheck663 AlignedValid.nil

def missing662_664 : List (BitVec (edgeCount 12)) :=
  missing662_663 ++ missing663_664
abbrev records662_664 : List Blob :=
  records662_663 ++ records663_664
theorem aligned662_664 :
    AlignedValid 12 2 missing662_664 records662_664 :=
  aligned662_663.append aligned663_664

def missing660_664 : List (BitVec (edgeCount 12)) :=
  missing660_662 ++ missing662_664
abbrev records660_664 : List Blob :=
  records660_662 ++ records662_664
theorem aligned660_664 :
    AlignedValid 12 2 missing660_664 records660_664 :=
  aligned660_662.append aligned662_664

def missing656_664 : List (BitVec (edgeCount 12)) :=
  missing656_660 ++ missing660_664
abbrev records656_664 : List Blob :=
  records656_660 ++ records660_664
theorem aligned656_664 :
    AlignedValid 12 2 missing656_664 records656_664 :=
  aligned656_660.append aligned660_664

def missing664_665 : List (BitVec (edgeCount 12)) :=
  [missing664]
abbrev records664_665 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record664]
theorem aligned664_665 :
    AlignedValid 12 2 missing664_665 records664_665 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check664
    maskCheck664 AlignedValid.nil

def missing665_666 : List (BitVec (edgeCount 12)) :=
  [missing665]
abbrev records665_666 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record665]
theorem aligned665_666 :
    AlignedValid 12 2 missing665_666 records665_666 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check665
    maskCheck665 AlignedValid.nil

def missing664_666 : List (BitVec (edgeCount 12)) :=
  missing664_665 ++ missing665_666
abbrev records664_666 : List Blob :=
  records664_665 ++ records665_666
theorem aligned664_666 :
    AlignedValid 12 2 missing664_666 records664_666 :=
  aligned664_665.append aligned665_666

def missing666_667 : List (BitVec (edgeCount 12)) :=
  [missing666]
abbrev records666_667 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record666]
theorem aligned666_667 :
    AlignedValid 12 2 missing666_667 records666_667 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check666
    maskCheck666 AlignedValid.nil

def missing667_668 : List (BitVec (edgeCount 12)) :=
  [missing667]
abbrev records667_668 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record667]
theorem aligned667_668 :
    AlignedValid 12 2 missing667_668 records667_668 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check667
    maskCheck667 AlignedValid.nil

def missing666_668 : List (BitVec (edgeCount 12)) :=
  missing666_667 ++ missing667_668
abbrev records666_668 : List Blob :=
  records666_667 ++ records667_668
theorem aligned666_668 :
    AlignedValid 12 2 missing666_668 records666_668 :=
  aligned666_667.append aligned667_668

def missing664_668 : List (BitVec (edgeCount 12)) :=
  missing664_666 ++ missing666_668
abbrev records664_668 : List Blob :=
  records664_666 ++ records666_668
theorem aligned664_668 :
    AlignedValid 12 2 missing664_668 records664_668 :=
  aligned664_666.append aligned666_668

def missing668_669 : List (BitVec (edgeCount 12)) :=
  [missing668]
abbrev records668_669 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record668]
theorem aligned668_669 :
    AlignedValid 12 2 missing668_669 records668_669 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check668
    maskCheck668 AlignedValid.nil

def missing669_670 : List (BitVec (edgeCount 12)) :=
  [missing669]
abbrev records669_670 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record669]
theorem aligned669_670 :
    AlignedValid 12 2 missing669_670 records669_670 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check669
    maskCheck669 AlignedValid.nil

def missing668_670 : List (BitVec (edgeCount 12)) :=
  missing668_669 ++ missing669_670
abbrev records668_670 : List Blob :=
  records668_669 ++ records669_670
theorem aligned668_670 :
    AlignedValid 12 2 missing668_670 records668_670 :=
  aligned668_669.append aligned669_670

def missing670_671 : List (BitVec (edgeCount 12)) :=
  [missing670]
abbrev records670_671 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record670]
theorem aligned670_671 :
    AlignedValid 12 2 missing670_671 records670_671 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check670
    maskCheck670 AlignedValid.nil

def missing671_672 : List (BitVec (edgeCount 12)) :=
  [missing671]
abbrev records671_672 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record671]
theorem aligned671_672 :
    AlignedValid 12 2 missing671_672 records671_672 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check671
    maskCheck671 AlignedValid.nil

def missing670_672 : List (BitVec (edgeCount 12)) :=
  missing670_671 ++ missing671_672
abbrev records670_672 : List Blob :=
  records670_671 ++ records671_672
theorem aligned670_672 :
    AlignedValid 12 2 missing670_672 records670_672 :=
  aligned670_671.append aligned671_672

def missing668_672 : List (BitVec (edgeCount 12)) :=
  missing668_670 ++ missing670_672
abbrev records668_672 : List Blob :=
  records668_670 ++ records670_672
theorem aligned668_672 :
    AlignedValid 12 2 missing668_672 records668_672 :=
  aligned668_670.append aligned670_672

def missing664_672 : List (BitVec (edgeCount 12)) :=
  missing664_668 ++ missing668_672
abbrev records664_672 : List Blob :=
  records664_668 ++ records668_672
theorem aligned664_672 :
    AlignedValid 12 2 missing664_672 records664_672 :=
  aligned664_668.append aligned668_672

def missing656_672 : List (BitVec (edgeCount 12)) :=
  missing656_664 ++ missing664_672
abbrev records656_672 : List Blob :=
  records656_664 ++ records664_672
theorem aligned656_672 :
    AlignedValid 12 2 missing656_672 records656_672 :=
  aligned656_664.append aligned664_672

def missing640_672 : List (BitVec (edgeCount 12)) :=
  missing640_656 ++ missing656_672
abbrev records640_672 : List Blob :=
  records640_656 ++ records656_672
theorem aligned640_672 :
    AlignedValid 12 2 missing640_672 records640_672 :=
  aligned640_656.append aligned656_672

def missing672_673 : List (BitVec (edgeCount 12)) :=
  [missing672]
abbrev records672_673 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record672]
theorem aligned672_673 :
    AlignedValid 12 2 missing672_673 records672_673 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check672
    maskCheck672 AlignedValid.nil

def missing673_674 : List (BitVec (edgeCount 12)) :=
  [missing673]
abbrev records673_674 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record673]
theorem aligned673_674 :
    AlignedValid 12 2 missing673_674 records673_674 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check673
    maskCheck673 AlignedValid.nil

def missing672_674 : List (BitVec (edgeCount 12)) :=
  missing672_673 ++ missing673_674
abbrev records672_674 : List Blob :=
  records672_673 ++ records673_674
theorem aligned672_674 :
    AlignedValid 12 2 missing672_674 records672_674 :=
  aligned672_673.append aligned673_674

def missing674_675 : List (BitVec (edgeCount 12)) :=
  [missing674]
abbrev records674_675 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record674]
theorem aligned674_675 :
    AlignedValid 12 2 missing674_675 records674_675 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check674
    maskCheck674 AlignedValid.nil

def missing675_676 : List (BitVec (edgeCount 12)) :=
  [missing675]
abbrev records675_676 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record675]
theorem aligned675_676 :
    AlignedValid 12 2 missing675_676 records675_676 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check675
    maskCheck675 AlignedValid.nil

def missing674_676 : List (BitVec (edgeCount 12)) :=
  missing674_675 ++ missing675_676
abbrev records674_676 : List Blob :=
  records674_675 ++ records675_676
theorem aligned674_676 :
    AlignedValid 12 2 missing674_676 records674_676 :=
  aligned674_675.append aligned675_676

def missing672_676 : List (BitVec (edgeCount 12)) :=
  missing672_674 ++ missing674_676
abbrev records672_676 : List Blob :=
  records672_674 ++ records674_676
theorem aligned672_676 :
    AlignedValid 12 2 missing672_676 records672_676 :=
  aligned672_674.append aligned674_676

def missing676_677 : List (BitVec (edgeCount 12)) :=
  [missing676]
abbrev records676_677 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record676]
theorem aligned676_677 :
    AlignedValid 12 2 missing676_677 records676_677 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check676
    maskCheck676 AlignedValid.nil

def missing677_678 : List (BitVec (edgeCount 12)) :=
  [missing677]
abbrev records677_678 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record677]
theorem aligned677_678 :
    AlignedValid 12 2 missing677_678 records677_678 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check677
    maskCheck677 AlignedValid.nil

def missing676_678 : List (BitVec (edgeCount 12)) :=
  missing676_677 ++ missing677_678
abbrev records676_678 : List Blob :=
  records676_677 ++ records677_678
theorem aligned676_678 :
    AlignedValid 12 2 missing676_678 records676_678 :=
  aligned676_677.append aligned677_678

def missing678_679 : List (BitVec (edgeCount 12)) :=
  [missing678]
abbrev records678_679 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record678]
theorem aligned678_679 :
    AlignedValid 12 2 missing678_679 records678_679 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check678
    maskCheck678 AlignedValid.nil

def missing679_680 : List (BitVec (edgeCount 12)) :=
  [missing679]
abbrev records679_680 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record679]
theorem aligned679_680 :
    AlignedValid 12 2 missing679_680 records679_680 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check679
    maskCheck679 AlignedValid.nil

def missing678_680 : List (BitVec (edgeCount 12)) :=
  missing678_679 ++ missing679_680
abbrev records678_680 : List Blob :=
  records678_679 ++ records679_680
theorem aligned678_680 :
    AlignedValid 12 2 missing678_680 records678_680 :=
  aligned678_679.append aligned679_680

def missing676_680 : List (BitVec (edgeCount 12)) :=
  missing676_678 ++ missing678_680
abbrev records676_680 : List Blob :=
  records676_678 ++ records678_680
theorem aligned676_680 :
    AlignedValid 12 2 missing676_680 records676_680 :=
  aligned676_678.append aligned678_680

def missing672_680 : List (BitVec (edgeCount 12)) :=
  missing672_676 ++ missing676_680
abbrev records672_680 : List Blob :=
  records672_676 ++ records676_680
theorem aligned672_680 :
    AlignedValid 12 2 missing672_680 records672_680 :=
  aligned672_676.append aligned676_680

def missing680_681 : List (BitVec (edgeCount 12)) :=
  [missing680]
abbrev records680_681 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record680]
theorem aligned680_681 :
    AlignedValid 12 2 missing680_681 records680_681 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check680
    maskCheck680 AlignedValid.nil

def missing681_682 : List (BitVec (edgeCount 12)) :=
  [missing681]
abbrev records681_682 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record681]
theorem aligned681_682 :
    AlignedValid 12 2 missing681_682 records681_682 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check681
    maskCheck681 AlignedValid.nil

def missing680_682 : List (BitVec (edgeCount 12)) :=
  missing680_681 ++ missing681_682
abbrev records680_682 : List Blob :=
  records680_681 ++ records681_682
theorem aligned680_682 :
    AlignedValid 12 2 missing680_682 records680_682 :=
  aligned680_681.append aligned681_682

def missing682_683 : List (BitVec (edgeCount 12)) :=
  [missing682]
abbrev records682_683 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record682]
theorem aligned682_683 :
    AlignedValid 12 2 missing682_683 records682_683 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check682
    maskCheck682 AlignedValid.nil

def missing683_684 : List (BitVec (edgeCount 12)) :=
  [missing683]
abbrev records683_684 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record683]
theorem aligned683_684 :
    AlignedValid 12 2 missing683_684 records683_684 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check683
    maskCheck683 AlignedValid.nil

def missing682_684 : List (BitVec (edgeCount 12)) :=
  missing682_683 ++ missing683_684
abbrev records682_684 : List Blob :=
  records682_683 ++ records683_684
theorem aligned682_684 :
    AlignedValid 12 2 missing682_684 records682_684 :=
  aligned682_683.append aligned683_684

def missing680_684 : List (BitVec (edgeCount 12)) :=
  missing680_682 ++ missing682_684
abbrev records680_684 : List Blob :=
  records680_682 ++ records682_684
theorem aligned680_684 :
    AlignedValid 12 2 missing680_684 records680_684 :=
  aligned680_682.append aligned682_684

def missing684_685 : List (BitVec (edgeCount 12)) :=
  [missing684]
abbrev records684_685 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record684]
theorem aligned684_685 :
    AlignedValid 12 2 missing684_685 records684_685 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check684
    maskCheck684 AlignedValid.nil

def missing685_686 : List (BitVec (edgeCount 12)) :=
  [missing685]
abbrev records685_686 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record685]
theorem aligned685_686 :
    AlignedValid 12 2 missing685_686 records685_686 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check685
    maskCheck685 AlignedValid.nil

def missing684_686 : List (BitVec (edgeCount 12)) :=
  missing684_685 ++ missing685_686
abbrev records684_686 : List Blob :=
  records684_685 ++ records685_686
theorem aligned684_686 :
    AlignedValid 12 2 missing684_686 records684_686 :=
  aligned684_685.append aligned685_686

def missing686_687 : List (BitVec (edgeCount 12)) :=
  [missing686]
abbrev records686_687 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record686]
theorem aligned686_687 :
    AlignedValid 12 2 missing686_687 records686_687 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check686
    maskCheck686 AlignedValid.nil

def missing687_688 : List (BitVec (edgeCount 12)) :=
  [missing687]
abbrev records687_688 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record687]
theorem aligned687_688 :
    AlignedValid 12 2 missing687_688 records687_688 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check687
    maskCheck687 AlignedValid.nil

def missing686_688 : List (BitVec (edgeCount 12)) :=
  missing686_687 ++ missing687_688
abbrev records686_688 : List Blob :=
  records686_687 ++ records687_688
theorem aligned686_688 :
    AlignedValid 12 2 missing686_688 records686_688 :=
  aligned686_687.append aligned687_688

def missing684_688 : List (BitVec (edgeCount 12)) :=
  missing684_686 ++ missing686_688
abbrev records684_688 : List Blob :=
  records684_686 ++ records686_688
theorem aligned684_688 :
    AlignedValid 12 2 missing684_688 records684_688 :=
  aligned684_686.append aligned686_688

def missing680_688 : List (BitVec (edgeCount 12)) :=
  missing680_684 ++ missing684_688
abbrev records680_688 : List Blob :=
  records680_684 ++ records684_688
theorem aligned680_688 :
    AlignedValid 12 2 missing680_688 records680_688 :=
  aligned680_684.append aligned684_688

def missing672_688 : List (BitVec (edgeCount 12)) :=
  missing672_680 ++ missing680_688
abbrev records672_688 : List Blob :=
  records672_680 ++ records680_688
theorem aligned672_688 :
    AlignedValid 12 2 missing672_688 records672_688 :=
  aligned672_680.append aligned680_688

def missing688_689 : List (BitVec (edgeCount 12)) :=
  [missing688]
abbrev records688_689 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record688]
theorem aligned688_689 :
    AlignedValid 12 2 missing688_689 records688_689 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check688
    maskCheck688 AlignedValid.nil

def missing689_690 : List (BitVec (edgeCount 12)) :=
  [missing689]
abbrev records689_690 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record689]
theorem aligned689_690 :
    AlignedValid 12 2 missing689_690 records689_690 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check689
    maskCheck689 AlignedValid.nil

def missing688_690 : List (BitVec (edgeCount 12)) :=
  missing688_689 ++ missing689_690
abbrev records688_690 : List Blob :=
  records688_689 ++ records689_690
theorem aligned688_690 :
    AlignedValid 12 2 missing688_690 records688_690 :=
  aligned688_689.append aligned689_690

def missing690_691 : List (BitVec (edgeCount 12)) :=
  [missing690]
abbrev records690_691 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record690]
theorem aligned690_691 :
    AlignedValid 12 2 missing690_691 records690_691 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check690
    maskCheck690 AlignedValid.nil

def missing691_692 : List (BitVec (edgeCount 12)) :=
  [missing691]
abbrev records691_692 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record691]
theorem aligned691_692 :
    AlignedValid 12 2 missing691_692 records691_692 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check691
    maskCheck691 AlignedValid.nil

def missing690_692 : List (BitVec (edgeCount 12)) :=
  missing690_691 ++ missing691_692
abbrev records690_692 : List Blob :=
  records690_691 ++ records691_692
theorem aligned690_692 :
    AlignedValid 12 2 missing690_692 records690_692 :=
  aligned690_691.append aligned691_692

def missing688_692 : List (BitVec (edgeCount 12)) :=
  missing688_690 ++ missing690_692
abbrev records688_692 : List Blob :=
  records688_690 ++ records690_692
theorem aligned688_692 :
    AlignedValid 12 2 missing688_692 records688_692 :=
  aligned688_690.append aligned690_692

def missing692_693 : List (BitVec (edgeCount 12)) :=
  [missing692]
abbrev records692_693 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record692]
theorem aligned692_693 :
    AlignedValid 12 2 missing692_693 records692_693 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check692
    maskCheck692 AlignedValid.nil

def missing693_694 : List (BitVec (edgeCount 12)) :=
  [missing693]
abbrev records693_694 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record693]
theorem aligned693_694 :
    AlignedValid 12 2 missing693_694 records693_694 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check693
    maskCheck693 AlignedValid.nil

def missing692_694 : List (BitVec (edgeCount 12)) :=
  missing692_693 ++ missing693_694
abbrev records692_694 : List Blob :=
  records692_693 ++ records693_694
theorem aligned692_694 :
    AlignedValid 12 2 missing692_694 records692_694 :=
  aligned692_693.append aligned693_694

def missing694_695 : List (BitVec (edgeCount 12)) :=
  [missing694]
abbrev records694_695 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record694]
theorem aligned694_695 :
    AlignedValid 12 2 missing694_695 records694_695 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check694
    maskCheck694 AlignedValid.nil

def missing695_696 : List (BitVec (edgeCount 12)) :=
  [missing695]
abbrev records695_696 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record695]
theorem aligned695_696 :
    AlignedValid 12 2 missing695_696 records695_696 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check695
    maskCheck695 AlignedValid.nil

def missing694_696 : List (BitVec (edgeCount 12)) :=
  missing694_695 ++ missing695_696
abbrev records694_696 : List Blob :=
  records694_695 ++ records695_696
theorem aligned694_696 :
    AlignedValid 12 2 missing694_696 records694_696 :=
  aligned694_695.append aligned695_696

def missing692_696 : List (BitVec (edgeCount 12)) :=
  missing692_694 ++ missing694_696
abbrev records692_696 : List Blob :=
  records692_694 ++ records694_696
theorem aligned692_696 :
    AlignedValid 12 2 missing692_696 records692_696 :=
  aligned692_694.append aligned694_696

def missing688_696 : List (BitVec (edgeCount 12)) :=
  missing688_692 ++ missing692_696
abbrev records688_696 : List Blob :=
  records688_692 ++ records692_696
theorem aligned688_696 :
    AlignedValid 12 2 missing688_696 records688_696 :=
  aligned688_692.append aligned692_696

def missing696_697 : List (BitVec (edgeCount 12)) :=
  [missing696]
abbrev records696_697 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record696]
theorem aligned696_697 :
    AlignedValid 12 2 missing696_697 records696_697 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check696
    maskCheck696 AlignedValid.nil

def missing697_698 : List (BitVec (edgeCount 12)) :=
  [missing697]
abbrev records697_698 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record697]
theorem aligned697_698 :
    AlignedValid 12 2 missing697_698 records697_698 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check697
    maskCheck697 AlignedValid.nil

def missing696_698 : List (BitVec (edgeCount 12)) :=
  missing696_697 ++ missing697_698
abbrev records696_698 : List Blob :=
  records696_697 ++ records697_698
theorem aligned696_698 :
    AlignedValid 12 2 missing696_698 records696_698 :=
  aligned696_697.append aligned697_698

def missing698_699 : List (BitVec (edgeCount 12)) :=
  [missing698]
abbrev records698_699 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record698]
theorem aligned698_699 :
    AlignedValid 12 2 missing698_699 records698_699 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check698
    maskCheck698 AlignedValid.nil

def missing699_700 : List (BitVec (edgeCount 12)) :=
  [missing699]
abbrev records699_700 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record699]
theorem aligned699_700 :
    AlignedValid 12 2 missing699_700 records699_700 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check699
    maskCheck699 AlignedValid.nil

def missing698_700 : List (BitVec (edgeCount 12)) :=
  missing698_699 ++ missing699_700
abbrev records698_700 : List Blob :=
  records698_699 ++ records699_700
theorem aligned698_700 :
    AlignedValid 12 2 missing698_700 records698_700 :=
  aligned698_699.append aligned699_700

def missing696_700 : List (BitVec (edgeCount 12)) :=
  missing696_698 ++ missing698_700
abbrev records696_700 : List Blob :=
  records696_698 ++ records698_700
theorem aligned696_700 :
    AlignedValid 12 2 missing696_700 records696_700 :=
  aligned696_698.append aligned698_700

def missing700_701 : List (BitVec (edgeCount 12)) :=
  [missing700]
abbrev records700_701 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record700]
theorem aligned700_701 :
    AlignedValid 12 2 missing700_701 records700_701 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check700
    maskCheck700 AlignedValid.nil

def missing701_702 : List (BitVec (edgeCount 12)) :=
  [missing701]
abbrev records701_702 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record701]
theorem aligned701_702 :
    AlignedValid 12 2 missing701_702 records701_702 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check701
    maskCheck701 AlignedValid.nil

def missing700_702 : List (BitVec (edgeCount 12)) :=
  missing700_701 ++ missing701_702
abbrev records700_702 : List Blob :=
  records700_701 ++ records701_702
theorem aligned700_702 :
    AlignedValid 12 2 missing700_702 records700_702 :=
  aligned700_701.append aligned701_702

def missing702_703 : List (BitVec (edgeCount 12)) :=
  [missing702]
abbrev records702_703 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record702]
theorem aligned702_703 :
    AlignedValid 12 2 missing702_703 records702_703 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check702
    maskCheck702 AlignedValid.nil

def missing703_704 : List (BitVec (edgeCount 12)) :=
  [missing703]
abbrev records703_704 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record703]
theorem aligned703_704 :
    AlignedValid 12 2 missing703_704 records703_704 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check703
    maskCheck703 AlignedValid.nil

def missing702_704 : List (BitVec (edgeCount 12)) :=
  missing702_703 ++ missing703_704
abbrev records702_704 : List Blob :=
  records702_703 ++ records703_704
theorem aligned702_704 :
    AlignedValid 12 2 missing702_704 records702_704 :=
  aligned702_703.append aligned703_704

def missing700_704 : List (BitVec (edgeCount 12)) :=
  missing700_702 ++ missing702_704
abbrev records700_704 : List Blob :=
  records700_702 ++ records702_704
theorem aligned700_704 :
    AlignedValid 12 2 missing700_704 records700_704 :=
  aligned700_702.append aligned702_704

def missing696_704 : List (BitVec (edgeCount 12)) :=
  missing696_700 ++ missing700_704
abbrev records696_704 : List Blob :=
  records696_700 ++ records700_704
theorem aligned696_704 :
    AlignedValid 12 2 missing696_704 records696_704 :=
  aligned696_700.append aligned700_704

def missing688_704 : List (BitVec (edgeCount 12)) :=
  missing688_696 ++ missing696_704
abbrev records688_704 : List Blob :=
  records688_696 ++ records696_704
theorem aligned688_704 :
    AlignedValid 12 2 missing688_704 records688_704 :=
  aligned688_696.append aligned696_704

def missing672_704 : List (BitVec (edgeCount 12)) :=
  missing672_688 ++ missing688_704
abbrev records672_704 : List Blob :=
  records672_688 ++ records688_704
theorem aligned672_704 :
    AlignedValid 12 2 missing672_704 records672_704 :=
  aligned672_688.append aligned688_704

def missing640_704 : List (BitVec (edgeCount 12)) :=
  missing640_672 ++ missing672_704
abbrev records640_704 : List Blob :=
  records640_672 ++ records672_704
theorem aligned640_704 :
    AlignedValid 12 2 missing640_704 records640_704 :=
  aligned640_672.append aligned672_704

def missing704_705 : List (BitVec (edgeCount 12)) :=
  [missing704]
abbrev records704_705 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record704]
theorem aligned704_705 :
    AlignedValid 12 2 missing704_705 records704_705 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check704
    maskCheck704 AlignedValid.nil

def missing705_706 : List (BitVec (edgeCount 12)) :=
  [missing705]
abbrev records705_706 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record705]
theorem aligned705_706 :
    AlignedValid 12 2 missing705_706 records705_706 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check705
    maskCheck705 AlignedValid.nil

def missing704_706 : List (BitVec (edgeCount 12)) :=
  missing704_705 ++ missing705_706
abbrev records704_706 : List Blob :=
  records704_705 ++ records705_706
theorem aligned704_706 :
    AlignedValid 12 2 missing704_706 records704_706 :=
  aligned704_705.append aligned705_706

def missing706_707 : List (BitVec (edgeCount 12)) :=
  [missing706]
abbrev records706_707 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record706]
theorem aligned706_707 :
    AlignedValid 12 2 missing706_707 records706_707 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check706
    maskCheck706 AlignedValid.nil

def missing707_708 : List (BitVec (edgeCount 12)) :=
  [missing707]
abbrev records707_708 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record707]
theorem aligned707_708 :
    AlignedValid 12 2 missing707_708 records707_708 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check707
    maskCheck707 AlignedValid.nil

def missing706_708 : List (BitVec (edgeCount 12)) :=
  missing706_707 ++ missing707_708
abbrev records706_708 : List Blob :=
  records706_707 ++ records707_708
theorem aligned706_708 :
    AlignedValid 12 2 missing706_708 records706_708 :=
  aligned706_707.append aligned707_708

def missing704_708 : List (BitVec (edgeCount 12)) :=
  missing704_706 ++ missing706_708
abbrev records704_708 : List Blob :=
  records704_706 ++ records706_708
theorem aligned704_708 :
    AlignedValid 12 2 missing704_708 records704_708 :=
  aligned704_706.append aligned706_708

def missing708_709 : List (BitVec (edgeCount 12)) :=
  [missing708]
abbrev records708_709 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record708]
theorem aligned708_709 :
    AlignedValid 12 2 missing708_709 records708_709 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check708
    maskCheck708 AlignedValid.nil

def missing709_710 : List (BitVec (edgeCount 12)) :=
  [missing709]
abbrev records709_710 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record709]
theorem aligned709_710 :
    AlignedValid 12 2 missing709_710 records709_710 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check709
    maskCheck709 AlignedValid.nil

def missing708_710 : List (BitVec (edgeCount 12)) :=
  missing708_709 ++ missing709_710
abbrev records708_710 : List Blob :=
  records708_709 ++ records709_710
theorem aligned708_710 :
    AlignedValid 12 2 missing708_710 records708_710 :=
  aligned708_709.append aligned709_710

def missing710_711 : List (BitVec (edgeCount 12)) :=
  [missing710]
abbrev records710_711 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record710]
theorem aligned710_711 :
    AlignedValid 12 2 missing710_711 records710_711 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check710
    maskCheck710 AlignedValid.nil

def missing711_712 : List (BitVec (edgeCount 12)) :=
  [missing711]
abbrev records711_712 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record711]
theorem aligned711_712 :
    AlignedValid 12 2 missing711_712 records711_712 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check711
    maskCheck711 AlignedValid.nil

def missing710_712 : List (BitVec (edgeCount 12)) :=
  missing710_711 ++ missing711_712
abbrev records710_712 : List Blob :=
  records710_711 ++ records711_712
theorem aligned710_712 :
    AlignedValid 12 2 missing710_712 records710_712 :=
  aligned710_711.append aligned711_712

def missing708_712 : List (BitVec (edgeCount 12)) :=
  missing708_710 ++ missing710_712
abbrev records708_712 : List Blob :=
  records708_710 ++ records710_712
theorem aligned708_712 :
    AlignedValid 12 2 missing708_712 records708_712 :=
  aligned708_710.append aligned710_712

def missing704_712 : List (BitVec (edgeCount 12)) :=
  missing704_708 ++ missing708_712
abbrev records704_712 : List Blob :=
  records704_708 ++ records708_712
theorem aligned704_712 :
    AlignedValid 12 2 missing704_712 records704_712 :=
  aligned704_708.append aligned708_712

def missing712_713 : List (BitVec (edgeCount 12)) :=
  [missing712]
abbrev records712_713 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record712]
theorem aligned712_713 :
    AlignedValid 12 2 missing712_713 records712_713 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check712
    maskCheck712 AlignedValid.nil

def missing713_714 : List (BitVec (edgeCount 12)) :=
  [missing713]
abbrev records713_714 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record713]
theorem aligned713_714 :
    AlignedValid 12 2 missing713_714 records713_714 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check713
    maskCheck713 AlignedValid.nil

def missing712_714 : List (BitVec (edgeCount 12)) :=
  missing712_713 ++ missing713_714
abbrev records712_714 : List Blob :=
  records712_713 ++ records713_714
theorem aligned712_714 :
    AlignedValid 12 2 missing712_714 records712_714 :=
  aligned712_713.append aligned713_714

def missing714_715 : List (BitVec (edgeCount 12)) :=
  [missing714]
abbrev records714_715 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record714]
theorem aligned714_715 :
    AlignedValid 12 2 missing714_715 records714_715 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check714
    maskCheck714 AlignedValid.nil

def missing715_716 : List (BitVec (edgeCount 12)) :=
  [missing715]
abbrev records715_716 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record715]
theorem aligned715_716 :
    AlignedValid 12 2 missing715_716 records715_716 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check715
    maskCheck715 AlignedValid.nil

def missing714_716 : List (BitVec (edgeCount 12)) :=
  missing714_715 ++ missing715_716
abbrev records714_716 : List Blob :=
  records714_715 ++ records715_716
theorem aligned714_716 :
    AlignedValid 12 2 missing714_716 records714_716 :=
  aligned714_715.append aligned715_716

def missing712_716 : List (BitVec (edgeCount 12)) :=
  missing712_714 ++ missing714_716
abbrev records712_716 : List Blob :=
  records712_714 ++ records714_716
theorem aligned712_716 :
    AlignedValid 12 2 missing712_716 records712_716 :=
  aligned712_714.append aligned714_716

def missing716_717 : List (BitVec (edgeCount 12)) :=
  [missing716]
abbrev records716_717 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record716]
theorem aligned716_717 :
    AlignedValid 12 2 missing716_717 records716_717 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check716
    maskCheck716 AlignedValid.nil

def missing717_718 : List (BitVec (edgeCount 12)) :=
  [missing717]
abbrev records717_718 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record717]
theorem aligned717_718 :
    AlignedValid 12 2 missing717_718 records717_718 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check717
    maskCheck717 AlignedValid.nil

def missing716_718 : List (BitVec (edgeCount 12)) :=
  missing716_717 ++ missing717_718
abbrev records716_718 : List Blob :=
  records716_717 ++ records717_718
theorem aligned716_718 :
    AlignedValid 12 2 missing716_718 records716_718 :=
  aligned716_717.append aligned717_718

def missing718_719 : List (BitVec (edgeCount 12)) :=
  [missing718]
abbrev records718_719 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record718]
theorem aligned718_719 :
    AlignedValid 12 2 missing718_719 records718_719 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check718
    maskCheck718 AlignedValid.nil

def missing719_720 : List (BitVec (edgeCount 12)) :=
  [missing719]
abbrev records719_720 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record719]
theorem aligned719_720 :
    AlignedValid 12 2 missing719_720 records719_720 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check719
    maskCheck719 AlignedValid.nil

def missing718_720 : List (BitVec (edgeCount 12)) :=
  missing718_719 ++ missing719_720
abbrev records718_720 : List Blob :=
  records718_719 ++ records719_720
theorem aligned718_720 :
    AlignedValid 12 2 missing718_720 records718_720 :=
  aligned718_719.append aligned719_720

def missing716_720 : List (BitVec (edgeCount 12)) :=
  missing716_718 ++ missing718_720
abbrev records716_720 : List Blob :=
  records716_718 ++ records718_720
theorem aligned716_720 :
    AlignedValid 12 2 missing716_720 records716_720 :=
  aligned716_718.append aligned718_720

def missing712_720 : List (BitVec (edgeCount 12)) :=
  missing712_716 ++ missing716_720
abbrev records712_720 : List Blob :=
  records712_716 ++ records716_720
theorem aligned712_720 :
    AlignedValid 12 2 missing712_720 records712_720 :=
  aligned712_716.append aligned716_720

def missing704_720 : List (BitVec (edgeCount 12)) :=
  missing704_712 ++ missing712_720
abbrev records704_720 : List Blob :=
  records704_712 ++ records712_720
theorem aligned704_720 :
    AlignedValid 12 2 missing704_720 records704_720 :=
  aligned704_712.append aligned712_720

def missing720_721 : List (BitVec (edgeCount 12)) :=
  [missing720]
abbrev records720_721 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record720]
theorem aligned720_721 :
    AlignedValid 12 2 missing720_721 records720_721 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check720
    maskCheck720 AlignedValid.nil

def missing721_722 : List (BitVec (edgeCount 12)) :=
  [missing721]
abbrev records721_722 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record721]
theorem aligned721_722 :
    AlignedValid 12 2 missing721_722 records721_722 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check721
    maskCheck721 AlignedValid.nil

def missing720_722 : List (BitVec (edgeCount 12)) :=
  missing720_721 ++ missing721_722
abbrev records720_722 : List Blob :=
  records720_721 ++ records721_722
theorem aligned720_722 :
    AlignedValid 12 2 missing720_722 records720_722 :=
  aligned720_721.append aligned721_722

def missing722_723 : List (BitVec (edgeCount 12)) :=
  [missing722]
abbrev records722_723 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record722]
theorem aligned722_723 :
    AlignedValid 12 2 missing722_723 records722_723 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check722
    maskCheck722 AlignedValid.nil

def missing723_724 : List (BitVec (edgeCount 12)) :=
  [missing723]
abbrev records723_724 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record723]
theorem aligned723_724 :
    AlignedValid 12 2 missing723_724 records723_724 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check723
    maskCheck723 AlignedValid.nil

def missing722_724 : List (BitVec (edgeCount 12)) :=
  missing722_723 ++ missing723_724
abbrev records722_724 : List Blob :=
  records722_723 ++ records723_724
theorem aligned722_724 :
    AlignedValid 12 2 missing722_724 records722_724 :=
  aligned722_723.append aligned723_724

def missing720_724 : List (BitVec (edgeCount 12)) :=
  missing720_722 ++ missing722_724
abbrev records720_724 : List Blob :=
  records720_722 ++ records722_724
theorem aligned720_724 :
    AlignedValid 12 2 missing720_724 records720_724 :=
  aligned720_722.append aligned722_724

def missing724_725 : List (BitVec (edgeCount 12)) :=
  [missing724]
abbrev records724_725 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record724]
theorem aligned724_725 :
    AlignedValid 12 2 missing724_725 records724_725 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check724
    maskCheck724 AlignedValid.nil

def missing725_726 : List (BitVec (edgeCount 12)) :=
  [missing725]
abbrev records725_726 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record725]
theorem aligned725_726 :
    AlignedValid 12 2 missing725_726 records725_726 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check725
    maskCheck725 AlignedValid.nil

def missing724_726 : List (BitVec (edgeCount 12)) :=
  missing724_725 ++ missing725_726
abbrev records724_726 : List Blob :=
  records724_725 ++ records725_726
theorem aligned724_726 :
    AlignedValid 12 2 missing724_726 records724_726 :=
  aligned724_725.append aligned725_726

def missing726_727 : List (BitVec (edgeCount 12)) :=
  [missing726]
abbrev records726_727 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record726]
theorem aligned726_727 :
    AlignedValid 12 2 missing726_727 records726_727 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check726
    maskCheck726 AlignedValid.nil

def missing727_728 : List (BitVec (edgeCount 12)) :=
  [missing727]
abbrev records727_728 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record727]
theorem aligned727_728 :
    AlignedValid 12 2 missing727_728 records727_728 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check727
    maskCheck727 AlignedValid.nil

def missing726_728 : List (BitVec (edgeCount 12)) :=
  missing726_727 ++ missing727_728
abbrev records726_728 : List Blob :=
  records726_727 ++ records727_728
theorem aligned726_728 :
    AlignedValid 12 2 missing726_728 records726_728 :=
  aligned726_727.append aligned727_728

def missing724_728 : List (BitVec (edgeCount 12)) :=
  missing724_726 ++ missing726_728
abbrev records724_728 : List Blob :=
  records724_726 ++ records726_728
theorem aligned724_728 :
    AlignedValid 12 2 missing724_728 records724_728 :=
  aligned724_726.append aligned726_728

def missing720_728 : List (BitVec (edgeCount 12)) :=
  missing720_724 ++ missing724_728
abbrev records720_728 : List Blob :=
  records720_724 ++ records724_728
theorem aligned720_728 :
    AlignedValid 12 2 missing720_728 records720_728 :=
  aligned720_724.append aligned724_728

def missing728_729 : List (BitVec (edgeCount 12)) :=
  [missing728]
abbrev records728_729 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record728]
theorem aligned728_729 :
    AlignedValid 12 2 missing728_729 records728_729 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check728
    maskCheck728 AlignedValid.nil

def missing729_730 : List (BitVec (edgeCount 12)) :=
  [missing729]
abbrev records729_730 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record729]
theorem aligned729_730 :
    AlignedValid 12 2 missing729_730 records729_730 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check729
    maskCheck729 AlignedValid.nil

def missing728_730 : List (BitVec (edgeCount 12)) :=
  missing728_729 ++ missing729_730
abbrev records728_730 : List Blob :=
  records728_729 ++ records729_730
theorem aligned728_730 :
    AlignedValid 12 2 missing728_730 records728_730 :=
  aligned728_729.append aligned729_730

def missing730_731 : List (BitVec (edgeCount 12)) :=
  [missing730]
abbrev records730_731 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record730]
theorem aligned730_731 :
    AlignedValid 12 2 missing730_731 records730_731 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check730
    maskCheck730 AlignedValid.nil

def missing731_732 : List (BitVec (edgeCount 12)) :=
  [missing731]
abbrev records731_732 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record731]
theorem aligned731_732 :
    AlignedValid 12 2 missing731_732 records731_732 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check731
    maskCheck731 AlignedValid.nil

def missing730_732 : List (BitVec (edgeCount 12)) :=
  missing730_731 ++ missing731_732
abbrev records730_732 : List Blob :=
  records730_731 ++ records731_732
theorem aligned730_732 :
    AlignedValid 12 2 missing730_732 records730_732 :=
  aligned730_731.append aligned731_732

def missing728_732 : List (BitVec (edgeCount 12)) :=
  missing728_730 ++ missing730_732
abbrev records728_732 : List Blob :=
  records728_730 ++ records730_732
theorem aligned728_732 :
    AlignedValid 12 2 missing728_732 records728_732 :=
  aligned728_730.append aligned730_732

def missing732_733 : List (BitVec (edgeCount 12)) :=
  [missing732]
abbrev records732_733 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record732]
theorem aligned732_733 :
    AlignedValid 12 2 missing732_733 records732_733 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check732
    maskCheck732 AlignedValid.nil

def missing733_734 : List (BitVec (edgeCount 12)) :=
  [missing733]
abbrev records733_734 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record733]
theorem aligned733_734 :
    AlignedValid 12 2 missing733_734 records733_734 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check733
    maskCheck733 AlignedValid.nil

def missing732_734 : List (BitVec (edgeCount 12)) :=
  missing732_733 ++ missing733_734
abbrev records732_734 : List Blob :=
  records732_733 ++ records733_734
theorem aligned732_734 :
    AlignedValid 12 2 missing732_734 records732_734 :=
  aligned732_733.append aligned733_734

def missing734_735 : List (BitVec (edgeCount 12)) :=
  [missing734]
abbrev records734_735 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record734]
theorem aligned734_735 :
    AlignedValid 12 2 missing734_735 records734_735 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check734
    maskCheck734 AlignedValid.nil

def missing735_736 : List (BitVec (edgeCount 12)) :=
  [missing735]
abbrev records735_736 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record735]
theorem aligned735_736 :
    AlignedValid 12 2 missing735_736 records735_736 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check735
    maskCheck735 AlignedValid.nil

def missing734_736 : List (BitVec (edgeCount 12)) :=
  missing734_735 ++ missing735_736
abbrev records734_736 : List Blob :=
  records734_735 ++ records735_736
theorem aligned734_736 :
    AlignedValid 12 2 missing734_736 records734_736 :=
  aligned734_735.append aligned735_736

def missing732_736 : List (BitVec (edgeCount 12)) :=
  missing732_734 ++ missing734_736
abbrev records732_736 : List Blob :=
  records732_734 ++ records734_736
theorem aligned732_736 :
    AlignedValid 12 2 missing732_736 records732_736 :=
  aligned732_734.append aligned734_736

def missing728_736 : List (BitVec (edgeCount 12)) :=
  missing728_732 ++ missing732_736
abbrev records728_736 : List Blob :=
  records728_732 ++ records732_736
theorem aligned728_736 :
    AlignedValid 12 2 missing728_736 records728_736 :=
  aligned728_732.append aligned732_736

def missing720_736 : List (BitVec (edgeCount 12)) :=
  missing720_728 ++ missing728_736
abbrev records720_736 : List Blob :=
  records720_728 ++ records728_736
theorem aligned720_736 :
    AlignedValid 12 2 missing720_736 records720_736 :=
  aligned720_728.append aligned728_736

def missing704_736 : List (BitVec (edgeCount 12)) :=
  missing704_720 ++ missing720_736
abbrev records704_736 : List Blob :=
  records704_720 ++ records720_736
theorem aligned704_736 :
    AlignedValid 12 2 missing704_736 records704_736 :=
  aligned704_720.append aligned720_736

def missing736_737 : List (BitVec (edgeCount 12)) :=
  [missing736]
abbrev records736_737 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record736]
theorem aligned736_737 :
    AlignedValid 12 2 missing736_737 records736_737 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check736
    maskCheck736 AlignedValid.nil

def missing737_738 : List (BitVec (edgeCount 12)) :=
  [missing737]
abbrev records737_738 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record737]
theorem aligned737_738 :
    AlignedValid 12 2 missing737_738 records737_738 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check737
    maskCheck737 AlignedValid.nil

def missing736_738 : List (BitVec (edgeCount 12)) :=
  missing736_737 ++ missing737_738
abbrev records736_738 : List Blob :=
  records736_737 ++ records737_738
theorem aligned736_738 :
    AlignedValid 12 2 missing736_738 records736_738 :=
  aligned736_737.append aligned737_738

def missing738_739 : List (BitVec (edgeCount 12)) :=
  [missing738]
abbrev records738_739 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record738]
theorem aligned738_739 :
    AlignedValid 12 2 missing738_739 records738_739 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check738
    maskCheck738 AlignedValid.nil

def missing739_740 : List (BitVec (edgeCount 12)) :=
  [missing739]
abbrev records739_740 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record739]
theorem aligned739_740 :
    AlignedValid 12 2 missing739_740 records739_740 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check739
    maskCheck739 AlignedValid.nil

def missing738_740 : List (BitVec (edgeCount 12)) :=
  missing738_739 ++ missing739_740
abbrev records738_740 : List Blob :=
  records738_739 ++ records739_740
theorem aligned738_740 :
    AlignedValid 12 2 missing738_740 records738_740 :=
  aligned738_739.append aligned739_740

def missing736_740 : List (BitVec (edgeCount 12)) :=
  missing736_738 ++ missing738_740
abbrev records736_740 : List Blob :=
  records736_738 ++ records738_740
theorem aligned736_740 :
    AlignedValid 12 2 missing736_740 records736_740 :=
  aligned736_738.append aligned738_740

def missing740_741 : List (BitVec (edgeCount 12)) :=
  [missing740]
abbrev records740_741 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record740]
theorem aligned740_741 :
    AlignedValid 12 2 missing740_741 records740_741 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check740
    maskCheck740 AlignedValid.nil

def missing741_742 : List (BitVec (edgeCount 12)) :=
  [missing741]
abbrev records741_742 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record741]
theorem aligned741_742 :
    AlignedValid 12 2 missing741_742 records741_742 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check741
    maskCheck741 AlignedValid.nil

def missing740_742 : List (BitVec (edgeCount 12)) :=
  missing740_741 ++ missing741_742
abbrev records740_742 : List Blob :=
  records740_741 ++ records741_742
theorem aligned740_742 :
    AlignedValid 12 2 missing740_742 records740_742 :=
  aligned740_741.append aligned741_742

def missing742_743 : List (BitVec (edgeCount 12)) :=
  [missing742]
abbrev records742_743 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record742]
theorem aligned742_743 :
    AlignedValid 12 2 missing742_743 records742_743 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check742
    maskCheck742 AlignedValid.nil

def missing743_744 : List (BitVec (edgeCount 12)) :=
  [missing743]
abbrev records743_744 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record743]
theorem aligned743_744 :
    AlignedValid 12 2 missing743_744 records743_744 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check743
    maskCheck743 AlignedValid.nil

def missing742_744 : List (BitVec (edgeCount 12)) :=
  missing742_743 ++ missing743_744
abbrev records742_744 : List Blob :=
  records742_743 ++ records743_744
theorem aligned742_744 :
    AlignedValid 12 2 missing742_744 records742_744 :=
  aligned742_743.append aligned743_744

def missing740_744 : List (BitVec (edgeCount 12)) :=
  missing740_742 ++ missing742_744
abbrev records740_744 : List Blob :=
  records740_742 ++ records742_744
theorem aligned740_744 :
    AlignedValid 12 2 missing740_744 records740_744 :=
  aligned740_742.append aligned742_744

def missing736_744 : List (BitVec (edgeCount 12)) :=
  missing736_740 ++ missing740_744
abbrev records736_744 : List Blob :=
  records736_740 ++ records740_744
theorem aligned736_744 :
    AlignedValid 12 2 missing736_744 records736_744 :=
  aligned736_740.append aligned740_744

def missing744_745 : List (BitVec (edgeCount 12)) :=
  [missing744]
abbrev records744_745 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record744]
theorem aligned744_745 :
    AlignedValid 12 2 missing744_745 records744_745 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check744
    maskCheck744 AlignedValid.nil

def missing745_746 : List (BitVec (edgeCount 12)) :=
  [missing745]
abbrev records745_746 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record745]
theorem aligned745_746 :
    AlignedValid 12 2 missing745_746 records745_746 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check745
    maskCheck745 AlignedValid.nil

def missing744_746 : List (BitVec (edgeCount 12)) :=
  missing744_745 ++ missing745_746
abbrev records744_746 : List Blob :=
  records744_745 ++ records745_746
theorem aligned744_746 :
    AlignedValid 12 2 missing744_746 records744_746 :=
  aligned744_745.append aligned745_746

def missing746_747 : List (BitVec (edgeCount 12)) :=
  [missing746]
abbrev records746_747 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record746]
theorem aligned746_747 :
    AlignedValid 12 2 missing746_747 records746_747 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check746
    maskCheck746 AlignedValid.nil

def missing747_748 : List (BitVec (edgeCount 12)) :=
  [missing747]
abbrev records747_748 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record747]
theorem aligned747_748 :
    AlignedValid 12 2 missing747_748 records747_748 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check747
    maskCheck747 AlignedValid.nil

def missing746_748 : List (BitVec (edgeCount 12)) :=
  missing746_747 ++ missing747_748
abbrev records746_748 : List Blob :=
  records746_747 ++ records747_748
theorem aligned746_748 :
    AlignedValid 12 2 missing746_748 records746_748 :=
  aligned746_747.append aligned747_748

def missing744_748 : List (BitVec (edgeCount 12)) :=
  missing744_746 ++ missing746_748
abbrev records744_748 : List Blob :=
  records744_746 ++ records746_748
theorem aligned744_748 :
    AlignedValid 12 2 missing744_748 records744_748 :=
  aligned744_746.append aligned746_748

def missing748_749 : List (BitVec (edgeCount 12)) :=
  [missing748]
abbrev records748_749 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record748]
theorem aligned748_749 :
    AlignedValid 12 2 missing748_749 records748_749 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check748
    maskCheck748 AlignedValid.nil

def missing749_750 : List (BitVec (edgeCount 12)) :=
  [missing749]
abbrev records749_750 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record749]
theorem aligned749_750 :
    AlignedValid 12 2 missing749_750 records749_750 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check749
    maskCheck749 AlignedValid.nil

def missing748_750 : List (BitVec (edgeCount 12)) :=
  missing748_749 ++ missing749_750
abbrev records748_750 : List Blob :=
  records748_749 ++ records749_750
theorem aligned748_750 :
    AlignedValid 12 2 missing748_750 records748_750 :=
  aligned748_749.append aligned749_750

def missing750_751 : List (BitVec (edgeCount 12)) :=
  [missing750]
abbrev records750_751 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record750]
theorem aligned750_751 :
    AlignedValid 12 2 missing750_751 records750_751 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check750
    maskCheck750 AlignedValid.nil

def missing751_752 : List (BitVec (edgeCount 12)) :=
  [missing751]
abbrev records751_752 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record751]
theorem aligned751_752 :
    AlignedValid 12 2 missing751_752 records751_752 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check751
    maskCheck751 AlignedValid.nil

def missing750_752 : List (BitVec (edgeCount 12)) :=
  missing750_751 ++ missing751_752
abbrev records750_752 : List Blob :=
  records750_751 ++ records751_752
theorem aligned750_752 :
    AlignedValid 12 2 missing750_752 records750_752 :=
  aligned750_751.append aligned751_752

def missing748_752 : List (BitVec (edgeCount 12)) :=
  missing748_750 ++ missing750_752
abbrev records748_752 : List Blob :=
  records748_750 ++ records750_752
theorem aligned748_752 :
    AlignedValid 12 2 missing748_752 records748_752 :=
  aligned748_750.append aligned750_752

def missing744_752 : List (BitVec (edgeCount 12)) :=
  missing744_748 ++ missing748_752
abbrev records744_752 : List Blob :=
  records744_748 ++ records748_752
theorem aligned744_752 :
    AlignedValid 12 2 missing744_752 records744_752 :=
  aligned744_748.append aligned748_752

def missing736_752 : List (BitVec (edgeCount 12)) :=
  missing736_744 ++ missing744_752
abbrev records736_752 : List Blob :=
  records736_744 ++ records744_752
theorem aligned736_752 :
    AlignedValid 12 2 missing736_752 records736_752 :=
  aligned736_744.append aligned744_752

def missing752_753 : List (BitVec (edgeCount 12)) :=
  [missing752]
abbrev records752_753 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record752]
theorem aligned752_753 :
    AlignedValid 12 2 missing752_753 records752_753 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check752
    maskCheck752 AlignedValid.nil

def missing753_754 : List (BitVec (edgeCount 12)) :=
  [missing753]
abbrev records753_754 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record753]
theorem aligned753_754 :
    AlignedValid 12 2 missing753_754 records753_754 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check753
    maskCheck753 AlignedValid.nil

def missing752_754 : List (BitVec (edgeCount 12)) :=
  missing752_753 ++ missing753_754
abbrev records752_754 : List Blob :=
  records752_753 ++ records753_754
theorem aligned752_754 :
    AlignedValid 12 2 missing752_754 records752_754 :=
  aligned752_753.append aligned753_754

def missing754_755 : List (BitVec (edgeCount 12)) :=
  [missing754]
abbrev records754_755 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record754]
theorem aligned754_755 :
    AlignedValid 12 2 missing754_755 records754_755 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check754
    maskCheck754 AlignedValid.nil

def missing755_756 : List (BitVec (edgeCount 12)) :=
  [missing755]
abbrev records755_756 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record755]
theorem aligned755_756 :
    AlignedValid 12 2 missing755_756 records755_756 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check755
    maskCheck755 AlignedValid.nil

def missing754_756 : List (BitVec (edgeCount 12)) :=
  missing754_755 ++ missing755_756
abbrev records754_756 : List Blob :=
  records754_755 ++ records755_756
theorem aligned754_756 :
    AlignedValid 12 2 missing754_756 records754_756 :=
  aligned754_755.append aligned755_756

def missing752_756 : List (BitVec (edgeCount 12)) :=
  missing752_754 ++ missing754_756
abbrev records752_756 : List Blob :=
  records752_754 ++ records754_756
theorem aligned752_756 :
    AlignedValid 12 2 missing752_756 records752_756 :=
  aligned752_754.append aligned754_756

def missing756_757 : List (BitVec (edgeCount 12)) :=
  [missing756]
abbrev records756_757 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record756]
theorem aligned756_757 :
    AlignedValid 12 2 missing756_757 records756_757 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check756
    maskCheck756 AlignedValid.nil

def missing757_758 : List (BitVec (edgeCount 12)) :=
  [missing757]
abbrev records757_758 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record757]
theorem aligned757_758 :
    AlignedValid 12 2 missing757_758 records757_758 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check757
    maskCheck757 AlignedValid.nil

def missing756_758 : List (BitVec (edgeCount 12)) :=
  missing756_757 ++ missing757_758
abbrev records756_758 : List Blob :=
  records756_757 ++ records757_758
theorem aligned756_758 :
    AlignedValid 12 2 missing756_758 records756_758 :=
  aligned756_757.append aligned757_758

def missing758_759 : List (BitVec (edgeCount 12)) :=
  [missing758]
abbrev records758_759 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record758]
theorem aligned758_759 :
    AlignedValid 12 2 missing758_759 records758_759 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check758
    maskCheck758 AlignedValid.nil

def missing759_760 : List (BitVec (edgeCount 12)) :=
  [missing759]
abbrev records759_760 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record759]
theorem aligned759_760 :
    AlignedValid 12 2 missing759_760 records759_760 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check759
    maskCheck759 AlignedValid.nil

def missing758_760 : List (BitVec (edgeCount 12)) :=
  missing758_759 ++ missing759_760
abbrev records758_760 : List Blob :=
  records758_759 ++ records759_760
theorem aligned758_760 :
    AlignedValid 12 2 missing758_760 records758_760 :=
  aligned758_759.append aligned759_760

def missing756_760 : List (BitVec (edgeCount 12)) :=
  missing756_758 ++ missing758_760
abbrev records756_760 : List Blob :=
  records756_758 ++ records758_760
theorem aligned756_760 :
    AlignedValid 12 2 missing756_760 records756_760 :=
  aligned756_758.append aligned758_760

def missing752_760 : List (BitVec (edgeCount 12)) :=
  missing752_756 ++ missing756_760
abbrev records752_760 : List Blob :=
  records752_756 ++ records756_760
theorem aligned752_760 :
    AlignedValid 12 2 missing752_760 records752_760 :=
  aligned752_756.append aligned756_760

def missing760_761 : List (BitVec (edgeCount 12)) :=
  [missing760]
abbrev records760_761 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record760]
theorem aligned760_761 :
    AlignedValid 12 2 missing760_761 records760_761 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check760
    maskCheck760 AlignedValid.nil

def missing761_762 : List (BitVec (edgeCount 12)) :=
  [missing761]
abbrev records761_762 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record761]
theorem aligned761_762 :
    AlignedValid 12 2 missing761_762 records761_762 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check761
    maskCheck761 AlignedValid.nil

def missing760_762 : List (BitVec (edgeCount 12)) :=
  missing760_761 ++ missing761_762
abbrev records760_762 : List Blob :=
  records760_761 ++ records761_762
theorem aligned760_762 :
    AlignedValid 12 2 missing760_762 records760_762 :=
  aligned760_761.append aligned761_762

def missing762_763 : List (BitVec (edgeCount 12)) :=
  [missing762]
abbrev records762_763 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record762]
theorem aligned762_763 :
    AlignedValid 12 2 missing762_763 records762_763 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check762
    maskCheck762 AlignedValid.nil

def missing763_764 : List (BitVec (edgeCount 12)) :=
  [missing763]
abbrev records763_764 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record763]
theorem aligned763_764 :
    AlignedValid 12 2 missing763_764 records763_764 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check763
    maskCheck763 AlignedValid.nil

def missing762_764 : List (BitVec (edgeCount 12)) :=
  missing762_763 ++ missing763_764
abbrev records762_764 : List Blob :=
  records762_763 ++ records763_764
theorem aligned762_764 :
    AlignedValid 12 2 missing762_764 records762_764 :=
  aligned762_763.append aligned763_764

def missing760_764 : List (BitVec (edgeCount 12)) :=
  missing760_762 ++ missing762_764
abbrev records760_764 : List Blob :=
  records760_762 ++ records762_764
theorem aligned760_764 :
    AlignedValid 12 2 missing760_764 records760_764 :=
  aligned760_762.append aligned762_764

def missing764_765 : List (BitVec (edgeCount 12)) :=
  [missing764]
abbrev records764_765 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record764]
theorem aligned764_765 :
    AlignedValid 12 2 missing764_765 records764_765 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check764
    maskCheck764 AlignedValid.nil

def missing765_766 : List (BitVec (edgeCount 12)) :=
  [missing765]
abbrev records765_766 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record765]
theorem aligned765_766 :
    AlignedValid 12 2 missing765_766 records765_766 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check765
    maskCheck765 AlignedValid.nil

def missing764_766 : List (BitVec (edgeCount 12)) :=
  missing764_765 ++ missing765_766
abbrev records764_766 : List Blob :=
  records764_765 ++ records765_766
theorem aligned764_766 :
    AlignedValid 12 2 missing764_766 records764_766 :=
  aligned764_765.append aligned765_766

def missing766_767 : List (BitVec (edgeCount 12)) :=
  [missing766]
abbrev records766_767 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record766]
theorem aligned766_767 :
    AlignedValid 12 2 missing766_767 records766_767 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check766
    maskCheck766 AlignedValid.nil

def missing767_768 : List (BitVec (edgeCount 12)) :=
  [missing767]
abbrev records767_768 : List Blob :=
  [StrongPackedBucketN12A2Shard005.record767]
theorem aligned767_768 :
    AlignedValid 12 2 missing767_768 records767_768 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard005.check767
    maskCheck767 AlignedValid.nil

def missing766_768 : List (BitVec (edgeCount 12)) :=
  missing766_767 ++ missing767_768
abbrev records766_768 : List Blob :=
  records766_767 ++ records767_768
theorem aligned766_768 :
    AlignedValid 12 2 missing766_768 records766_768 :=
  aligned766_767.append aligned767_768

def missing764_768 : List (BitVec (edgeCount 12)) :=
  missing764_766 ++ missing766_768
abbrev records764_768 : List Blob :=
  records764_766 ++ records766_768
theorem aligned764_768 :
    AlignedValid 12 2 missing764_768 records764_768 :=
  aligned764_766.append aligned766_768

def missing760_768 : List (BitVec (edgeCount 12)) :=
  missing760_764 ++ missing764_768
abbrev records760_768 : List Blob :=
  records760_764 ++ records764_768
theorem aligned760_768 :
    AlignedValid 12 2 missing760_768 records760_768 :=
  aligned760_764.append aligned764_768

def missing752_768 : List (BitVec (edgeCount 12)) :=
  missing752_760 ++ missing760_768
abbrev records752_768 : List Blob :=
  records752_760 ++ records760_768
theorem aligned752_768 :
    AlignedValid 12 2 missing752_768 records752_768 :=
  aligned752_760.append aligned760_768

def missing736_768 : List (BitVec (edgeCount 12)) :=
  missing736_752 ++ missing752_768
abbrev records736_768 : List Blob :=
  records736_752 ++ records752_768
theorem aligned736_768 :
    AlignedValid 12 2 missing736_768 records736_768 :=
  aligned736_752.append aligned752_768

def missing704_768 : List (BitVec (edgeCount 12)) :=
  missing704_736 ++ missing736_768
abbrev records704_768 : List Blob :=
  records704_736 ++ records736_768
theorem aligned704_768 :
    AlignedValid 12 2 missing704_768 records704_768 :=
  aligned704_736.append aligned736_768

def missing640_768 : List (BitVec (edgeCount 12)) :=
  missing640_704 ++ missing704_768
abbrev records640_768 : List Blob :=
  records640_704 ++ records704_768
theorem aligned640_768 :
    AlignedValid 12 2 missing640_768 records640_768 :=
  aligned640_704.append aligned704_768

abbrev missing : List (BitVec (edgeCount 12)) := missing640_768
abbrev records : List Blob := records640_768
theorem aligned : AlignedValid 12 2 missing records := aligned640_768

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A2AlignedShard005
