/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A3Shard060

/-! Decode-only alignment checks for n=12, a=3, records 7680--7807. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A3AlignedShard060

open PackedBucketCertificate

def missing7680 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5873679901682302976
theorem maskCheck7680 :
    checkMaskFor missing7680 StrongPackedBucketN12A3Shard060.record7680 = true := by
  decide

def missing7681 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5945737495720230912
theorem maskCheck7681 :
    checkMaskFor missing7681 StrongPackedBucketN12A3Shard060.record7681 = true := by
  decide

def missing7682 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6378083059947798528
theorem maskCheck7682 :
    checkMaskFor missing7682 StrongPackedBucketN12A3Shard060.record7682 = true := by
  decide

def missing7683 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8107465316858068992
theorem maskCheck7683 :
    checkMaskFor missing7683 StrongPackedBucketN12A3Shard060.record7683 = true := by
  decide

def missing7684 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13944130433930231808
theorem maskCheck7684 :
    checkMaskFor missing7684 StrongPackedBucketN12A3Shard060.record7684 = true := by
  decide

def missing7685 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18699931640433475584
theorem maskCheck7685 :
    checkMaskFor missing7685 StrongPackedBucketN12A3Shard060.record7685 = true := by
  decide

def missing7686 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18916104422547259392
theorem maskCheck7686 :
    checkMaskFor missing7686 StrongPackedBucketN12A3Shard060.record7686 = true := by
  decide

def missing7687 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19132277204661043200
theorem maskCheck7687 :
    checkMaskFor missing7687 StrongPackedBucketN12A3Shard060.record7687 = true := by
  decide

def missing7688 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19204334798698971136
theorem maskCheck7688 :
    checkMaskFor missing7688 StrongPackedBucketN12A3Shard060.record7688 = true := by
  decide

def missing7689 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19456536377831718912
theorem maskCheck7689 :
    checkMaskFor missing7689 StrongPackedBucketN12A3Shard060.record7689 = true := by
  decide

def missing7690 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19708737956964466688
theorem maskCheck7690 :
    checkMaskFor missing7690 StrongPackedBucketN12A3Shard060.record7690 = true := by
  decide

def missing7691 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19780795551002394624
theorem maskCheck7691 :
    checkMaskFor missing7691 StrongPackedBucketN12A3Shard060.record7691 = true := by
  decide

def missing7692 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20032997130135142400
theorem maskCheck7692 :
    checkMaskFor missing7692 StrongPackedBucketN12A3Shard060.record7692 = true := by
  decide

def missing7693 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20213141115229962240
theorem maskCheck7693 :
    checkMaskFor missing7693 StrongPackedBucketN12A3Shard060.record7693 = true := by
  decide

def missing7694 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20321227506286854144
theorem maskCheck7694 :
    checkMaskFor missing7694 StrongPackedBucketN12A3Shard060.record7694 = true := by
  decide

def missing7695 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21942523372140232704
theorem maskCheck7695 :
    checkMaskFor missing7695 StrongPackedBucketN12A3Shard060.record7695 = true := by
  decide

def missing7696 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22050609763197124608
theorem maskCheck7696 :
    checkMaskFor missing7696 StrongPackedBucketN12A3Shard060.record7696 = true := by
  decide

def missing7697 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22482955327424692224
theorem maskCheck7697 :
    checkMaskFor missing7697 StrongPackedBucketN12A3Shard060.record7697 = true := by
  decide

def missing7698 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23167502470785007616
theorem maskCheck7698 :
    checkMaskFor missing7698 StrongPackedBucketN12A3Shard060.record7698 = true := by
  decide

def missing7699 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23239560064822935552
theorem maskCheck7699 :
    checkMaskFor missing7699 StrongPackedBucketN12A3Shard060.record7699 = true := by
  decide

def missing7700 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23671905629050503168
theorem maskCheck7700 :
    checkMaskFor missing7700 StrongPackedBucketN12A3Shard060.record7700 = true := by
  decide

def missing7701 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 24248366381353926656
theorem maskCheck7701 :
    checkMaskFor missing7701 StrongPackedBucketN12A3Shard060.record7701 = true := by
  decide

def missing7702 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37146675714143027200
theorem maskCheck7702 :
    checkMaskFor missing7702 StrongPackedBucketN12A3Shard060.record7702 = true := by
  decide

def missing7703 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37362848496256811008
theorem maskCheck7703 :
    checkMaskFor missing7703 StrongPackedBucketN12A3Shard060.record7703 = true := by
  decide

def missing7704 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37579021278370594816
theorem maskCheck7704 :
    checkMaskFor missing7704 StrongPackedBucketN12A3Shard060.record7704 = true := by
  decide

def missing7705 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37651078872408522752
theorem maskCheck7705 :
    checkMaskFor missing7705 StrongPackedBucketN12A3Shard060.record7705 = true := by
  decide

def missing7706 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37903280451541270528
theorem maskCheck7706 :
    checkMaskFor missing7706 StrongPackedBucketN12A3Shard060.record7706 = true := by
  decide

def missing7707 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38155482030674018304
theorem maskCheck7707 :
    checkMaskFor missing7707 StrongPackedBucketN12A3Shard060.record7707 = true := by
  decide

def missing7708 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38227539624711946240
theorem maskCheck7708 :
    checkMaskFor missing7708 StrongPackedBucketN12A3Shard060.record7708 = true := by
  decide

def missing7709 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38479741203844694016
theorem maskCheck7709 :
    checkMaskFor missing7709 StrongPackedBucketN12A3Shard060.record7709 = true := by
  decide

def missing7710 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41614246544494559232
theorem maskCheck7710 :
    checkMaskFor missing7710 StrongPackedBucketN12A3Shard060.record7710 = true := by
  decide

def missing7711 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41686304138532487168
theorem maskCheck7711 :
    checkMaskFor missing7711 StrongPackedBucketN12A3Shard060.record7711 = true := by
  decide

def missing7712 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42118649702760054784
theorem maskCheck7712 :
    checkMaskFor missing7712 StrongPackedBucketN12A3Shard060.record7712 = true := by
  decide

def missing7713 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42695110455063478272
theorem maskCheck7713 :
    checkMaskFor missing7713 StrongPackedBucketN12A3Shard060.record7713 = true := by
  decide

def missing7714 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55449304599776722944
theorem maskCheck7714 :
    checkMaskFor missing7714 StrongPackedBucketN12A3Shard060.record7714 = true := by
  decide

def missing7715 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55521362193814650880
theorem maskCheck7715 :
    checkMaskFor missing7715 StrongPackedBucketN12A3Shard060.record7715 = true := by
  decide

def missing7716 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 59988933024166182912
theorem maskCheck7716 :
    checkMaskFor missing7716 StrongPackedBucketN12A3Shard060.record7716 = true := by
  decide

def missing7717 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 542156814689501184
theorem maskCheck7717 :
    checkMaskFor missing7717 StrongPackedBucketN12A3Shard060.record7717 = true := by
  decide

def missing7718 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 830387190841212928
theorem maskCheck7718 :
    checkMaskFor missing7718 StrongPackedBucketN12A3Shard060.record7718 = true := by
  decide

def missing7719 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1046559972954996736
theorem maskCheck7719 :
    checkMaskFor missing7719 StrongPackedBucketN12A3Shard060.record7719 = true := by
  decide

def missing7720 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1082588769973960704
theorem maskCheck7720 :
    checkMaskFor missing7720 StrongPackedBucketN12A3Shard060.record7720 = true := by
  decide

def missing7721 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1839193507372204032
theorem maskCheck7721 :
    checkMaskFor missing7721 StrongPackedBucketN12A3Shard060.record7721 = true := by
  decide

def missing7722 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1911251101410131968
theorem maskCheck7722 :
    checkMaskFor missing7722 StrongPackedBucketN12A3Shard060.record7722 = true := by
  decide

def missing7723 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1947279898429095936
theorem maskCheck7723 :
    checkMaskFor missing7723 StrongPackedBucketN12A3Shard060.record7723 = true := by
  decide

def missing7724 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2163452680542879744
theorem maskCheck7724 :
    checkMaskFor missing7724 StrongPackedBucketN12A3Shard060.record7724 = true := by
  decide

def missing7725 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2559769447751483392
theorem maskCheck7725 :
    checkMaskFor missing7725 StrongPackedBucketN12A3Shard060.record7725 = true := by
  decide

def missing7726 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2775942229865267200
theorem maskCheck7726 :
    checkMaskFor missing7726 StrongPackedBucketN12A3Shard060.record7726 = true := by
  decide

def missing7727 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2811971026884231168
theorem maskCheck7727 :
    checkMaskFor missing7727 StrongPackedBucketN12A3Shard060.record7727 = true := by
  decide

def missing7728 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2992115011979051008
theorem maskCheck7728 :
    checkMaskFor missing7728 StrongPackedBucketN12A3Shard060.record7728 = true := by
  decide

def missing7729 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3064172606016978944
theorem maskCheck7729 :
    checkMaskFor missing7729 StrongPackedBucketN12A3Shard060.record7729 = true := by
  decide

def missing7730 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3100201403035942912
theorem maskCheck7730 :
    checkMaskFor missing7730 StrongPackedBucketN12A3Shard060.record7730 = true := by
  decide

def missing7731 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3316374185149726720
theorem maskCheck7731 :
    checkMaskFor missing7731 StrongPackedBucketN12A3Shard060.record7731 = true := by
  decide

def missing7732 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4072978922547970048
theorem maskCheck7732 :
    checkMaskFor missing7732 StrongPackedBucketN12A3Shard060.record7732 = true := by
  decide

def missing7733 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4109007719566934016
theorem maskCheck7733 :
    checkMaskFor missing7733 StrongPackedBucketN12A3Shard060.record7733 = true := by
  decide

def missing7734 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4181065313604861952
theorem maskCheck7734 :
    checkMaskFor missing7734 StrongPackedBucketN12A3Shard060.record7734 = true := by
  decide

def missing7735 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4865612456965177344
theorem maskCheck7735 :
    checkMaskFor missing7735 StrongPackedBucketN12A3Shard060.record7735 = true := by
  decide

def missing7736 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5081785239078961152
theorem maskCheck7736 :
    checkMaskFor missing7736 StrongPackedBucketN12A3Shard060.record7736 = true := by
  decide

def missing7737 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5117814036097925120
theorem maskCheck7737 :
    checkMaskFor missing7737 StrongPackedBucketN12A3Shard060.record7737 = true := by
  decide

def missing7738 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5297958021192744960
theorem maskCheck7738 :
    checkMaskFor missing7738 StrongPackedBucketN12A3Shard060.record7738 = true := by
  decide

def missing7739 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5370015615230672896
theorem maskCheck7739 :
    checkMaskFor missing7739 StrongPackedBucketN12A3Shard060.record7739 = true := by
  decide

def missing7740 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5406044412249636864
theorem maskCheck7740 :
    checkMaskFor missing7740 StrongPackedBucketN12A3Shard060.record7740 = true := by
  decide

def missing7741 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5622217194363420672
theorem maskCheck7741 :
    checkMaskFor missing7741 StrongPackedBucketN12A3Shard060.record7741 = true := by
  decide

def missing7742 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6378821931761664000
theorem maskCheck7742 :
    checkMaskFor missing7742 StrongPackedBucketN12A3Shard060.record7742 = true := by
  decide

def missing7743 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6414850728780627968
theorem maskCheck7743 :
    checkMaskFor missing7743 StrongPackedBucketN12A3Shard060.record7743 = true := by
  decide

def missing7744 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6486908322818555904
theorem maskCheck7744 :
    checkMaskFor missing7744 StrongPackedBucketN12A3Shard060.record7744 = true := by
  decide

def missing7745 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7027340278103015424
theorem maskCheck7745 :
    checkMaskFor missing7745 StrongPackedBucketN12A3Shard060.record7745 = true := by
  decide

def missing7746 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7099397872140943360
theorem maskCheck7746 :
    checkMaskFor missing7746 StrongPackedBucketN12A3Shard060.record7746 = true := by
  decide

def missing7747 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7135426669159907328
theorem maskCheck7747 :
    checkMaskFor missing7747 StrongPackedBucketN12A3Shard060.record7747 = true := by
  decide

def missing7748 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7351599451273691136
theorem maskCheck7748 :
    checkMaskFor missing7748 StrongPackedBucketN12A3Shard060.record7748 = true := by
  decide

def missing7749 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7531743436368510976
theorem maskCheck7749 :
    checkMaskFor missing7749 StrongPackedBucketN12A3Shard060.record7749 = true := by
  decide

def missing7750 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7567772233387474944
theorem maskCheck7750 :
    checkMaskFor missing7750 StrongPackedBucketN12A3Shard060.record7750 = true := by
  decide

def missing7751 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7639829827425402880
theorem maskCheck7751 :
    checkMaskFor missing7751 StrongPackedBucketN12A3Shard060.record7751 = true := by
  decide

def missing7752 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8648636143956393984
theorem maskCheck7752 :
    checkMaskFor missing7752 StrongPackedBucketN12A3Shard060.record7752 = true := by
  decide

def missing7753 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9477298475392565248
theorem maskCheck7753 :
    checkMaskFor missing7753 StrongPackedBucketN12A3Shard060.record7753 = true := by
  decide

def missing7754 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9729500054525313024
theorem maskCheck7754 :
    checkMaskFor missing7754 StrongPackedBucketN12A3Shard060.record7754 = true := by
  decide

def missing7755 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9909644039620132864
theorem maskCheck7755 :
    checkMaskFor missing7755 StrongPackedBucketN12A3Shard060.record7755 = true := by
  decide

def missing7756 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10017730430677024768
theorem maskCheck7756 :
    checkMaskFor missing7756 StrongPackedBucketN12A3Shard060.record7756 = true := by
  decide

def missing7757 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11026536747208015872
theorem maskCheck7757 :
    checkMaskFor missing7757 StrongPackedBucketN12A3Shard060.record7757 = true := by
  decide

def missing7758 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11639026296530403328
theorem maskCheck7758 :
    checkMaskFor missing7758 StrongPackedBucketN12A3Shard060.record7758 = true := by
  decide

def missing7759 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11747112687587295232
theorem maskCheck7759 :
    checkMaskFor missing7759 StrongPackedBucketN12A3Shard060.record7759 = true := by
  decide

def missing7760 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12179458251814862848
theorem maskCheck7760 :
    checkMaskFor missing7760 StrongPackedBucketN12A3Shard060.record7760 = true := by
  decide

def missing7761 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13944869305744097280
theorem maskCheck7761 :
    checkMaskFor missing7761 StrongPackedBucketN12A3Shard060.record7761 = true := by
  decide

def missing7762 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14052955696800989184
theorem maskCheck7762 :
    checkMaskFor missing7762 StrongPackedBucketN12A3Shard060.record7762 = true := by
  decide

def missing7763 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14485301261028556800
theorem maskCheck7763 :
    checkMaskFor missing7763 StrongPackedBucketN12A3Shard060.record7763 = true := by
  decide

def missing7764 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 16214683517938827264
theorem maskCheck7764 :
    checkMaskFor missing7764 StrongPackedBucketN12A3Shard060.record7764 = true := by
  decide

def missing7765 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18700670512247341056
theorem maskCheck7765 :
    checkMaskFor missing7765 StrongPackedBucketN12A3Shard060.record7765 = true := by
  decide

def missing7766 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18916843294361124864
theorem maskCheck7766 :
    checkMaskFor missing7766 StrongPackedBucketN12A3Shard060.record7766 = true := by
  decide

def missing7767 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18952872091380088832
theorem maskCheck7767 :
    checkMaskFor missing7767 StrongPackedBucketN12A3Shard060.record7767 = true := by
  decide

def missing7768 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19133016076474908672
theorem maskCheck7768 :
    checkMaskFor missing7768 StrongPackedBucketN12A3Shard060.record7768 = true := by
  decide

def missing7769 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19205073670512836608
theorem maskCheck7769 :
    checkMaskFor missing7769 StrongPackedBucketN12A3Shard060.record7769 = true := by
  decide

def missing7770 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19241102467531800576
theorem maskCheck7770 :
    checkMaskFor missing7770 StrongPackedBucketN12A3Shard060.record7770 = true := by
  decide

def missing7771 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19457275249645584384
theorem maskCheck7771 :
    checkMaskFor missing7771 StrongPackedBucketN12A3Shard060.record7771 = true := by
  decide

def missing7772 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20213879987043827712
theorem maskCheck7772 :
    checkMaskFor missing7772 StrongPackedBucketN12A3Shard060.record7772 = true := by
  decide

def missing7773 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20249908784062791680
theorem maskCheck7773 :
    checkMaskFor missing7773 StrongPackedBucketN12A3Shard060.record7773 = true := by
  decide

def missing7774 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20321966378100719616
theorem maskCheck7774 :
    checkMaskFor missing7774 StrongPackedBucketN12A3Shard060.record7774 = true := by
  decide

def missing7775 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20862398333385179136
theorem maskCheck7775 :
    checkMaskFor missing7775 StrongPackedBucketN12A3Shard060.record7775 = true := by
  decide

def missing7776 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20934455927423107072
theorem maskCheck7776 :
    checkMaskFor missing7776 StrongPackedBucketN12A3Shard060.record7776 = true := by
  decide

def missing7777 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20970484724442071040
theorem maskCheck7777 :
    checkMaskFor missing7777 StrongPackedBucketN12A3Shard060.record7777 = true := by
  decide

def missing7778 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21186657506555854848
theorem maskCheck7778 :
    checkMaskFor missing7778 StrongPackedBucketN12A3Shard060.record7778 = true := by
  decide

def missing7779 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21366801491650674688
theorem maskCheck7779 :
    checkMaskFor missing7779 StrongPackedBucketN12A3Shard060.record7779 = true := by
  decide

def missing7780 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21402830288669638656
theorem maskCheck7780 :
    checkMaskFor missing7780 StrongPackedBucketN12A3Shard060.record7780 = true := by
  decide

def missing7781 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21474887882707566592
theorem maskCheck7781 :
    checkMaskFor missing7781 StrongPackedBucketN12A3Shard060.record7781 = true := by
  decide

def missing7782 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22483694199238557696
theorem maskCheck7782 :
    checkMaskFor missing7782 StrongPackedBucketN12A3Shard060.record7782 = true := by
  decide

def missing7783 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23168241342598873088
theorem maskCheck7783 :
    checkMaskFor missing7783 StrongPackedBucketN12A3Shard060.record7783 = true := by
  decide

def missing7784 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23240298936636801024
theorem maskCheck7784 :
    checkMaskFor missing7784 StrongPackedBucketN12A3Shard060.record7784 = true := by
  decide

def missing7785 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23276327733655764992
theorem maskCheck7785 :
    checkMaskFor missing7785 StrongPackedBucketN12A3Shard060.record7785 = true := by
  decide

def missing7786 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23492500515769548800
theorem maskCheck7786 :
    checkMaskFor missing7786 StrongPackedBucketN12A3Shard060.record7786 = true := by
  decide

def missing7787 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23672644500864368640
theorem maskCheck7787 :
    checkMaskFor missing7787 StrongPackedBucketN12A3Shard060.record7787 = true := by
  decide

def missing7788 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23708673297883332608
theorem maskCheck7788 :
    checkMaskFor missing7788 StrongPackedBucketN12A3Shard060.record7788 = true := by
  decide

def missing7789 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23780730891921260544
theorem maskCheck7789 :
    checkMaskFor missing7789 StrongPackedBucketN12A3Shard060.record7789 = true := by
  decide

def missing7790 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 24789537208452251648
theorem maskCheck7790 :
    checkMaskFor missing7790 StrongPackedBucketN12A3Shard060.record7790 = true := by
  decide

def missing7791 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 25402026757774639104
theorem maskCheck7791 :
    checkMaskFor missing7791 StrongPackedBucketN12A3Shard060.record7791 = true := by
  decide

def missing7792 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 25438055554793603072
theorem maskCheck7792 :
    checkMaskFor missing7792 StrongPackedBucketN12A3Shard060.record7792 = true := by
  decide

def missing7793 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 25510113148831531008
theorem maskCheck7793 :
    checkMaskFor missing7793 StrongPackedBucketN12A3Shard060.record7793 = true := by
  decide

def missing7794 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 25942458713059098624
theorem maskCheck7794 :
    checkMaskFor missing7794 StrongPackedBucketN12A3Shard060.record7794 = true := by
  decide

def missing7795 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27779927361026260992
theorem maskCheck7795 :
    checkMaskFor missing7795 StrongPackedBucketN12A3Shard060.record7795 = true := by
  decide

def missing7796 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27888013752083152896
theorem maskCheck7796 :
    checkMaskFor missing7796 StrongPackedBucketN12A3Shard060.record7796 = true := by
  decide

def missing7797 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28320359316310720512
theorem maskCheck7797 :
    checkMaskFor missing7797 StrongPackedBucketN12A3Shard060.record7797 = true := by
  decide

def missing7798 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 30049741573220990976
theorem maskCheck7798 :
    checkMaskFor missing7798 StrongPackedBucketN12A3Shard060.record7798 = true := by
  decide

def missing7799 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32355584582434684928
theorem maskCheck7799 :
    checkMaskFor missing7799 StrongPackedBucketN12A3Shard060.record7799 = true := by
  decide

def missing7800 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37147414585956892672
theorem maskCheck7800 :
    checkMaskFor missing7800 StrongPackedBucketN12A3Shard060.record7800 = true := by
  decide

def missing7801 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37363587368070676480
theorem maskCheck7801 :
    checkMaskFor missing7801 StrongPackedBucketN12A3Shard060.record7801 = true := by
  decide

def missing7802 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37399616165089640448
theorem maskCheck7802 :
    checkMaskFor missing7802 StrongPackedBucketN12A3Shard060.record7802 = true := by
  decide

def missing7803 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37579760150184460288
theorem maskCheck7803 :
    checkMaskFor missing7803 StrongPackedBucketN12A3Shard060.record7803 = true := by
  decide

def missing7804 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37651817744222388224
theorem maskCheck7804 :
    checkMaskFor missing7804 StrongPackedBucketN12A3Shard060.record7804 = true := by
  decide

def missing7805 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37687846541241352192
theorem maskCheck7805 :
    checkMaskFor missing7805 StrongPackedBucketN12A3Shard060.record7805 = true := by
  decide

def missing7806 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37904019323355136000
theorem maskCheck7806 :
    checkMaskFor missing7806 StrongPackedBucketN12A3Shard060.record7806 = true := by
  decide

def missing7807 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38660624060753379328
theorem maskCheck7807 :
    checkMaskFor missing7807 StrongPackedBucketN12A3Shard060.record7807 = true := by
  decide

def missing7680_7681 : List (BitVec (edgeCount 12)) :=
  [missing7680]
abbrev records7680_7681 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7680]
theorem aligned7680_7681 :
    AlignedValid 12 3 missing7680_7681 records7680_7681 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7680
    maskCheck7680 AlignedValid.nil

def missing7681_7682 : List (BitVec (edgeCount 12)) :=
  [missing7681]
abbrev records7681_7682 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7681]
theorem aligned7681_7682 :
    AlignedValid 12 3 missing7681_7682 records7681_7682 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7681
    maskCheck7681 AlignedValid.nil

def missing7680_7682 : List (BitVec (edgeCount 12)) :=
  missing7680_7681 ++ missing7681_7682
abbrev records7680_7682 : List Blob :=
  records7680_7681 ++ records7681_7682
theorem aligned7680_7682 :
    AlignedValid 12 3 missing7680_7682 records7680_7682 :=
  aligned7680_7681.append aligned7681_7682

def missing7682_7683 : List (BitVec (edgeCount 12)) :=
  [missing7682]
abbrev records7682_7683 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7682]
theorem aligned7682_7683 :
    AlignedValid 12 3 missing7682_7683 records7682_7683 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7682
    maskCheck7682 AlignedValid.nil

def missing7683_7684 : List (BitVec (edgeCount 12)) :=
  [missing7683]
abbrev records7683_7684 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7683]
theorem aligned7683_7684 :
    AlignedValid 12 3 missing7683_7684 records7683_7684 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7683
    maskCheck7683 AlignedValid.nil

def missing7682_7684 : List (BitVec (edgeCount 12)) :=
  missing7682_7683 ++ missing7683_7684
abbrev records7682_7684 : List Blob :=
  records7682_7683 ++ records7683_7684
theorem aligned7682_7684 :
    AlignedValid 12 3 missing7682_7684 records7682_7684 :=
  aligned7682_7683.append aligned7683_7684

def missing7680_7684 : List (BitVec (edgeCount 12)) :=
  missing7680_7682 ++ missing7682_7684
abbrev records7680_7684 : List Blob :=
  records7680_7682 ++ records7682_7684
theorem aligned7680_7684 :
    AlignedValid 12 3 missing7680_7684 records7680_7684 :=
  aligned7680_7682.append aligned7682_7684

def missing7684_7685 : List (BitVec (edgeCount 12)) :=
  [missing7684]
abbrev records7684_7685 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7684]
theorem aligned7684_7685 :
    AlignedValid 12 3 missing7684_7685 records7684_7685 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7684
    maskCheck7684 AlignedValid.nil

def missing7685_7686 : List (BitVec (edgeCount 12)) :=
  [missing7685]
abbrev records7685_7686 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7685]
theorem aligned7685_7686 :
    AlignedValid 12 3 missing7685_7686 records7685_7686 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7685
    maskCheck7685 AlignedValid.nil

def missing7684_7686 : List (BitVec (edgeCount 12)) :=
  missing7684_7685 ++ missing7685_7686
abbrev records7684_7686 : List Blob :=
  records7684_7685 ++ records7685_7686
theorem aligned7684_7686 :
    AlignedValid 12 3 missing7684_7686 records7684_7686 :=
  aligned7684_7685.append aligned7685_7686

def missing7686_7687 : List (BitVec (edgeCount 12)) :=
  [missing7686]
abbrev records7686_7687 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7686]
theorem aligned7686_7687 :
    AlignedValid 12 3 missing7686_7687 records7686_7687 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7686
    maskCheck7686 AlignedValid.nil

def missing7687_7688 : List (BitVec (edgeCount 12)) :=
  [missing7687]
abbrev records7687_7688 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7687]
theorem aligned7687_7688 :
    AlignedValid 12 3 missing7687_7688 records7687_7688 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7687
    maskCheck7687 AlignedValid.nil

def missing7686_7688 : List (BitVec (edgeCount 12)) :=
  missing7686_7687 ++ missing7687_7688
abbrev records7686_7688 : List Blob :=
  records7686_7687 ++ records7687_7688
theorem aligned7686_7688 :
    AlignedValid 12 3 missing7686_7688 records7686_7688 :=
  aligned7686_7687.append aligned7687_7688

def missing7684_7688 : List (BitVec (edgeCount 12)) :=
  missing7684_7686 ++ missing7686_7688
abbrev records7684_7688 : List Blob :=
  records7684_7686 ++ records7686_7688
theorem aligned7684_7688 :
    AlignedValid 12 3 missing7684_7688 records7684_7688 :=
  aligned7684_7686.append aligned7686_7688

def missing7680_7688 : List (BitVec (edgeCount 12)) :=
  missing7680_7684 ++ missing7684_7688
abbrev records7680_7688 : List Blob :=
  records7680_7684 ++ records7684_7688
theorem aligned7680_7688 :
    AlignedValid 12 3 missing7680_7688 records7680_7688 :=
  aligned7680_7684.append aligned7684_7688

def missing7688_7689 : List (BitVec (edgeCount 12)) :=
  [missing7688]
abbrev records7688_7689 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7688]
theorem aligned7688_7689 :
    AlignedValid 12 3 missing7688_7689 records7688_7689 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7688
    maskCheck7688 AlignedValid.nil

def missing7689_7690 : List (BitVec (edgeCount 12)) :=
  [missing7689]
abbrev records7689_7690 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7689]
theorem aligned7689_7690 :
    AlignedValid 12 3 missing7689_7690 records7689_7690 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7689
    maskCheck7689 AlignedValid.nil

def missing7688_7690 : List (BitVec (edgeCount 12)) :=
  missing7688_7689 ++ missing7689_7690
abbrev records7688_7690 : List Blob :=
  records7688_7689 ++ records7689_7690
theorem aligned7688_7690 :
    AlignedValid 12 3 missing7688_7690 records7688_7690 :=
  aligned7688_7689.append aligned7689_7690

def missing7690_7691 : List (BitVec (edgeCount 12)) :=
  [missing7690]
abbrev records7690_7691 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7690]
theorem aligned7690_7691 :
    AlignedValid 12 3 missing7690_7691 records7690_7691 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7690
    maskCheck7690 AlignedValid.nil

def missing7691_7692 : List (BitVec (edgeCount 12)) :=
  [missing7691]
abbrev records7691_7692 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7691]
theorem aligned7691_7692 :
    AlignedValid 12 3 missing7691_7692 records7691_7692 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7691
    maskCheck7691 AlignedValid.nil

def missing7690_7692 : List (BitVec (edgeCount 12)) :=
  missing7690_7691 ++ missing7691_7692
abbrev records7690_7692 : List Blob :=
  records7690_7691 ++ records7691_7692
theorem aligned7690_7692 :
    AlignedValid 12 3 missing7690_7692 records7690_7692 :=
  aligned7690_7691.append aligned7691_7692

def missing7688_7692 : List (BitVec (edgeCount 12)) :=
  missing7688_7690 ++ missing7690_7692
abbrev records7688_7692 : List Blob :=
  records7688_7690 ++ records7690_7692
theorem aligned7688_7692 :
    AlignedValid 12 3 missing7688_7692 records7688_7692 :=
  aligned7688_7690.append aligned7690_7692

def missing7692_7693 : List (BitVec (edgeCount 12)) :=
  [missing7692]
abbrev records7692_7693 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7692]
theorem aligned7692_7693 :
    AlignedValid 12 3 missing7692_7693 records7692_7693 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7692
    maskCheck7692 AlignedValid.nil

def missing7693_7694 : List (BitVec (edgeCount 12)) :=
  [missing7693]
abbrev records7693_7694 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7693]
theorem aligned7693_7694 :
    AlignedValid 12 3 missing7693_7694 records7693_7694 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7693
    maskCheck7693 AlignedValid.nil

def missing7692_7694 : List (BitVec (edgeCount 12)) :=
  missing7692_7693 ++ missing7693_7694
abbrev records7692_7694 : List Blob :=
  records7692_7693 ++ records7693_7694
theorem aligned7692_7694 :
    AlignedValid 12 3 missing7692_7694 records7692_7694 :=
  aligned7692_7693.append aligned7693_7694

def missing7694_7695 : List (BitVec (edgeCount 12)) :=
  [missing7694]
abbrev records7694_7695 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7694]
theorem aligned7694_7695 :
    AlignedValid 12 3 missing7694_7695 records7694_7695 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7694
    maskCheck7694 AlignedValid.nil

def missing7695_7696 : List (BitVec (edgeCount 12)) :=
  [missing7695]
abbrev records7695_7696 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7695]
theorem aligned7695_7696 :
    AlignedValid 12 3 missing7695_7696 records7695_7696 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7695
    maskCheck7695 AlignedValid.nil

def missing7694_7696 : List (BitVec (edgeCount 12)) :=
  missing7694_7695 ++ missing7695_7696
abbrev records7694_7696 : List Blob :=
  records7694_7695 ++ records7695_7696
theorem aligned7694_7696 :
    AlignedValid 12 3 missing7694_7696 records7694_7696 :=
  aligned7694_7695.append aligned7695_7696

def missing7692_7696 : List (BitVec (edgeCount 12)) :=
  missing7692_7694 ++ missing7694_7696
abbrev records7692_7696 : List Blob :=
  records7692_7694 ++ records7694_7696
theorem aligned7692_7696 :
    AlignedValid 12 3 missing7692_7696 records7692_7696 :=
  aligned7692_7694.append aligned7694_7696

def missing7688_7696 : List (BitVec (edgeCount 12)) :=
  missing7688_7692 ++ missing7692_7696
abbrev records7688_7696 : List Blob :=
  records7688_7692 ++ records7692_7696
theorem aligned7688_7696 :
    AlignedValid 12 3 missing7688_7696 records7688_7696 :=
  aligned7688_7692.append aligned7692_7696

def missing7680_7696 : List (BitVec (edgeCount 12)) :=
  missing7680_7688 ++ missing7688_7696
abbrev records7680_7696 : List Blob :=
  records7680_7688 ++ records7688_7696
theorem aligned7680_7696 :
    AlignedValid 12 3 missing7680_7696 records7680_7696 :=
  aligned7680_7688.append aligned7688_7696

def missing7696_7697 : List (BitVec (edgeCount 12)) :=
  [missing7696]
abbrev records7696_7697 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7696]
theorem aligned7696_7697 :
    AlignedValid 12 3 missing7696_7697 records7696_7697 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7696
    maskCheck7696 AlignedValid.nil

def missing7697_7698 : List (BitVec (edgeCount 12)) :=
  [missing7697]
abbrev records7697_7698 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7697]
theorem aligned7697_7698 :
    AlignedValid 12 3 missing7697_7698 records7697_7698 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7697
    maskCheck7697 AlignedValid.nil

def missing7696_7698 : List (BitVec (edgeCount 12)) :=
  missing7696_7697 ++ missing7697_7698
abbrev records7696_7698 : List Blob :=
  records7696_7697 ++ records7697_7698
theorem aligned7696_7698 :
    AlignedValid 12 3 missing7696_7698 records7696_7698 :=
  aligned7696_7697.append aligned7697_7698

def missing7698_7699 : List (BitVec (edgeCount 12)) :=
  [missing7698]
abbrev records7698_7699 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7698]
theorem aligned7698_7699 :
    AlignedValid 12 3 missing7698_7699 records7698_7699 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7698
    maskCheck7698 AlignedValid.nil

def missing7699_7700 : List (BitVec (edgeCount 12)) :=
  [missing7699]
abbrev records7699_7700 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7699]
theorem aligned7699_7700 :
    AlignedValid 12 3 missing7699_7700 records7699_7700 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7699
    maskCheck7699 AlignedValid.nil

def missing7698_7700 : List (BitVec (edgeCount 12)) :=
  missing7698_7699 ++ missing7699_7700
abbrev records7698_7700 : List Blob :=
  records7698_7699 ++ records7699_7700
theorem aligned7698_7700 :
    AlignedValid 12 3 missing7698_7700 records7698_7700 :=
  aligned7698_7699.append aligned7699_7700

def missing7696_7700 : List (BitVec (edgeCount 12)) :=
  missing7696_7698 ++ missing7698_7700
abbrev records7696_7700 : List Blob :=
  records7696_7698 ++ records7698_7700
theorem aligned7696_7700 :
    AlignedValid 12 3 missing7696_7700 records7696_7700 :=
  aligned7696_7698.append aligned7698_7700

def missing7700_7701 : List (BitVec (edgeCount 12)) :=
  [missing7700]
abbrev records7700_7701 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7700]
theorem aligned7700_7701 :
    AlignedValid 12 3 missing7700_7701 records7700_7701 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7700
    maskCheck7700 AlignedValid.nil

def missing7701_7702 : List (BitVec (edgeCount 12)) :=
  [missing7701]
abbrev records7701_7702 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7701]
theorem aligned7701_7702 :
    AlignedValid 12 3 missing7701_7702 records7701_7702 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7701
    maskCheck7701 AlignedValid.nil

def missing7700_7702 : List (BitVec (edgeCount 12)) :=
  missing7700_7701 ++ missing7701_7702
abbrev records7700_7702 : List Blob :=
  records7700_7701 ++ records7701_7702
theorem aligned7700_7702 :
    AlignedValid 12 3 missing7700_7702 records7700_7702 :=
  aligned7700_7701.append aligned7701_7702

def missing7702_7703 : List (BitVec (edgeCount 12)) :=
  [missing7702]
abbrev records7702_7703 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7702]
theorem aligned7702_7703 :
    AlignedValid 12 3 missing7702_7703 records7702_7703 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7702
    maskCheck7702 AlignedValid.nil

def missing7703_7704 : List (BitVec (edgeCount 12)) :=
  [missing7703]
abbrev records7703_7704 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7703]
theorem aligned7703_7704 :
    AlignedValid 12 3 missing7703_7704 records7703_7704 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7703
    maskCheck7703 AlignedValid.nil

def missing7702_7704 : List (BitVec (edgeCount 12)) :=
  missing7702_7703 ++ missing7703_7704
abbrev records7702_7704 : List Blob :=
  records7702_7703 ++ records7703_7704
theorem aligned7702_7704 :
    AlignedValid 12 3 missing7702_7704 records7702_7704 :=
  aligned7702_7703.append aligned7703_7704

def missing7700_7704 : List (BitVec (edgeCount 12)) :=
  missing7700_7702 ++ missing7702_7704
abbrev records7700_7704 : List Blob :=
  records7700_7702 ++ records7702_7704
theorem aligned7700_7704 :
    AlignedValid 12 3 missing7700_7704 records7700_7704 :=
  aligned7700_7702.append aligned7702_7704

def missing7696_7704 : List (BitVec (edgeCount 12)) :=
  missing7696_7700 ++ missing7700_7704
abbrev records7696_7704 : List Blob :=
  records7696_7700 ++ records7700_7704
theorem aligned7696_7704 :
    AlignedValid 12 3 missing7696_7704 records7696_7704 :=
  aligned7696_7700.append aligned7700_7704

def missing7704_7705 : List (BitVec (edgeCount 12)) :=
  [missing7704]
abbrev records7704_7705 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7704]
theorem aligned7704_7705 :
    AlignedValid 12 3 missing7704_7705 records7704_7705 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7704
    maskCheck7704 AlignedValid.nil

def missing7705_7706 : List (BitVec (edgeCount 12)) :=
  [missing7705]
abbrev records7705_7706 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7705]
theorem aligned7705_7706 :
    AlignedValid 12 3 missing7705_7706 records7705_7706 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7705
    maskCheck7705 AlignedValid.nil

def missing7704_7706 : List (BitVec (edgeCount 12)) :=
  missing7704_7705 ++ missing7705_7706
abbrev records7704_7706 : List Blob :=
  records7704_7705 ++ records7705_7706
theorem aligned7704_7706 :
    AlignedValid 12 3 missing7704_7706 records7704_7706 :=
  aligned7704_7705.append aligned7705_7706

def missing7706_7707 : List (BitVec (edgeCount 12)) :=
  [missing7706]
abbrev records7706_7707 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7706]
theorem aligned7706_7707 :
    AlignedValid 12 3 missing7706_7707 records7706_7707 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7706
    maskCheck7706 AlignedValid.nil

def missing7707_7708 : List (BitVec (edgeCount 12)) :=
  [missing7707]
abbrev records7707_7708 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7707]
theorem aligned7707_7708 :
    AlignedValid 12 3 missing7707_7708 records7707_7708 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7707
    maskCheck7707 AlignedValid.nil

def missing7706_7708 : List (BitVec (edgeCount 12)) :=
  missing7706_7707 ++ missing7707_7708
abbrev records7706_7708 : List Blob :=
  records7706_7707 ++ records7707_7708
theorem aligned7706_7708 :
    AlignedValid 12 3 missing7706_7708 records7706_7708 :=
  aligned7706_7707.append aligned7707_7708

def missing7704_7708 : List (BitVec (edgeCount 12)) :=
  missing7704_7706 ++ missing7706_7708
abbrev records7704_7708 : List Blob :=
  records7704_7706 ++ records7706_7708
theorem aligned7704_7708 :
    AlignedValid 12 3 missing7704_7708 records7704_7708 :=
  aligned7704_7706.append aligned7706_7708

def missing7708_7709 : List (BitVec (edgeCount 12)) :=
  [missing7708]
abbrev records7708_7709 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7708]
theorem aligned7708_7709 :
    AlignedValid 12 3 missing7708_7709 records7708_7709 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7708
    maskCheck7708 AlignedValid.nil

def missing7709_7710 : List (BitVec (edgeCount 12)) :=
  [missing7709]
abbrev records7709_7710 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7709]
theorem aligned7709_7710 :
    AlignedValid 12 3 missing7709_7710 records7709_7710 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7709
    maskCheck7709 AlignedValid.nil

def missing7708_7710 : List (BitVec (edgeCount 12)) :=
  missing7708_7709 ++ missing7709_7710
abbrev records7708_7710 : List Blob :=
  records7708_7709 ++ records7709_7710
theorem aligned7708_7710 :
    AlignedValid 12 3 missing7708_7710 records7708_7710 :=
  aligned7708_7709.append aligned7709_7710

def missing7710_7711 : List (BitVec (edgeCount 12)) :=
  [missing7710]
abbrev records7710_7711 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7710]
theorem aligned7710_7711 :
    AlignedValid 12 3 missing7710_7711 records7710_7711 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7710
    maskCheck7710 AlignedValid.nil

def missing7711_7712 : List (BitVec (edgeCount 12)) :=
  [missing7711]
abbrev records7711_7712 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7711]
theorem aligned7711_7712 :
    AlignedValid 12 3 missing7711_7712 records7711_7712 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7711
    maskCheck7711 AlignedValid.nil

def missing7710_7712 : List (BitVec (edgeCount 12)) :=
  missing7710_7711 ++ missing7711_7712
abbrev records7710_7712 : List Blob :=
  records7710_7711 ++ records7711_7712
theorem aligned7710_7712 :
    AlignedValid 12 3 missing7710_7712 records7710_7712 :=
  aligned7710_7711.append aligned7711_7712

def missing7708_7712 : List (BitVec (edgeCount 12)) :=
  missing7708_7710 ++ missing7710_7712
abbrev records7708_7712 : List Blob :=
  records7708_7710 ++ records7710_7712
theorem aligned7708_7712 :
    AlignedValid 12 3 missing7708_7712 records7708_7712 :=
  aligned7708_7710.append aligned7710_7712

def missing7704_7712 : List (BitVec (edgeCount 12)) :=
  missing7704_7708 ++ missing7708_7712
abbrev records7704_7712 : List Blob :=
  records7704_7708 ++ records7708_7712
theorem aligned7704_7712 :
    AlignedValid 12 3 missing7704_7712 records7704_7712 :=
  aligned7704_7708.append aligned7708_7712

def missing7696_7712 : List (BitVec (edgeCount 12)) :=
  missing7696_7704 ++ missing7704_7712
abbrev records7696_7712 : List Blob :=
  records7696_7704 ++ records7704_7712
theorem aligned7696_7712 :
    AlignedValid 12 3 missing7696_7712 records7696_7712 :=
  aligned7696_7704.append aligned7704_7712

def missing7680_7712 : List (BitVec (edgeCount 12)) :=
  missing7680_7696 ++ missing7696_7712
abbrev records7680_7712 : List Blob :=
  records7680_7696 ++ records7696_7712
theorem aligned7680_7712 :
    AlignedValid 12 3 missing7680_7712 records7680_7712 :=
  aligned7680_7696.append aligned7696_7712

def missing7712_7713 : List (BitVec (edgeCount 12)) :=
  [missing7712]
abbrev records7712_7713 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7712]
theorem aligned7712_7713 :
    AlignedValid 12 3 missing7712_7713 records7712_7713 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7712
    maskCheck7712 AlignedValid.nil

def missing7713_7714 : List (BitVec (edgeCount 12)) :=
  [missing7713]
abbrev records7713_7714 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7713]
theorem aligned7713_7714 :
    AlignedValid 12 3 missing7713_7714 records7713_7714 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7713
    maskCheck7713 AlignedValid.nil

def missing7712_7714 : List (BitVec (edgeCount 12)) :=
  missing7712_7713 ++ missing7713_7714
abbrev records7712_7714 : List Blob :=
  records7712_7713 ++ records7713_7714
theorem aligned7712_7714 :
    AlignedValid 12 3 missing7712_7714 records7712_7714 :=
  aligned7712_7713.append aligned7713_7714

def missing7714_7715 : List (BitVec (edgeCount 12)) :=
  [missing7714]
abbrev records7714_7715 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7714]
theorem aligned7714_7715 :
    AlignedValid 12 3 missing7714_7715 records7714_7715 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7714
    maskCheck7714 AlignedValid.nil

def missing7715_7716 : List (BitVec (edgeCount 12)) :=
  [missing7715]
abbrev records7715_7716 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7715]
theorem aligned7715_7716 :
    AlignedValid 12 3 missing7715_7716 records7715_7716 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7715
    maskCheck7715 AlignedValid.nil

def missing7714_7716 : List (BitVec (edgeCount 12)) :=
  missing7714_7715 ++ missing7715_7716
abbrev records7714_7716 : List Blob :=
  records7714_7715 ++ records7715_7716
theorem aligned7714_7716 :
    AlignedValid 12 3 missing7714_7716 records7714_7716 :=
  aligned7714_7715.append aligned7715_7716

def missing7712_7716 : List (BitVec (edgeCount 12)) :=
  missing7712_7714 ++ missing7714_7716
abbrev records7712_7716 : List Blob :=
  records7712_7714 ++ records7714_7716
theorem aligned7712_7716 :
    AlignedValid 12 3 missing7712_7716 records7712_7716 :=
  aligned7712_7714.append aligned7714_7716

def missing7716_7717 : List (BitVec (edgeCount 12)) :=
  [missing7716]
abbrev records7716_7717 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7716]
theorem aligned7716_7717 :
    AlignedValid 12 3 missing7716_7717 records7716_7717 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7716
    maskCheck7716 AlignedValid.nil

def missing7717_7718 : List (BitVec (edgeCount 12)) :=
  [missing7717]
abbrev records7717_7718 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7717]
theorem aligned7717_7718 :
    AlignedValid 12 3 missing7717_7718 records7717_7718 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7717
    maskCheck7717 AlignedValid.nil

def missing7716_7718 : List (BitVec (edgeCount 12)) :=
  missing7716_7717 ++ missing7717_7718
abbrev records7716_7718 : List Blob :=
  records7716_7717 ++ records7717_7718
theorem aligned7716_7718 :
    AlignedValid 12 3 missing7716_7718 records7716_7718 :=
  aligned7716_7717.append aligned7717_7718

def missing7718_7719 : List (BitVec (edgeCount 12)) :=
  [missing7718]
abbrev records7718_7719 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7718]
theorem aligned7718_7719 :
    AlignedValid 12 3 missing7718_7719 records7718_7719 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7718
    maskCheck7718 AlignedValid.nil

def missing7719_7720 : List (BitVec (edgeCount 12)) :=
  [missing7719]
abbrev records7719_7720 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7719]
theorem aligned7719_7720 :
    AlignedValid 12 3 missing7719_7720 records7719_7720 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7719
    maskCheck7719 AlignedValid.nil

def missing7718_7720 : List (BitVec (edgeCount 12)) :=
  missing7718_7719 ++ missing7719_7720
abbrev records7718_7720 : List Blob :=
  records7718_7719 ++ records7719_7720
theorem aligned7718_7720 :
    AlignedValid 12 3 missing7718_7720 records7718_7720 :=
  aligned7718_7719.append aligned7719_7720

def missing7716_7720 : List (BitVec (edgeCount 12)) :=
  missing7716_7718 ++ missing7718_7720
abbrev records7716_7720 : List Blob :=
  records7716_7718 ++ records7718_7720
theorem aligned7716_7720 :
    AlignedValid 12 3 missing7716_7720 records7716_7720 :=
  aligned7716_7718.append aligned7718_7720

def missing7712_7720 : List (BitVec (edgeCount 12)) :=
  missing7712_7716 ++ missing7716_7720
abbrev records7712_7720 : List Blob :=
  records7712_7716 ++ records7716_7720
theorem aligned7712_7720 :
    AlignedValid 12 3 missing7712_7720 records7712_7720 :=
  aligned7712_7716.append aligned7716_7720

def missing7720_7721 : List (BitVec (edgeCount 12)) :=
  [missing7720]
abbrev records7720_7721 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7720]
theorem aligned7720_7721 :
    AlignedValid 12 3 missing7720_7721 records7720_7721 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7720
    maskCheck7720 AlignedValid.nil

def missing7721_7722 : List (BitVec (edgeCount 12)) :=
  [missing7721]
abbrev records7721_7722 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7721]
theorem aligned7721_7722 :
    AlignedValid 12 3 missing7721_7722 records7721_7722 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7721
    maskCheck7721 AlignedValid.nil

def missing7720_7722 : List (BitVec (edgeCount 12)) :=
  missing7720_7721 ++ missing7721_7722
abbrev records7720_7722 : List Blob :=
  records7720_7721 ++ records7721_7722
theorem aligned7720_7722 :
    AlignedValid 12 3 missing7720_7722 records7720_7722 :=
  aligned7720_7721.append aligned7721_7722

def missing7722_7723 : List (BitVec (edgeCount 12)) :=
  [missing7722]
abbrev records7722_7723 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7722]
theorem aligned7722_7723 :
    AlignedValid 12 3 missing7722_7723 records7722_7723 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7722
    maskCheck7722 AlignedValid.nil

def missing7723_7724 : List (BitVec (edgeCount 12)) :=
  [missing7723]
abbrev records7723_7724 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7723]
theorem aligned7723_7724 :
    AlignedValid 12 3 missing7723_7724 records7723_7724 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7723
    maskCheck7723 AlignedValid.nil

def missing7722_7724 : List (BitVec (edgeCount 12)) :=
  missing7722_7723 ++ missing7723_7724
abbrev records7722_7724 : List Blob :=
  records7722_7723 ++ records7723_7724
theorem aligned7722_7724 :
    AlignedValid 12 3 missing7722_7724 records7722_7724 :=
  aligned7722_7723.append aligned7723_7724

def missing7720_7724 : List (BitVec (edgeCount 12)) :=
  missing7720_7722 ++ missing7722_7724
abbrev records7720_7724 : List Blob :=
  records7720_7722 ++ records7722_7724
theorem aligned7720_7724 :
    AlignedValid 12 3 missing7720_7724 records7720_7724 :=
  aligned7720_7722.append aligned7722_7724

def missing7724_7725 : List (BitVec (edgeCount 12)) :=
  [missing7724]
abbrev records7724_7725 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7724]
theorem aligned7724_7725 :
    AlignedValid 12 3 missing7724_7725 records7724_7725 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7724
    maskCheck7724 AlignedValid.nil

def missing7725_7726 : List (BitVec (edgeCount 12)) :=
  [missing7725]
abbrev records7725_7726 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7725]
theorem aligned7725_7726 :
    AlignedValid 12 3 missing7725_7726 records7725_7726 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7725
    maskCheck7725 AlignedValid.nil

def missing7724_7726 : List (BitVec (edgeCount 12)) :=
  missing7724_7725 ++ missing7725_7726
abbrev records7724_7726 : List Blob :=
  records7724_7725 ++ records7725_7726
theorem aligned7724_7726 :
    AlignedValid 12 3 missing7724_7726 records7724_7726 :=
  aligned7724_7725.append aligned7725_7726

def missing7726_7727 : List (BitVec (edgeCount 12)) :=
  [missing7726]
abbrev records7726_7727 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7726]
theorem aligned7726_7727 :
    AlignedValid 12 3 missing7726_7727 records7726_7727 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7726
    maskCheck7726 AlignedValid.nil

def missing7727_7728 : List (BitVec (edgeCount 12)) :=
  [missing7727]
abbrev records7727_7728 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7727]
theorem aligned7727_7728 :
    AlignedValid 12 3 missing7727_7728 records7727_7728 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7727
    maskCheck7727 AlignedValid.nil

def missing7726_7728 : List (BitVec (edgeCount 12)) :=
  missing7726_7727 ++ missing7727_7728
abbrev records7726_7728 : List Blob :=
  records7726_7727 ++ records7727_7728
theorem aligned7726_7728 :
    AlignedValid 12 3 missing7726_7728 records7726_7728 :=
  aligned7726_7727.append aligned7727_7728

def missing7724_7728 : List (BitVec (edgeCount 12)) :=
  missing7724_7726 ++ missing7726_7728
abbrev records7724_7728 : List Blob :=
  records7724_7726 ++ records7726_7728
theorem aligned7724_7728 :
    AlignedValid 12 3 missing7724_7728 records7724_7728 :=
  aligned7724_7726.append aligned7726_7728

def missing7720_7728 : List (BitVec (edgeCount 12)) :=
  missing7720_7724 ++ missing7724_7728
abbrev records7720_7728 : List Blob :=
  records7720_7724 ++ records7724_7728
theorem aligned7720_7728 :
    AlignedValid 12 3 missing7720_7728 records7720_7728 :=
  aligned7720_7724.append aligned7724_7728

def missing7712_7728 : List (BitVec (edgeCount 12)) :=
  missing7712_7720 ++ missing7720_7728
abbrev records7712_7728 : List Blob :=
  records7712_7720 ++ records7720_7728
theorem aligned7712_7728 :
    AlignedValid 12 3 missing7712_7728 records7712_7728 :=
  aligned7712_7720.append aligned7720_7728

def missing7728_7729 : List (BitVec (edgeCount 12)) :=
  [missing7728]
abbrev records7728_7729 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7728]
theorem aligned7728_7729 :
    AlignedValid 12 3 missing7728_7729 records7728_7729 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7728
    maskCheck7728 AlignedValid.nil

def missing7729_7730 : List (BitVec (edgeCount 12)) :=
  [missing7729]
abbrev records7729_7730 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7729]
theorem aligned7729_7730 :
    AlignedValid 12 3 missing7729_7730 records7729_7730 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7729
    maskCheck7729 AlignedValid.nil

def missing7728_7730 : List (BitVec (edgeCount 12)) :=
  missing7728_7729 ++ missing7729_7730
abbrev records7728_7730 : List Blob :=
  records7728_7729 ++ records7729_7730
theorem aligned7728_7730 :
    AlignedValid 12 3 missing7728_7730 records7728_7730 :=
  aligned7728_7729.append aligned7729_7730

def missing7730_7731 : List (BitVec (edgeCount 12)) :=
  [missing7730]
abbrev records7730_7731 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7730]
theorem aligned7730_7731 :
    AlignedValid 12 3 missing7730_7731 records7730_7731 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7730
    maskCheck7730 AlignedValid.nil

def missing7731_7732 : List (BitVec (edgeCount 12)) :=
  [missing7731]
abbrev records7731_7732 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7731]
theorem aligned7731_7732 :
    AlignedValid 12 3 missing7731_7732 records7731_7732 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7731
    maskCheck7731 AlignedValid.nil

def missing7730_7732 : List (BitVec (edgeCount 12)) :=
  missing7730_7731 ++ missing7731_7732
abbrev records7730_7732 : List Blob :=
  records7730_7731 ++ records7731_7732
theorem aligned7730_7732 :
    AlignedValid 12 3 missing7730_7732 records7730_7732 :=
  aligned7730_7731.append aligned7731_7732

def missing7728_7732 : List (BitVec (edgeCount 12)) :=
  missing7728_7730 ++ missing7730_7732
abbrev records7728_7732 : List Blob :=
  records7728_7730 ++ records7730_7732
theorem aligned7728_7732 :
    AlignedValid 12 3 missing7728_7732 records7728_7732 :=
  aligned7728_7730.append aligned7730_7732

def missing7732_7733 : List (BitVec (edgeCount 12)) :=
  [missing7732]
abbrev records7732_7733 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7732]
theorem aligned7732_7733 :
    AlignedValid 12 3 missing7732_7733 records7732_7733 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7732
    maskCheck7732 AlignedValid.nil

def missing7733_7734 : List (BitVec (edgeCount 12)) :=
  [missing7733]
abbrev records7733_7734 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7733]
theorem aligned7733_7734 :
    AlignedValid 12 3 missing7733_7734 records7733_7734 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7733
    maskCheck7733 AlignedValid.nil

def missing7732_7734 : List (BitVec (edgeCount 12)) :=
  missing7732_7733 ++ missing7733_7734
abbrev records7732_7734 : List Blob :=
  records7732_7733 ++ records7733_7734
theorem aligned7732_7734 :
    AlignedValid 12 3 missing7732_7734 records7732_7734 :=
  aligned7732_7733.append aligned7733_7734

def missing7734_7735 : List (BitVec (edgeCount 12)) :=
  [missing7734]
abbrev records7734_7735 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7734]
theorem aligned7734_7735 :
    AlignedValid 12 3 missing7734_7735 records7734_7735 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7734
    maskCheck7734 AlignedValid.nil

def missing7735_7736 : List (BitVec (edgeCount 12)) :=
  [missing7735]
abbrev records7735_7736 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7735]
theorem aligned7735_7736 :
    AlignedValid 12 3 missing7735_7736 records7735_7736 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7735
    maskCheck7735 AlignedValid.nil

def missing7734_7736 : List (BitVec (edgeCount 12)) :=
  missing7734_7735 ++ missing7735_7736
abbrev records7734_7736 : List Blob :=
  records7734_7735 ++ records7735_7736
theorem aligned7734_7736 :
    AlignedValid 12 3 missing7734_7736 records7734_7736 :=
  aligned7734_7735.append aligned7735_7736

def missing7732_7736 : List (BitVec (edgeCount 12)) :=
  missing7732_7734 ++ missing7734_7736
abbrev records7732_7736 : List Blob :=
  records7732_7734 ++ records7734_7736
theorem aligned7732_7736 :
    AlignedValid 12 3 missing7732_7736 records7732_7736 :=
  aligned7732_7734.append aligned7734_7736

def missing7728_7736 : List (BitVec (edgeCount 12)) :=
  missing7728_7732 ++ missing7732_7736
abbrev records7728_7736 : List Blob :=
  records7728_7732 ++ records7732_7736
theorem aligned7728_7736 :
    AlignedValid 12 3 missing7728_7736 records7728_7736 :=
  aligned7728_7732.append aligned7732_7736

def missing7736_7737 : List (BitVec (edgeCount 12)) :=
  [missing7736]
abbrev records7736_7737 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7736]
theorem aligned7736_7737 :
    AlignedValid 12 3 missing7736_7737 records7736_7737 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7736
    maskCheck7736 AlignedValid.nil

def missing7737_7738 : List (BitVec (edgeCount 12)) :=
  [missing7737]
abbrev records7737_7738 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7737]
theorem aligned7737_7738 :
    AlignedValid 12 3 missing7737_7738 records7737_7738 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7737
    maskCheck7737 AlignedValid.nil

def missing7736_7738 : List (BitVec (edgeCount 12)) :=
  missing7736_7737 ++ missing7737_7738
abbrev records7736_7738 : List Blob :=
  records7736_7737 ++ records7737_7738
theorem aligned7736_7738 :
    AlignedValid 12 3 missing7736_7738 records7736_7738 :=
  aligned7736_7737.append aligned7737_7738

def missing7738_7739 : List (BitVec (edgeCount 12)) :=
  [missing7738]
abbrev records7738_7739 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7738]
theorem aligned7738_7739 :
    AlignedValid 12 3 missing7738_7739 records7738_7739 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7738
    maskCheck7738 AlignedValid.nil

def missing7739_7740 : List (BitVec (edgeCount 12)) :=
  [missing7739]
abbrev records7739_7740 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7739]
theorem aligned7739_7740 :
    AlignedValid 12 3 missing7739_7740 records7739_7740 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7739
    maskCheck7739 AlignedValid.nil

def missing7738_7740 : List (BitVec (edgeCount 12)) :=
  missing7738_7739 ++ missing7739_7740
abbrev records7738_7740 : List Blob :=
  records7738_7739 ++ records7739_7740
theorem aligned7738_7740 :
    AlignedValid 12 3 missing7738_7740 records7738_7740 :=
  aligned7738_7739.append aligned7739_7740

def missing7736_7740 : List (BitVec (edgeCount 12)) :=
  missing7736_7738 ++ missing7738_7740
abbrev records7736_7740 : List Blob :=
  records7736_7738 ++ records7738_7740
theorem aligned7736_7740 :
    AlignedValid 12 3 missing7736_7740 records7736_7740 :=
  aligned7736_7738.append aligned7738_7740

def missing7740_7741 : List (BitVec (edgeCount 12)) :=
  [missing7740]
abbrev records7740_7741 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7740]
theorem aligned7740_7741 :
    AlignedValid 12 3 missing7740_7741 records7740_7741 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7740
    maskCheck7740 AlignedValid.nil

def missing7741_7742 : List (BitVec (edgeCount 12)) :=
  [missing7741]
abbrev records7741_7742 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7741]
theorem aligned7741_7742 :
    AlignedValid 12 3 missing7741_7742 records7741_7742 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7741
    maskCheck7741 AlignedValid.nil

def missing7740_7742 : List (BitVec (edgeCount 12)) :=
  missing7740_7741 ++ missing7741_7742
abbrev records7740_7742 : List Blob :=
  records7740_7741 ++ records7741_7742
theorem aligned7740_7742 :
    AlignedValid 12 3 missing7740_7742 records7740_7742 :=
  aligned7740_7741.append aligned7741_7742

def missing7742_7743 : List (BitVec (edgeCount 12)) :=
  [missing7742]
abbrev records7742_7743 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7742]
theorem aligned7742_7743 :
    AlignedValid 12 3 missing7742_7743 records7742_7743 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7742
    maskCheck7742 AlignedValid.nil

def missing7743_7744 : List (BitVec (edgeCount 12)) :=
  [missing7743]
abbrev records7743_7744 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7743]
theorem aligned7743_7744 :
    AlignedValid 12 3 missing7743_7744 records7743_7744 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7743
    maskCheck7743 AlignedValid.nil

def missing7742_7744 : List (BitVec (edgeCount 12)) :=
  missing7742_7743 ++ missing7743_7744
abbrev records7742_7744 : List Blob :=
  records7742_7743 ++ records7743_7744
theorem aligned7742_7744 :
    AlignedValid 12 3 missing7742_7744 records7742_7744 :=
  aligned7742_7743.append aligned7743_7744

def missing7740_7744 : List (BitVec (edgeCount 12)) :=
  missing7740_7742 ++ missing7742_7744
abbrev records7740_7744 : List Blob :=
  records7740_7742 ++ records7742_7744
theorem aligned7740_7744 :
    AlignedValid 12 3 missing7740_7744 records7740_7744 :=
  aligned7740_7742.append aligned7742_7744

def missing7736_7744 : List (BitVec (edgeCount 12)) :=
  missing7736_7740 ++ missing7740_7744
abbrev records7736_7744 : List Blob :=
  records7736_7740 ++ records7740_7744
theorem aligned7736_7744 :
    AlignedValid 12 3 missing7736_7744 records7736_7744 :=
  aligned7736_7740.append aligned7740_7744

def missing7728_7744 : List (BitVec (edgeCount 12)) :=
  missing7728_7736 ++ missing7736_7744
abbrev records7728_7744 : List Blob :=
  records7728_7736 ++ records7736_7744
theorem aligned7728_7744 :
    AlignedValid 12 3 missing7728_7744 records7728_7744 :=
  aligned7728_7736.append aligned7736_7744

def missing7712_7744 : List (BitVec (edgeCount 12)) :=
  missing7712_7728 ++ missing7728_7744
abbrev records7712_7744 : List Blob :=
  records7712_7728 ++ records7728_7744
theorem aligned7712_7744 :
    AlignedValid 12 3 missing7712_7744 records7712_7744 :=
  aligned7712_7728.append aligned7728_7744

def missing7680_7744 : List (BitVec (edgeCount 12)) :=
  missing7680_7712 ++ missing7712_7744
abbrev records7680_7744 : List Blob :=
  records7680_7712 ++ records7712_7744
theorem aligned7680_7744 :
    AlignedValid 12 3 missing7680_7744 records7680_7744 :=
  aligned7680_7712.append aligned7712_7744

def missing7744_7745 : List (BitVec (edgeCount 12)) :=
  [missing7744]
abbrev records7744_7745 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7744]
theorem aligned7744_7745 :
    AlignedValid 12 3 missing7744_7745 records7744_7745 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7744
    maskCheck7744 AlignedValid.nil

def missing7745_7746 : List (BitVec (edgeCount 12)) :=
  [missing7745]
abbrev records7745_7746 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7745]
theorem aligned7745_7746 :
    AlignedValid 12 3 missing7745_7746 records7745_7746 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7745
    maskCheck7745 AlignedValid.nil

def missing7744_7746 : List (BitVec (edgeCount 12)) :=
  missing7744_7745 ++ missing7745_7746
abbrev records7744_7746 : List Blob :=
  records7744_7745 ++ records7745_7746
theorem aligned7744_7746 :
    AlignedValid 12 3 missing7744_7746 records7744_7746 :=
  aligned7744_7745.append aligned7745_7746

def missing7746_7747 : List (BitVec (edgeCount 12)) :=
  [missing7746]
abbrev records7746_7747 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7746]
theorem aligned7746_7747 :
    AlignedValid 12 3 missing7746_7747 records7746_7747 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7746
    maskCheck7746 AlignedValid.nil

def missing7747_7748 : List (BitVec (edgeCount 12)) :=
  [missing7747]
abbrev records7747_7748 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7747]
theorem aligned7747_7748 :
    AlignedValid 12 3 missing7747_7748 records7747_7748 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7747
    maskCheck7747 AlignedValid.nil

def missing7746_7748 : List (BitVec (edgeCount 12)) :=
  missing7746_7747 ++ missing7747_7748
abbrev records7746_7748 : List Blob :=
  records7746_7747 ++ records7747_7748
theorem aligned7746_7748 :
    AlignedValid 12 3 missing7746_7748 records7746_7748 :=
  aligned7746_7747.append aligned7747_7748

def missing7744_7748 : List (BitVec (edgeCount 12)) :=
  missing7744_7746 ++ missing7746_7748
abbrev records7744_7748 : List Blob :=
  records7744_7746 ++ records7746_7748
theorem aligned7744_7748 :
    AlignedValid 12 3 missing7744_7748 records7744_7748 :=
  aligned7744_7746.append aligned7746_7748

def missing7748_7749 : List (BitVec (edgeCount 12)) :=
  [missing7748]
abbrev records7748_7749 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7748]
theorem aligned7748_7749 :
    AlignedValid 12 3 missing7748_7749 records7748_7749 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7748
    maskCheck7748 AlignedValid.nil

def missing7749_7750 : List (BitVec (edgeCount 12)) :=
  [missing7749]
abbrev records7749_7750 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7749]
theorem aligned7749_7750 :
    AlignedValid 12 3 missing7749_7750 records7749_7750 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7749
    maskCheck7749 AlignedValid.nil

def missing7748_7750 : List (BitVec (edgeCount 12)) :=
  missing7748_7749 ++ missing7749_7750
abbrev records7748_7750 : List Blob :=
  records7748_7749 ++ records7749_7750
theorem aligned7748_7750 :
    AlignedValid 12 3 missing7748_7750 records7748_7750 :=
  aligned7748_7749.append aligned7749_7750

def missing7750_7751 : List (BitVec (edgeCount 12)) :=
  [missing7750]
abbrev records7750_7751 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7750]
theorem aligned7750_7751 :
    AlignedValid 12 3 missing7750_7751 records7750_7751 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7750
    maskCheck7750 AlignedValid.nil

def missing7751_7752 : List (BitVec (edgeCount 12)) :=
  [missing7751]
abbrev records7751_7752 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7751]
theorem aligned7751_7752 :
    AlignedValid 12 3 missing7751_7752 records7751_7752 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7751
    maskCheck7751 AlignedValid.nil

def missing7750_7752 : List (BitVec (edgeCount 12)) :=
  missing7750_7751 ++ missing7751_7752
abbrev records7750_7752 : List Blob :=
  records7750_7751 ++ records7751_7752
theorem aligned7750_7752 :
    AlignedValid 12 3 missing7750_7752 records7750_7752 :=
  aligned7750_7751.append aligned7751_7752

def missing7748_7752 : List (BitVec (edgeCount 12)) :=
  missing7748_7750 ++ missing7750_7752
abbrev records7748_7752 : List Blob :=
  records7748_7750 ++ records7750_7752
theorem aligned7748_7752 :
    AlignedValid 12 3 missing7748_7752 records7748_7752 :=
  aligned7748_7750.append aligned7750_7752

def missing7744_7752 : List (BitVec (edgeCount 12)) :=
  missing7744_7748 ++ missing7748_7752
abbrev records7744_7752 : List Blob :=
  records7744_7748 ++ records7748_7752
theorem aligned7744_7752 :
    AlignedValid 12 3 missing7744_7752 records7744_7752 :=
  aligned7744_7748.append aligned7748_7752

def missing7752_7753 : List (BitVec (edgeCount 12)) :=
  [missing7752]
abbrev records7752_7753 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7752]
theorem aligned7752_7753 :
    AlignedValid 12 3 missing7752_7753 records7752_7753 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7752
    maskCheck7752 AlignedValid.nil

def missing7753_7754 : List (BitVec (edgeCount 12)) :=
  [missing7753]
abbrev records7753_7754 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7753]
theorem aligned7753_7754 :
    AlignedValid 12 3 missing7753_7754 records7753_7754 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7753
    maskCheck7753 AlignedValid.nil

def missing7752_7754 : List (BitVec (edgeCount 12)) :=
  missing7752_7753 ++ missing7753_7754
abbrev records7752_7754 : List Blob :=
  records7752_7753 ++ records7753_7754
theorem aligned7752_7754 :
    AlignedValid 12 3 missing7752_7754 records7752_7754 :=
  aligned7752_7753.append aligned7753_7754

def missing7754_7755 : List (BitVec (edgeCount 12)) :=
  [missing7754]
abbrev records7754_7755 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7754]
theorem aligned7754_7755 :
    AlignedValid 12 3 missing7754_7755 records7754_7755 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7754
    maskCheck7754 AlignedValid.nil

def missing7755_7756 : List (BitVec (edgeCount 12)) :=
  [missing7755]
abbrev records7755_7756 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7755]
theorem aligned7755_7756 :
    AlignedValid 12 3 missing7755_7756 records7755_7756 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7755
    maskCheck7755 AlignedValid.nil

def missing7754_7756 : List (BitVec (edgeCount 12)) :=
  missing7754_7755 ++ missing7755_7756
abbrev records7754_7756 : List Blob :=
  records7754_7755 ++ records7755_7756
theorem aligned7754_7756 :
    AlignedValid 12 3 missing7754_7756 records7754_7756 :=
  aligned7754_7755.append aligned7755_7756

def missing7752_7756 : List (BitVec (edgeCount 12)) :=
  missing7752_7754 ++ missing7754_7756
abbrev records7752_7756 : List Blob :=
  records7752_7754 ++ records7754_7756
theorem aligned7752_7756 :
    AlignedValid 12 3 missing7752_7756 records7752_7756 :=
  aligned7752_7754.append aligned7754_7756

def missing7756_7757 : List (BitVec (edgeCount 12)) :=
  [missing7756]
abbrev records7756_7757 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7756]
theorem aligned7756_7757 :
    AlignedValid 12 3 missing7756_7757 records7756_7757 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7756
    maskCheck7756 AlignedValid.nil

def missing7757_7758 : List (BitVec (edgeCount 12)) :=
  [missing7757]
abbrev records7757_7758 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7757]
theorem aligned7757_7758 :
    AlignedValid 12 3 missing7757_7758 records7757_7758 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7757
    maskCheck7757 AlignedValid.nil

def missing7756_7758 : List (BitVec (edgeCount 12)) :=
  missing7756_7757 ++ missing7757_7758
abbrev records7756_7758 : List Blob :=
  records7756_7757 ++ records7757_7758
theorem aligned7756_7758 :
    AlignedValid 12 3 missing7756_7758 records7756_7758 :=
  aligned7756_7757.append aligned7757_7758

def missing7758_7759 : List (BitVec (edgeCount 12)) :=
  [missing7758]
abbrev records7758_7759 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7758]
theorem aligned7758_7759 :
    AlignedValid 12 3 missing7758_7759 records7758_7759 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7758
    maskCheck7758 AlignedValid.nil

def missing7759_7760 : List (BitVec (edgeCount 12)) :=
  [missing7759]
abbrev records7759_7760 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7759]
theorem aligned7759_7760 :
    AlignedValid 12 3 missing7759_7760 records7759_7760 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7759
    maskCheck7759 AlignedValid.nil

def missing7758_7760 : List (BitVec (edgeCount 12)) :=
  missing7758_7759 ++ missing7759_7760
abbrev records7758_7760 : List Blob :=
  records7758_7759 ++ records7759_7760
theorem aligned7758_7760 :
    AlignedValid 12 3 missing7758_7760 records7758_7760 :=
  aligned7758_7759.append aligned7759_7760

def missing7756_7760 : List (BitVec (edgeCount 12)) :=
  missing7756_7758 ++ missing7758_7760
abbrev records7756_7760 : List Blob :=
  records7756_7758 ++ records7758_7760
theorem aligned7756_7760 :
    AlignedValid 12 3 missing7756_7760 records7756_7760 :=
  aligned7756_7758.append aligned7758_7760

def missing7752_7760 : List (BitVec (edgeCount 12)) :=
  missing7752_7756 ++ missing7756_7760
abbrev records7752_7760 : List Blob :=
  records7752_7756 ++ records7756_7760
theorem aligned7752_7760 :
    AlignedValid 12 3 missing7752_7760 records7752_7760 :=
  aligned7752_7756.append aligned7756_7760

def missing7744_7760 : List (BitVec (edgeCount 12)) :=
  missing7744_7752 ++ missing7752_7760
abbrev records7744_7760 : List Blob :=
  records7744_7752 ++ records7752_7760
theorem aligned7744_7760 :
    AlignedValid 12 3 missing7744_7760 records7744_7760 :=
  aligned7744_7752.append aligned7752_7760

def missing7760_7761 : List (BitVec (edgeCount 12)) :=
  [missing7760]
abbrev records7760_7761 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7760]
theorem aligned7760_7761 :
    AlignedValid 12 3 missing7760_7761 records7760_7761 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7760
    maskCheck7760 AlignedValid.nil

def missing7761_7762 : List (BitVec (edgeCount 12)) :=
  [missing7761]
abbrev records7761_7762 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7761]
theorem aligned7761_7762 :
    AlignedValid 12 3 missing7761_7762 records7761_7762 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7761
    maskCheck7761 AlignedValid.nil

def missing7760_7762 : List (BitVec (edgeCount 12)) :=
  missing7760_7761 ++ missing7761_7762
abbrev records7760_7762 : List Blob :=
  records7760_7761 ++ records7761_7762
theorem aligned7760_7762 :
    AlignedValid 12 3 missing7760_7762 records7760_7762 :=
  aligned7760_7761.append aligned7761_7762

def missing7762_7763 : List (BitVec (edgeCount 12)) :=
  [missing7762]
abbrev records7762_7763 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7762]
theorem aligned7762_7763 :
    AlignedValid 12 3 missing7762_7763 records7762_7763 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7762
    maskCheck7762 AlignedValid.nil

def missing7763_7764 : List (BitVec (edgeCount 12)) :=
  [missing7763]
abbrev records7763_7764 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7763]
theorem aligned7763_7764 :
    AlignedValid 12 3 missing7763_7764 records7763_7764 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7763
    maskCheck7763 AlignedValid.nil

def missing7762_7764 : List (BitVec (edgeCount 12)) :=
  missing7762_7763 ++ missing7763_7764
abbrev records7762_7764 : List Blob :=
  records7762_7763 ++ records7763_7764
theorem aligned7762_7764 :
    AlignedValid 12 3 missing7762_7764 records7762_7764 :=
  aligned7762_7763.append aligned7763_7764

def missing7760_7764 : List (BitVec (edgeCount 12)) :=
  missing7760_7762 ++ missing7762_7764
abbrev records7760_7764 : List Blob :=
  records7760_7762 ++ records7762_7764
theorem aligned7760_7764 :
    AlignedValid 12 3 missing7760_7764 records7760_7764 :=
  aligned7760_7762.append aligned7762_7764

def missing7764_7765 : List (BitVec (edgeCount 12)) :=
  [missing7764]
abbrev records7764_7765 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7764]
theorem aligned7764_7765 :
    AlignedValid 12 3 missing7764_7765 records7764_7765 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7764
    maskCheck7764 AlignedValid.nil

def missing7765_7766 : List (BitVec (edgeCount 12)) :=
  [missing7765]
abbrev records7765_7766 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7765]
theorem aligned7765_7766 :
    AlignedValid 12 3 missing7765_7766 records7765_7766 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7765
    maskCheck7765 AlignedValid.nil

def missing7764_7766 : List (BitVec (edgeCount 12)) :=
  missing7764_7765 ++ missing7765_7766
abbrev records7764_7766 : List Blob :=
  records7764_7765 ++ records7765_7766
theorem aligned7764_7766 :
    AlignedValid 12 3 missing7764_7766 records7764_7766 :=
  aligned7764_7765.append aligned7765_7766

def missing7766_7767 : List (BitVec (edgeCount 12)) :=
  [missing7766]
abbrev records7766_7767 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7766]
theorem aligned7766_7767 :
    AlignedValid 12 3 missing7766_7767 records7766_7767 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7766
    maskCheck7766 AlignedValid.nil

def missing7767_7768 : List (BitVec (edgeCount 12)) :=
  [missing7767]
abbrev records7767_7768 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7767]
theorem aligned7767_7768 :
    AlignedValid 12 3 missing7767_7768 records7767_7768 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7767
    maskCheck7767 AlignedValid.nil

def missing7766_7768 : List (BitVec (edgeCount 12)) :=
  missing7766_7767 ++ missing7767_7768
abbrev records7766_7768 : List Blob :=
  records7766_7767 ++ records7767_7768
theorem aligned7766_7768 :
    AlignedValid 12 3 missing7766_7768 records7766_7768 :=
  aligned7766_7767.append aligned7767_7768

def missing7764_7768 : List (BitVec (edgeCount 12)) :=
  missing7764_7766 ++ missing7766_7768
abbrev records7764_7768 : List Blob :=
  records7764_7766 ++ records7766_7768
theorem aligned7764_7768 :
    AlignedValid 12 3 missing7764_7768 records7764_7768 :=
  aligned7764_7766.append aligned7766_7768

def missing7760_7768 : List (BitVec (edgeCount 12)) :=
  missing7760_7764 ++ missing7764_7768
abbrev records7760_7768 : List Blob :=
  records7760_7764 ++ records7764_7768
theorem aligned7760_7768 :
    AlignedValid 12 3 missing7760_7768 records7760_7768 :=
  aligned7760_7764.append aligned7764_7768

def missing7768_7769 : List (BitVec (edgeCount 12)) :=
  [missing7768]
abbrev records7768_7769 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7768]
theorem aligned7768_7769 :
    AlignedValid 12 3 missing7768_7769 records7768_7769 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7768
    maskCheck7768 AlignedValid.nil

def missing7769_7770 : List (BitVec (edgeCount 12)) :=
  [missing7769]
abbrev records7769_7770 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7769]
theorem aligned7769_7770 :
    AlignedValid 12 3 missing7769_7770 records7769_7770 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7769
    maskCheck7769 AlignedValid.nil

def missing7768_7770 : List (BitVec (edgeCount 12)) :=
  missing7768_7769 ++ missing7769_7770
abbrev records7768_7770 : List Blob :=
  records7768_7769 ++ records7769_7770
theorem aligned7768_7770 :
    AlignedValid 12 3 missing7768_7770 records7768_7770 :=
  aligned7768_7769.append aligned7769_7770

def missing7770_7771 : List (BitVec (edgeCount 12)) :=
  [missing7770]
abbrev records7770_7771 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7770]
theorem aligned7770_7771 :
    AlignedValid 12 3 missing7770_7771 records7770_7771 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7770
    maskCheck7770 AlignedValid.nil

def missing7771_7772 : List (BitVec (edgeCount 12)) :=
  [missing7771]
abbrev records7771_7772 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7771]
theorem aligned7771_7772 :
    AlignedValid 12 3 missing7771_7772 records7771_7772 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7771
    maskCheck7771 AlignedValid.nil

def missing7770_7772 : List (BitVec (edgeCount 12)) :=
  missing7770_7771 ++ missing7771_7772
abbrev records7770_7772 : List Blob :=
  records7770_7771 ++ records7771_7772
theorem aligned7770_7772 :
    AlignedValid 12 3 missing7770_7772 records7770_7772 :=
  aligned7770_7771.append aligned7771_7772

def missing7768_7772 : List (BitVec (edgeCount 12)) :=
  missing7768_7770 ++ missing7770_7772
abbrev records7768_7772 : List Blob :=
  records7768_7770 ++ records7770_7772
theorem aligned7768_7772 :
    AlignedValid 12 3 missing7768_7772 records7768_7772 :=
  aligned7768_7770.append aligned7770_7772

def missing7772_7773 : List (BitVec (edgeCount 12)) :=
  [missing7772]
abbrev records7772_7773 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7772]
theorem aligned7772_7773 :
    AlignedValid 12 3 missing7772_7773 records7772_7773 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7772
    maskCheck7772 AlignedValid.nil

def missing7773_7774 : List (BitVec (edgeCount 12)) :=
  [missing7773]
abbrev records7773_7774 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7773]
theorem aligned7773_7774 :
    AlignedValid 12 3 missing7773_7774 records7773_7774 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7773
    maskCheck7773 AlignedValid.nil

def missing7772_7774 : List (BitVec (edgeCount 12)) :=
  missing7772_7773 ++ missing7773_7774
abbrev records7772_7774 : List Blob :=
  records7772_7773 ++ records7773_7774
theorem aligned7772_7774 :
    AlignedValid 12 3 missing7772_7774 records7772_7774 :=
  aligned7772_7773.append aligned7773_7774

def missing7774_7775 : List (BitVec (edgeCount 12)) :=
  [missing7774]
abbrev records7774_7775 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7774]
theorem aligned7774_7775 :
    AlignedValid 12 3 missing7774_7775 records7774_7775 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7774
    maskCheck7774 AlignedValid.nil

def missing7775_7776 : List (BitVec (edgeCount 12)) :=
  [missing7775]
abbrev records7775_7776 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7775]
theorem aligned7775_7776 :
    AlignedValid 12 3 missing7775_7776 records7775_7776 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7775
    maskCheck7775 AlignedValid.nil

def missing7774_7776 : List (BitVec (edgeCount 12)) :=
  missing7774_7775 ++ missing7775_7776
abbrev records7774_7776 : List Blob :=
  records7774_7775 ++ records7775_7776
theorem aligned7774_7776 :
    AlignedValid 12 3 missing7774_7776 records7774_7776 :=
  aligned7774_7775.append aligned7775_7776

def missing7772_7776 : List (BitVec (edgeCount 12)) :=
  missing7772_7774 ++ missing7774_7776
abbrev records7772_7776 : List Blob :=
  records7772_7774 ++ records7774_7776
theorem aligned7772_7776 :
    AlignedValid 12 3 missing7772_7776 records7772_7776 :=
  aligned7772_7774.append aligned7774_7776

def missing7768_7776 : List (BitVec (edgeCount 12)) :=
  missing7768_7772 ++ missing7772_7776
abbrev records7768_7776 : List Blob :=
  records7768_7772 ++ records7772_7776
theorem aligned7768_7776 :
    AlignedValid 12 3 missing7768_7776 records7768_7776 :=
  aligned7768_7772.append aligned7772_7776

def missing7760_7776 : List (BitVec (edgeCount 12)) :=
  missing7760_7768 ++ missing7768_7776
abbrev records7760_7776 : List Blob :=
  records7760_7768 ++ records7768_7776
theorem aligned7760_7776 :
    AlignedValid 12 3 missing7760_7776 records7760_7776 :=
  aligned7760_7768.append aligned7768_7776

def missing7744_7776 : List (BitVec (edgeCount 12)) :=
  missing7744_7760 ++ missing7760_7776
abbrev records7744_7776 : List Blob :=
  records7744_7760 ++ records7760_7776
theorem aligned7744_7776 :
    AlignedValid 12 3 missing7744_7776 records7744_7776 :=
  aligned7744_7760.append aligned7760_7776

def missing7776_7777 : List (BitVec (edgeCount 12)) :=
  [missing7776]
abbrev records7776_7777 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7776]
theorem aligned7776_7777 :
    AlignedValid 12 3 missing7776_7777 records7776_7777 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7776
    maskCheck7776 AlignedValid.nil

def missing7777_7778 : List (BitVec (edgeCount 12)) :=
  [missing7777]
abbrev records7777_7778 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7777]
theorem aligned7777_7778 :
    AlignedValid 12 3 missing7777_7778 records7777_7778 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7777
    maskCheck7777 AlignedValid.nil

def missing7776_7778 : List (BitVec (edgeCount 12)) :=
  missing7776_7777 ++ missing7777_7778
abbrev records7776_7778 : List Blob :=
  records7776_7777 ++ records7777_7778
theorem aligned7776_7778 :
    AlignedValid 12 3 missing7776_7778 records7776_7778 :=
  aligned7776_7777.append aligned7777_7778

def missing7778_7779 : List (BitVec (edgeCount 12)) :=
  [missing7778]
abbrev records7778_7779 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7778]
theorem aligned7778_7779 :
    AlignedValid 12 3 missing7778_7779 records7778_7779 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7778
    maskCheck7778 AlignedValid.nil

def missing7779_7780 : List (BitVec (edgeCount 12)) :=
  [missing7779]
abbrev records7779_7780 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7779]
theorem aligned7779_7780 :
    AlignedValid 12 3 missing7779_7780 records7779_7780 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7779
    maskCheck7779 AlignedValid.nil

def missing7778_7780 : List (BitVec (edgeCount 12)) :=
  missing7778_7779 ++ missing7779_7780
abbrev records7778_7780 : List Blob :=
  records7778_7779 ++ records7779_7780
theorem aligned7778_7780 :
    AlignedValid 12 3 missing7778_7780 records7778_7780 :=
  aligned7778_7779.append aligned7779_7780

def missing7776_7780 : List (BitVec (edgeCount 12)) :=
  missing7776_7778 ++ missing7778_7780
abbrev records7776_7780 : List Blob :=
  records7776_7778 ++ records7778_7780
theorem aligned7776_7780 :
    AlignedValid 12 3 missing7776_7780 records7776_7780 :=
  aligned7776_7778.append aligned7778_7780

def missing7780_7781 : List (BitVec (edgeCount 12)) :=
  [missing7780]
abbrev records7780_7781 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7780]
theorem aligned7780_7781 :
    AlignedValid 12 3 missing7780_7781 records7780_7781 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7780
    maskCheck7780 AlignedValid.nil

def missing7781_7782 : List (BitVec (edgeCount 12)) :=
  [missing7781]
abbrev records7781_7782 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7781]
theorem aligned7781_7782 :
    AlignedValid 12 3 missing7781_7782 records7781_7782 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7781
    maskCheck7781 AlignedValid.nil

def missing7780_7782 : List (BitVec (edgeCount 12)) :=
  missing7780_7781 ++ missing7781_7782
abbrev records7780_7782 : List Blob :=
  records7780_7781 ++ records7781_7782
theorem aligned7780_7782 :
    AlignedValid 12 3 missing7780_7782 records7780_7782 :=
  aligned7780_7781.append aligned7781_7782

def missing7782_7783 : List (BitVec (edgeCount 12)) :=
  [missing7782]
abbrev records7782_7783 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7782]
theorem aligned7782_7783 :
    AlignedValid 12 3 missing7782_7783 records7782_7783 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7782
    maskCheck7782 AlignedValid.nil

def missing7783_7784 : List (BitVec (edgeCount 12)) :=
  [missing7783]
abbrev records7783_7784 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7783]
theorem aligned7783_7784 :
    AlignedValid 12 3 missing7783_7784 records7783_7784 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7783
    maskCheck7783 AlignedValid.nil

def missing7782_7784 : List (BitVec (edgeCount 12)) :=
  missing7782_7783 ++ missing7783_7784
abbrev records7782_7784 : List Blob :=
  records7782_7783 ++ records7783_7784
theorem aligned7782_7784 :
    AlignedValid 12 3 missing7782_7784 records7782_7784 :=
  aligned7782_7783.append aligned7783_7784

def missing7780_7784 : List (BitVec (edgeCount 12)) :=
  missing7780_7782 ++ missing7782_7784
abbrev records7780_7784 : List Blob :=
  records7780_7782 ++ records7782_7784
theorem aligned7780_7784 :
    AlignedValid 12 3 missing7780_7784 records7780_7784 :=
  aligned7780_7782.append aligned7782_7784

def missing7776_7784 : List (BitVec (edgeCount 12)) :=
  missing7776_7780 ++ missing7780_7784
abbrev records7776_7784 : List Blob :=
  records7776_7780 ++ records7780_7784
theorem aligned7776_7784 :
    AlignedValid 12 3 missing7776_7784 records7776_7784 :=
  aligned7776_7780.append aligned7780_7784

def missing7784_7785 : List (BitVec (edgeCount 12)) :=
  [missing7784]
abbrev records7784_7785 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7784]
theorem aligned7784_7785 :
    AlignedValid 12 3 missing7784_7785 records7784_7785 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7784
    maskCheck7784 AlignedValid.nil

def missing7785_7786 : List (BitVec (edgeCount 12)) :=
  [missing7785]
abbrev records7785_7786 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7785]
theorem aligned7785_7786 :
    AlignedValid 12 3 missing7785_7786 records7785_7786 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7785
    maskCheck7785 AlignedValid.nil

def missing7784_7786 : List (BitVec (edgeCount 12)) :=
  missing7784_7785 ++ missing7785_7786
abbrev records7784_7786 : List Blob :=
  records7784_7785 ++ records7785_7786
theorem aligned7784_7786 :
    AlignedValid 12 3 missing7784_7786 records7784_7786 :=
  aligned7784_7785.append aligned7785_7786

def missing7786_7787 : List (BitVec (edgeCount 12)) :=
  [missing7786]
abbrev records7786_7787 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7786]
theorem aligned7786_7787 :
    AlignedValid 12 3 missing7786_7787 records7786_7787 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7786
    maskCheck7786 AlignedValid.nil

def missing7787_7788 : List (BitVec (edgeCount 12)) :=
  [missing7787]
abbrev records7787_7788 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7787]
theorem aligned7787_7788 :
    AlignedValid 12 3 missing7787_7788 records7787_7788 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7787
    maskCheck7787 AlignedValid.nil

def missing7786_7788 : List (BitVec (edgeCount 12)) :=
  missing7786_7787 ++ missing7787_7788
abbrev records7786_7788 : List Blob :=
  records7786_7787 ++ records7787_7788
theorem aligned7786_7788 :
    AlignedValid 12 3 missing7786_7788 records7786_7788 :=
  aligned7786_7787.append aligned7787_7788

def missing7784_7788 : List (BitVec (edgeCount 12)) :=
  missing7784_7786 ++ missing7786_7788
abbrev records7784_7788 : List Blob :=
  records7784_7786 ++ records7786_7788
theorem aligned7784_7788 :
    AlignedValid 12 3 missing7784_7788 records7784_7788 :=
  aligned7784_7786.append aligned7786_7788

def missing7788_7789 : List (BitVec (edgeCount 12)) :=
  [missing7788]
abbrev records7788_7789 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7788]
theorem aligned7788_7789 :
    AlignedValid 12 3 missing7788_7789 records7788_7789 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7788
    maskCheck7788 AlignedValid.nil

def missing7789_7790 : List (BitVec (edgeCount 12)) :=
  [missing7789]
abbrev records7789_7790 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7789]
theorem aligned7789_7790 :
    AlignedValid 12 3 missing7789_7790 records7789_7790 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7789
    maskCheck7789 AlignedValid.nil

def missing7788_7790 : List (BitVec (edgeCount 12)) :=
  missing7788_7789 ++ missing7789_7790
abbrev records7788_7790 : List Blob :=
  records7788_7789 ++ records7789_7790
theorem aligned7788_7790 :
    AlignedValid 12 3 missing7788_7790 records7788_7790 :=
  aligned7788_7789.append aligned7789_7790

def missing7790_7791 : List (BitVec (edgeCount 12)) :=
  [missing7790]
abbrev records7790_7791 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7790]
theorem aligned7790_7791 :
    AlignedValid 12 3 missing7790_7791 records7790_7791 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7790
    maskCheck7790 AlignedValid.nil

def missing7791_7792 : List (BitVec (edgeCount 12)) :=
  [missing7791]
abbrev records7791_7792 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7791]
theorem aligned7791_7792 :
    AlignedValid 12 3 missing7791_7792 records7791_7792 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7791
    maskCheck7791 AlignedValid.nil

def missing7790_7792 : List (BitVec (edgeCount 12)) :=
  missing7790_7791 ++ missing7791_7792
abbrev records7790_7792 : List Blob :=
  records7790_7791 ++ records7791_7792
theorem aligned7790_7792 :
    AlignedValid 12 3 missing7790_7792 records7790_7792 :=
  aligned7790_7791.append aligned7791_7792

def missing7788_7792 : List (BitVec (edgeCount 12)) :=
  missing7788_7790 ++ missing7790_7792
abbrev records7788_7792 : List Blob :=
  records7788_7790 ++ records7790_7792
theorem aligned7788_7792 :
    AlignedValid 12 3 missing7788_7792 records7788_7792 :=
  aligned7788_7790.append aligned7790_7792

def missing7784_7792 : List (BitVec (edgeCount 12)) :=
  missing7784_7788 ++ missing7788_7792
abbrev records7784_7792 : List Blob :=
  records7784_7788 ++ records7788_7792
theorem aligned7784_7792 :
    AlignedValid 12 3 missing7784_7792 records7784_7792 :=
  aligned7784_7788.append aligned7788_7792

def missing7776_7792 : List (BitVec (edgeCount 12)) :=
  missing7776_7784 ++ missing7784_7792
abbrev records7776_7792 : List Blob :=
  records7776_7784 ++ records7784_7792
theorem aligned7776_7792 :
    AlignedValid 12 3 missing7776_7792 records7776_7792 :=
  aligned7776_7784.append aligned7784_7792

def missing7792_7793 : List (BitVec (edgeCount 12)) :=
  [missing7792]
abbrev records7792_7793 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7792]
theorem aligned7792_7793 :
    AlignedValid 12 3 missing7792_7793 records7792_7793 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7792
    maskCheck7792 AlignedValid.nil

def missing7793_7794 : List (BitVec (edgeCount 12)) :=
  [missing7793]
abbrev records7793_7794 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7793]
theorem aligned7793_7794 :
    AlignedValid 12 3 missing7793_7794 records7793_7794 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7793
    maskCheck7793 AlignedValid.nil

def missing7792_7794 : List (BitVec (edgeCount 12)) :=
  missing7792_7793 ++ missing7793_7794
abbrev records7792_7794 : List Blob :=
  records7792_7793 ++ records7793_7794
theorem aligned7792_7794 :
    AlignedValid 12 3 missing7792_7794 records7792_7794 :=
  aligned7792_7793.append aligned7793_7794

def missing7794_7795 : List (BitVec (edgeCount 12)) :=
  [missing7794]
abbrev records7794_7795 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7794]
theorem aligned7794_7795 :
    AlignedValid 12 3 missing7794_7795 records7794_7795 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7794
    maskCheck7794 AlignedValid.nil

def missing7795_7796 : List (BitVec (edgeCount 12)) :=
  [missing7795]
abbrev records7795_7796 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7795]
theorem aligned7795_7796 :
    AlignedValid 12 3 missing7795_7796 records7795_7796 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7795
    maskCheck7795 AlignedValid.nil

def missing7794_7796 : List (BitVec (edgeCount 12)) :=
  missing7794_7795 ++ missing7795_7796
abbrev records7794_7796 : List Blob :=
  records7794_7795 ++ records7795_7796
theorem aligned7794_7796 :
    AlignedValid 12 3 missing7794_7796 records7794_7796 :=
  aligned7794_7795.append aligned7795_7796

def missing7792_7796 : List (BitVec (edgeCount 12)) :=
  missing7792_7794 ++ missing7794_7796
abbrev records7792_7796 : List Blob :=
  records7792_7794 ++ records7794_7796
theorem aligned7792_7796 :
    AlignedValid 12 3 missing7792_7796 records7792_7796 :=
  aligned7792_7794.append aligned7794_7796

def missing7796_7797 : List (BitVec (edgeCount 12)) :=
  [missing7796]
abbrev records7796_7797 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7796]
theorem aligned7796_7797 :
    AlignedValid 12 3 missing7796_7797 records7796_7797 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7796
    maskCheck7796 AlignedValid.nil

def missing7797_7798 : List (BitVec (edgeCount 12)) :=
  [missing7797]
abbrev records7797_7798 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7797]
theorem aligned7797_7798 :
    AlignedValid 12 3 missing7797_7798 records7797_7798 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7797
    maskCheck7797 AlignedValid.nil

def missing7796_7798 : List (BitVec (edgeCount 12)) :=
  missing7796_7797 ++ missing7797_7798
abbrev records7796_7798 : List Blob :=
  records7796_7797 ++ records7797_7798
theorem aligned7796_7798 :
    AlignedValid 12 3 missing7796_7798 records7796_7798 :=
  aligned7796_7797.append aligned7797_7798

def missing7798_7799 : List (BitVec (edgeCount 12)) :=
  [missing7798]
abbrev records7798_7799 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7798]
theorem aligned7798_7799 :
    AlignedValid 12 3 missing7798_7799 records7798_7799 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7798
    maskCheck7798 AlignedValid.nil

def missing7799_7800 : List (BitVec (edgeCount 12)) :=
  [missing7799]
abbrev records7799_7800 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7799]
theorem aligned7799_7800 :
    AlignedValid 12 3 missing7799_7800 records7799_7800 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7799
    maskCheck7799 AlignedValid.nil

def missing7798_7800 : List (BitVec (edgeCount 12)) :=
  missing7798_7799 ++ missing7799_7800
abbrev records7798_7800 : List Blob :=
  records7798_7799 ++ records7799_7800
theorem aligned7798_7800 :
    AlignedValid 12 3 missing7798_7800 records7798_7800 :=
  aligned7798_7799.append aligned7799_7800

def missing7796_7800 : List (BitVec (edgeCount 12)) :=
  missing7796_7798 ++ missing7798_7800
abbrev records7796_7800 : List Blob :=
  records7796_7798 ++ records7798_7800
theorem aligned7796_7800 :
    AlignedValid 12 3 missing7796_7800 records7796_7800 :=
  aligned7796_7798.append aligned7798_7800

def missing7792_7800 : List (BitVec (edgeCount 12)) :=
  missing7792_7796 ++ missing7796_7800
abbrev records7792_7800 : List Blob :=
  records7792_7796 ++ records7796_7800
theorem aligned7792_7800 :
    AlignedValid 12 3 missing7792_7800 records7792_7800 :=
  aligned7792_7796.append aligned7796_7800

def missing7800_7801 : List (BitVec (edgeCount 12)) :=
  [missing7800]
abbrev records7800_7801 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7800]
theorem aligned7800_7801 :
    AlignedValid 12 3 missing7800_7801 records7800_7801 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7800
    maskCheck7800 AlignedValid.nil

def missing7801_7802 : List (BitVec (edgeCount 12)) :=
  [missing7801]
abbrev records7801_7802 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7801]
theorem aligned7801_7802 :
    AlignedValid 12 3 missing7801_7802 records7801_7802 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7801
    maskCheck7801 AlignedValid.nil

def missing7800_7802 : List (BitVec (edgeCount 12)) :=
  missing7800_7801 ++ missing7801_7802
abbrev records7800_7802 : List Blob :=
  records7800_7801 ++ records7801_7802
theorem aligned7800_7802 :
    AlignedValid 12 3 missing7800_7802 records7800_7802 :=
  aligned7800_7801.append aligned7801_7802

def missing7802_7803 : List (BitVec (edgeCount 12)) :=
  [missing7802]
abbrev records7802_7803 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7802]
theorem aligned7802_7803 :
    AlignedValid 12 3 missing7802_7803 records7802_7803 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7802
    maskCheck7802 AlignedValid.nil

def missing7803_7804 : List (BitVec (edgeCount 12)) :=
  [missing7803]
abbrev records7803_7804 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7803]
theorem aligned7803_7804 :
    AlignedValid 12 3 missing7803_7804 records7803_7804 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7803
    maskCheck7803 AlignedValid.nil

def missing7802_7804 : List (BitVec (edgeCount 12)) :=
  missing7802_7803 ++ missing7803_7804
abbrev records7802_7804 : List Blob :=
  records7802_7803 ++ records7803_7804
theorem aligned7802_7804 :
    AlignedValid 12 3 missing7802_7804 records7802_7804 :=
  aligned7802_7803.append aligned7803_7804

def missing7800_7804 : List (BitVec (edgeCount 12)) :=
  missing7800_7802 ++ missing7802_7804
abbrev records7800_7804 : List Blob :=
  records7800_7802 ++ records7802_7804
theorem aligned7800_7804 :
    AlignedValid 12 3 missing7800_7804 records7800_7804 :=
  aligned7800_7802.append aligned7802_7804

def missing7804_7805 : List (BitVec (edgeCount 12)) :=
  [missing7804]
abbrev records7804_7805 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7804]
theorem aligned7804_7805 :
    AlignedValid 12 3 missing7804_7805 records7804_7805 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7804
    maskCheck7804 AlignedValid.nil

def missing7805_7806 : List (BitVec (edgeCount 12)) :=
  [missing7805]
abbrev records7805_7806 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7805]
theorem aligned7805_7806 :
    AlignedValid 12 3 missing7805_7806 records7805_7806 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7805
    maskCheck7805 AlignedValid.nil

def missing7804_7806 : List (BitVec (edgeCount 12)) :=
  missing7804_7805 ++ missing7805_7806
abbrev records7804_7806 : List Blob :=
  records7804_7805 ++ records7805_7806
theorem aligned7804_7806 :
    AlignedValid 12 3 missing7804_7806 records7804_7806 :=
  aligned7804_7805.append aligned7805_7806

def missing7806_7807 : List (BitVec (edgeCount 12)) :=
  [missing7806]
abbrev records7806_7807 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7806]
theorem aligned7806_7807 :
    AlignedValid 12 3 missing7806_7807 records7806_7807 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7806
    maskCheck7806 AlignedValid.nil

def missing7807_7808 : List (BitVec (edgeCount 12)) :=
  [missing7807]
abbrev records7807_7808 : List Blob :=
  [StrongPackedBucketN12A3Shard060.record7807]
theorem aligned7807_7808 :
    AlignedValid 12 3 missing7807_7808 records7807_7808 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard060.check7807
    maskCheck7807 AlignedValid.nil

def missing7806_7808 : List (BitVec (edgeCount 12)) :=
  missing7806_7807 ++ missing7807_7808
abbrev records7806_7808 : List Blob :=
  records7806_7807 ++ records7807_7808
theorem aligned7806_7808 :
    AlignedValid 12 3 missing7806_7808 records7806_7808 :=
  aligned7806_7807.append aligned7807_7808

def missing7804_7808 : List (BitVec (edgeCount 12)) :=
  missing7804_7806 ++ missing7806_7808
abbrev records7804_7808 : List Blob :=
  records7804_7806 ++ records7806_7808
theorem aligned7804_7808 :
    AlignedValid 12 3 missing7804_7808 records7804_7808 :=
  aligned7804_7806.append aligned7806_7808

def missing7800_7808 : List (BitVec (edgeCount 12)) :=
  missing7800_7804 ++ missing7804_7808
abbrev records7800_7808 : List Blob :=
  records7800_7804 ++ records7804_7808
theorem aligned7800_7808 :
    AlignedValid 12 3 missing7800_7808 records7800_7808 :=
  aligned7800_7804.append aligned7804_7808

def missing7792_7808 : List (BitVec (edgeCount 12)) :=
  missing7792_7800 ++ missing7800_7808
abbrev records7792_7808 : List Blob :=
  records7792_7800 ++ records7800_7808
theorem aligned7792_7808 :
    AlignedValid 12 3 missing7792_7808 records7792_7808 :=
  aligned7792_7800.append aligned7800_7808

def missing7776_7808 : List (BitVec (edgeCount 12)) :=
  missing7776_7792 ++ missing7792_7808
abbrev records7776_7808 : List Blob :=
  records7776_7792 ++ records7792_7808
theorem aligned7776_7808 :
    AlignedValid 12 3 missing7776_7808 records7776_7808 :=
  aligned7776_7792.append aligned7792_7808

def missing7744_7808 : List (BitVec (edgeCount 12)) :=
  missing7744_7776 ++ missing7776_7808
abbrev records7744_7808 : List Blob :=
  records7744_7776 ++ records7776_7808
theorem aligned7744_7808 :
    AlignedValid 12 3 missing7744_7808 records7744_7808 :=
  aligned7744_7776.append aligned7776_7808

def missing7680_7808 : List (BitVec (edgeCount 12)) :=
  missing7680_7744 ++ missing7744_7808
abbrev records7680_7808 : List Blob :=
  records7680_7744 ++ records7744_7808
theorem aligned7680_7808 :
    AlignedValid 12 3 missing7680_7808 records7680_7808 :=
  aligned7680_7744.append aligned7744_7808

abbrev missing : List (BitVec (edgeCount 12)) := missing7680_7808
abbrev records : List Blob := records7680_7808
theorem aligned : AlignedValid 12 3 missing records := aligned7680_7808

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A3AlignedShard060
