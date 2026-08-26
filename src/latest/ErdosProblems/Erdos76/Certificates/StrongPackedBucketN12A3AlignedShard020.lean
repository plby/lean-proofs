/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A3Shard020

/-! Decode-only alignment checks for n=12, a=3, records 2560--2687. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A3AlignedShard020

open PackedBucketCertificate

def missing2560 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4413633600524648448
theorem maskCheck2560 :
    checkMaskFor missing2560 StrongPackedBucketN12A3Shard020.record2560 = true := by
  decide

def missing2561 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4485691194562576384
theorem maskCheck2561 :
    checkMaskFor missing2561 StrongPackedBucketN12A3Shard020.record2561 = true := by
  decide

def missing2562 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8953262024914108416
theorem maskCheck2562 :
    checkMaskFor missing2562 StrongPackedBucketN12A3Shard020.record2562 = true := by
  decide

def missing2563 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9781924356350279680
theorem maskCheck2563 :
    checkMaskFor missing2563 StrongPackedBucketN12A3Shard020.record2563 = true := by
  decide

def missing2564 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10214269920577847296
theorem maskCheck2564 :
    checkMaskFor missing2564 StrongPackedBucketN12A3Shard020.record2564 = true := by
  decide

def missing2565 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10286327514615775232
theorem maskCheck2565 :
    checkMaskFor missing2565 StrongPackedBucketN12A3Shard020.record2565 = true := by
  decide

def missing2566 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10322356311634739200
theorem maskCheck2566 :
    checkMaskFor missing2566 StrongPackedBucketN12A3Shard020.record2566 = true := by
  decide

def missing2567 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11295133831146766336
theorem maskCheck2567 :
    checkMaskFor missing2567 StrongPackedBucketN12A3Shard020.record2567 = true := by
  decide

def missing2568 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11331162628165730304
theorem maskCheck2568 :
    checkMaskFor missing2568 StrongPackedBucketN12A3Shard020.record2568 = true := by
  decide

def missing2569 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11403220222203658240
theorem maskCheck2569 :
    checkMaskFor missing2569 StrongPackedBucketN12A3Shard020.record2569 = true := by
  decide

def missing2570 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13564948043341496320
theorem maskCheck2570 :
    checkMaskFor missing2570 StrongPackedBucketN12A3Shard020.record2570 = true := by
  decide

def missing2571 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19005296393205055488
theorem maskCheck2571 :
    checkMaskFor missing2571 StrongPackedBucketN12A3Shard020.record2571 = true := by
  decide

def missing2572 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19437641957432623104
theorem maskCheck2572 :
    checkMaskFor missing2572 StrongPackedBucketN12A3Shard020.record2572 = true := by
  decide

def missing2573 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19509699551470551040
theorem maskCheck2573 :
    checkMaskFor missing2573 StrongPackedBucketN12A3Shard020.record2573 = true := by
  decide

def missing2574 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19545728348489515008
theorem maskCheck2574 :
    checkMaskFor missing2574 StrongPackedBucketN12A3Shard020.record2574 = true := by
  decide

def missing2575 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20518505868001542144
theorem maskCheck2575 :
    checkMaskFor missing2575 StrongPackedBucketN12A3Shard020.record2575 = true := by
  decide

def missing2576 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20554534665020506112
theorem maskCheck2576 :
    checkMaskFor missing2576 StrongPackedBucketN12A3Shard020.record2576 = true := by
  decide

def missing2577 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20626592259058434048
theorem maskCheck2577 :
    checkMaskFor missing2577 StrongPackedBucketN12A3Shard020.record2577 = true := by
  decide

def missing2578 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22788320080196272128
theorem maskCheck2578 :
    checkMaskFor missing2578 StrongPackedBucketN12A3Shard020.record2578 = true := by
  decide

def missing2579 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27940438053908119552
theorem maskCheck2579 :
    checkMaskFor missing2579 StrongPackedBucketN12A3Shard020.record2579 = true := by
  decide

def missing2580 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28084553241983975424
theorem maskCheck2580 :
    checkMaskFor missing2580 StrongPackedBucketN12A3Shard020.record2580 = true := by
  decide

def missing2581 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28156610836021903360
theorem maskCheck2581 :
    checkMaskFor missing2581 StrongPackedBucketN12A3Shard020.record2581 = true := by
  decide

def missing2582 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28192639633040867328
theorem maskCheck2582 :
    checkMaskFor missing2582 StrongPackedBucketN12A3Shard020.record2582 = true := by
  decide

def missing2583 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28588956400249470976
theorem maskCheck2583 :
    checkMaskFor missing2583 StrongPackedBucketN12A3Shard020.record2583 = true := by
  decide

def missing2584 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28624985197268434944
theorem maskCheck2584 :
    checkMaskFor missing2584 StrongPackedBucketN12A3Shard020.record2584 = true := by
  decide

def missing2585 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28697042791306362880
theorem maskCheck2585 :
    checkMaskFor missing2585 StrongPackedBucketN12A3Shard020.record2585 = true := by
  decide

def missing2586 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29705849107837353984
theorem maskCheck2586 :
    checkMaskFor missing2586 StrongPackedBucketN12A3Shard020.record2586 = true := by
  decide

def missing2587 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37452040466914607104
theorem maskCheck2587 :
    checkMaskFor missing2587 StrongPackedBucketN12A3Shard020.record2587 = true := by
  decide

def missing2588 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37884386031142174720
theorem maskCheck2588 :
    checkMaskFor missing2588 StrongPackedBucketN12A3Shard020.record2588 = true := by
  decide

def missing2589 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37956443625180102656
theorem maskCheck2589 :
    checkMaskFor missing2589 StrongPackedBucketN12A3Shard020.record2589 = true := by
  decide

def missing2590 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37992472422199066624
theorem maskCheck2590 :
    checkMaskFor missing2590 StrongPackedBucketN12A3Shard020.record2590 = true := by
  decide

def missing2591 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38965249941711093760
theorem maskCheck2591 :
    checkMaskFor missing2591 StrongPackedBucketN12A3Shard020.record2591 = true := by
  decide

def missing2592 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39001278738730057728
theorem maskCheck2592 :
    checkMaskFor missing2592 StrongPackedBucketN12A3Shard020.record2592 = true := by
  decide

def missing2593 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39073336332767985664
theorem maskCheck2593 :
    checkMaskFor missing2593 StrongPackedBucketN12A3Shard020.record2593 = true := by
  decide

def missing2594 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41235064153905823744
theorem maskCheck2594 :
    checkMaskFor missing2594 StrongPackedBucketN12A3Shard020.record2594 = true := by
  decide

def missing2595 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46387182127617671168
theorem maskCheck2595 :
    checkMaskFor missing2595 StrongPackedBucketN12A3Shard020.record2595 = true := by
  decide

def missing2596 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46531297315693527040
theorem maskCheck2596 :
    checkMaskFor missing2596 StrongPackedBucketN12A3Shard020.record2596 = true := by
  decide

def missing2597 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46603354909731454976
theorem maskCheck2597 :
    checkMaskFor missing2597 StrongPackedBucketN12A3Shard020.record2597 = true := by
  decide

def missing2598 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46639383706750418944
theorem maskCheck2598 :
    checkMaskFor missing2598 StrongPackedBucketN12A3Shard020.record2598 = true := by
  decide

def missing2599 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47035700473959022592
theorem maskCheck2599 :
    checkMaskFor missing2599 StrongPackedBucketN12A3Shard020.record2599 = true := by
  decide

def missing2600 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47071729270977986560
theorem maskCheck2600 :
    checkMaskFor missing2600 StrongPackedBucketN12A3Shard020.record2600 = true := by
  decide

def missing2601 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47143786865015914496
theorem maskCheck2601 :
    checkMaskFor missing2601 StrongPackedBucketN12A3Shard020.record2601 = true := by
  decide

def missing2602 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 48152593181546905600
theorem maskCheck2602 :
    checkMaskFor missing2602 StrongPackedBucketN12A3Shard020.record2602 = true := by
  decide

def missing2603 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55610554164472446976
theorem maskCheck2603 :
    checkMaskFor missing2603 StrongPackedBucketN12A3Shard020.record2603 = true := by
  decide

def missing2604 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55754669352548302848
theorem maskCheck2604 :
    checkMaskFor missing2604 StrongPackedBucketN12A3Shard020.record2604 = true := by
  decide

def missing2605 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55826726946586230784
theorem maskCheck2605 :
    checkMaskFor missing2605 StrongPackedBucketN12A3Shard020.record2605 = true := by
  decide

def missing2606 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55862755743605194752
theorem maskCheck2606 :
    checkMaskFor missing2606 StrongPackedBucketN12A3Shard020.record2606 = true := by
  decide

def missing2607 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56259072510813798400
theorem maskCheck2607 :
    checkMaskFor missing2607 StrongPackedBucketN12A3Shard020.record2607 = true := by
  decide

def missing2608 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56295101307832762368
theorem maskCheck2608 :
    checkMaskFor missing2608 StrongPackedBucketN12A3Shard020.record2608 = true := by
  decide

def missing2609 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56367158901870690304
theorem maskCheck2609 :
    checkMaskFor missing2609 StrongPackedBucketN12A3Shard020.record2609 = true := by
  decide

def missing2610 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57375965218401681408
theorem maskCheck2610 :
    checkMaskFor missing2610 StrongPackedBucketN12A3Shard020.record2610 = true := by
  decide

def missing2611 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64689811013251366912
theorem maskCheck2611 :
    checkMaskFor missing2611 StrongPackedBucketN12A3Shard020.record2611 = true := by
  decide

def missing2612 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64761868607289294848
theorem maskCheck2612 :
    checkMaskFor missing2612 StrongPackedBucketN12A3Shard020.record2612 = true := by
  decide

def missing2613 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64797897404308258816
theorem maskCheck2613 :
    checkMaskFor missing2613 StrongPackedBucketN12A3Shard020.record2613 = true := by
  decide

def missing2614 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64905983795365150720
theorem maskCheck2614 :
    checkMaskFor missing2614 StrongPackedBucketN12A3Shard020.record2614 = true := by
  decide

def missing2615 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64942012592384114688
theorem maskCheck2615 :
    checkMaskFor missing2615 StrongPackedBucketN12A3Shard020.record2615 = true := by
  decide

def missing2616 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 65014070186422042624
theorem maskCheck2616 :
    checkMaskFor missing2616 StrongPackedBucketN12A3Shard020.record2616 = true := by
  decide

def missing2617 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 65446415750649610240
theorem maskCheck2617 :
    checkMaskFor missing2617 StrongPackedBucketN12A3Shard020.record2617 = true := by
  decide

def missing2618 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1135118624915193856
theorem maskCheck2618 :
    checkMaskFor missing2618 StrongPackedBucketN12A3Shard020.record2618 = true := by
  decide

def missing2619 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2143924941446184960
theorem maskCheck2619 :
    checkMaskFor missing2619 StrongPackedBucketN12A3Shard020.record2619 = true := by
  decide

def missing2620 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2252011332503076864
theorem maskCheck2620 :
    checkMaskFor missing2620 StrongPackedBucketN12A3Shard020.record2620 = true := by
  decide

def missing2621 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4377710356621950976
theorem maskCheck2621 :
    checkMaskFor missing2621 StrongPackedBucketN12A3Shard020.record2621 = true := by
  decide

def missing2622 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4413739153640914944
theorem maskCheck2622 :
    checkMaskFor missing2622 StrongPackedBucketN12A3Shard020.record2622 = true := by
  decide

def missing2623 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8953367578030374912
theorem maskCheck2623 :
    checkMaskFor missing2623 StrongPackedBucketN12A3Shard020.record2623 = true := by
  decide

def missing2624 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9782029909466546176
theorem maskCheck2624 :
    checkMaskFor missing2624 StrongPackedBucketN12A3Shard020.record2624 = true := by
  decide

def missing2625 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10214375473694113792
theorem maskCheck2625 :
    checkMaskFor missing2625 StrongPackedBucketN12A3Shard020.record2625 = true := by
  decide

def missing2626 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11295239384263032832
theorem maskCheck2626 :
    checkMaskFor missing2626 StrongPackedBucketN12A3Shard020.record2626 = true := by
  decide

def missing2627 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19005401946321321984
theorem maskCheck2627 :
    checkMaskFor missing2627 StrongPackedBucketN12A3Shard020.record2627 = true := by
  decide

def missing2628 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19437747510548889600
theorem maskCheck2628 :
    checkMaskFor missing2628 StrongPackedBucketN12A3Shard020.record2628 = true := by
  decide

def missing2629 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19545833901605781504
theorem maskCheck2629 :
    checkMaskFor missing2629 StrongPackedBucketN12A3Shard020.record2629 = true := by
  decide

def missing2630 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20518611421117808640
theorem maskCheck2630 :
    checkMaskFor missing2630 StrongPackedBucketN12A3Shard020.record2630 = true := by
  decide

def missing2631 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20554640218136772608
theorem maskCheck2631 :
    checkMaskFor missing2631 StrongPackedBucketN12A3Shard020.record2631 = true := by
  decide

def missing2632 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22788425633312538624
theorem maskCheck2632 :
    checkMaskFor missing2632 StrongPackedBucketN12A3Shard020.record2632 = true := by
  decide

def missing2633 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27940543607024386048
theorem maskCheck2633 :
    checkMaskFor missing2633 StrongPackedBucketN12A3Shard020.record2633 = true := by
  decide

def missing2634 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28084658795100241920
theorem maskCheck2634 :
    checkMaskFor missing2634 StrongPackedBucketN12A3Shard020.record2634 = true := by
  decide

def missing2635 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28589061953365737472
theorem maskCheck2635 :
    checkMaskFor missing2635 StrongPackedBucketN12A3Shard020.record2635 = true := by
  decide

def missing2636 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55610659717588713472
theorem maskCheck2636 :
    checkMaskFor missing2636 StrongPackedBucketN12A3Shard020.record2636 = true := by
  decide

def missing2637 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55754774905664569344
theorem maskCheck2637 :
    checkMaskFor missing2637 StrongPackedBucketN12A3Shard020.record2637 = true := by
  decide

def missing2638 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55862861296721461248
theorem maskCheck2638 :
    checkMaskFor missing2638 StrongPackedBucketN12A3Shard020.record2638 = true := by
  decide

def missing2639 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56259178063930064896
theorem maskCheck2639 :
    checkMaskFor missing2639 StrongPackedBucketN12A3Shard020.record2639 = true := by
  decide

def missing2640 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56295206860949028864
theorem maskCheck2640 :
    checkMaskFor missing2640 StrongPackedBucketN12A3Shard020.record2640 = true := by
  decide

def missing2641 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57376070771517947904
theorem maskCheck2641 :
    checkMaskFor missing2641 StrongPackedBucketN12A3Shard020.record2641 = true := by
  decide

def missing2642 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64689916566367633408
theorem maskCheck2642 :
    checkMaskFor missing2642 StrongPackedBucketN12A3Shard020.record2642 = true := by
  decide

def missing2643 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64906089348481417216
theorem maskCheck2643 :
    checkMaskFor missing2643 StrongPackedBucketN12A3Shard020.record2643 = true := by
  decide

def missing2644 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1135224178031460352
theorem maskCheck2644 :
    checkMaskFor missing2644 StrongPackedBucketN12A3Shard020.record2644 = true := by
  decide

def missing2645 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1999915306486595584
theorem maskCheck2645 :
    checkMaskFor missing2645 StrongPackedBucketN12A3Shard020.record2645 = true := by
  decide

def missing2646 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2144030494562451456
theorem maskCheck2646 :
    checkMaskFor missing2646 StrongPackedBucketN12A3Shard020.record2646 = true := by
  decide

def missing2647 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2252116885619343360
theorem maskCheck2647 :
    checkMaskFor missing2647 StrongPackedBucketN12A3Shard020.record2647 = true := by
  decide

def missing2648 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4161643127624433664
theorem maskCheck2648 :
    checkMaskFor missing2648 StrongPackedBucketN12A3Shard020.record2648 = true := by
  decide

def missing2649 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4269729518681325568
theorem maskCheck2649 :
    checkMaskFor missing2649 StrongPackedBucketN12A3Shard020.record2649 = true := by
  decide

def missing2650 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4377815909738217472
theorem maskCheck2650 :
    checkMaskFor missing2650 StrongPackedBucketN12A3Shard020.record2650 = true := by
  decide

def missing2651 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4413844706757181440
theorem maskCheck2651 :
    checkMaskFor missing2651 StrongPackedBucketN12A3Shard020.record2651 = true := by
  decide

def missing2652 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8701271552013893632
theorem maskCheck2652 :
    checkMaskFor missing2652 StrongPackedBucketN12A3Shard020.record2652 = true := by
  decide

def missing2653 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8737300349032857600
theorem maskCheck2653 :
    checkMaskFor missing2653 StrongPackedBucketN12A3Shard020.record2653 = true := by
  decide

def missing2654 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8953473131146641408
theorem maskCheck2654 :
    checkMaskFor missing2654 StrongPackedBucketN12A3Shard020.record2654 = true := by
  decide

def missing2655 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9782135462582812672
theorem maskCheck2655 :
    checkMaskFor missing2655 StrongPackedBucketN12A3Shard020.record2655 = true := by
  decide

def missing2656 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10070365838734524416
theorem maskCheck2656 :
    checkMaskFor missing2656 StrongPackedBucketN12A3Shard020.record2656 = true := by
  decide

def missing2657 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10214481026810380288
theorem maskCheck2657 :
    checkMaskFor missing2657 StrongPackedBucketN12A3Shard020.record2657 = true := by
  decide

def missing2658 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10322567417867272192
theorem maskCheck2658 :
    checkMaskFor missing2658 StrongPackedBucketN12A3Shard020.record2658 = true := by
  decide

def missing2659 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11079172155265515520
theorem maskCheck2659 :
    checkMaskFor missing2659 StrongPackedBucketN12A3Shard020.record2659 = true := by
  decide

def missing2660 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11187258546322407424
theorem maskCheck2660 :
    checkMaskFor missing2660 StrongPackedBucketN12A3Shard020.record2660 = true := by
  decide

def missing2661 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11295344937379299328
theorem maskCheck2661 :
    checkMaskFor missing2661 StrongPackedBucketN12A3Shard020.record2661 = true := by
  decide

def missing2662 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11331373734398263296
theorem maskCheck2662 :
    checkMaskFor missing2662 StrongPackedBucketN12A3Shard020.record2662 = true := by
  decide

def missing2663 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13312957570441281536
theorem maskCheck2663 :
    checkMaskFor missing2663 StrongPackedBucketN12A3Shard020.record2663 = true := by
  decide

def missing2664 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13348986367460245504
theorem maskCheck2664 :
    checkMaskFor missing2664 StrongPackedBucketN12A3Shard020.record2664 = true := by
  decide

def missing2665 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13565159149574029312
theorem maskCheck2665 :
    checkMaskFor missing2665 StrongPackedBucketN12A3Shard020.record2665 = true := by
  decide

def missing2666 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 17888614791849705472
theorem maskCheck2666 :
    checkMaskFor missing2666 StrongPackedBucketN12A3Shard020.record2666 = true := by
  decide

def missing2667 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19005507499437588480
theorem maskCheck2667 :
    checkMaskFor missing2667 StrongPackedBucketN12A3Shard020.record2667 = true := by
  decide

def missing2668 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19293737875589300224
theorem maskCheck2668 :
    checkMaskFor missing2668 StrongPackedBucketN12A3Shard020.record2668 = true := by
  decide

def missing2669 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19437853063665156096
theorem maskCheck2669 :
    checkMaskFor missing2669 StrongPackedBucketN12A3Shard020.record2669 = true := by
  decide

def missing2670 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19545939454722048000
theorem maskCheck2670 :
    checkMaskFor missing2670 StrongPackedBucketN12A3Shard020.record2670 = true := by
  decide

def missing2671 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20302544192120291328
theorem maskCheck2671 :
    checkMaskFor missing2671 StrongPackedBucketN12A3Shard020.record2671 = true := by
  decide

def missing2672 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20410630583177183232
theorem maskCheck2672 :
    checkMaskFor missing2672 StrongPackedBucketN12A3Shard020.record2672 = true := by
  decide

def missing2673 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20518716974234075136
theorem maskCheck2673 :
    checkMaskFor missing2673 StrongPackedBucketN12A3Shard020.record2673 = true := by
  decide

def missing2674 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20554745771253039104
theorem maskCheck2674 :
    checkMaskFor missing2674 StrongPackedBucketN12A3Shard020.record2674 = true := by
  decide

def missing2675 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22536329607296057344
theorem maskCheck2675 :
    checkMaskFor missing2675 StrongPackedBucketN12A3Shard020.record2675 = true := by
  decide

def missing2676 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22572358404315021312
theorem maskCheck2676 :
    checkMaskFor missing2676 StrongPackedBucketN12A3Shard020.record2676 = true := by
  decide

def missing2677 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22788531186428805120
theorem maskCheck2677 :
    checkMaskFor missing2677 StrongPackedBucketN12A3Shard020.record2677 = true := by
  decide

def missing2678 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27111986828704481280
theorem maskCheck2678 :
    checkMaskFor missing2678 StrongPackedBucketN12A3Shard020.record2678 = true := by
  decide

def missing2679 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27940649160140652544
theorem maskCheck2679 :
    checkMaskFor missing2679 StrongPackedBucketN12A3Shard020.record2679 = true := by
  decide

def missing2680 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28084764348216508416
theorem maskCheck2680 :
    checkMaskFor missing2680 StrongPackedBucketN12A3Shard020.record2680 = true := by
  decide

def missing2681 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28192850739273400320
theorem maskCheck2681 :
    checkMaskFor missing2681 StrongPackedBucketN12A3Shard020.record2681 = true := by
  decide

def missing2682 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28372994724368220160
theorem maskCheck2682 :
    checkMaskFor missing2682 StrongPackedBucketN12A3Shard020.record2682 = true := by
  decide

def missing2683 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28481081115425112064
theorem maskCheck2683 :
    checkMaskFor missing2683 StrongPackedBucketN12A3Shard020.record2683 = true := by
  decide

def missing2684 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28589167506482003968
theorem maskCheck2684 :
    checkMaskFor missing2684 StrongPackedBucketN12A3Shard020.record2684 = true := by
  decide

def missing2685 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28625196303500967936
theorem maskCheck2685 :
    checkMaskFor missing2685 StrongPackedBucketN12A3Shard020.record2685 = true := by
  decide

def missing2686 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29453858634937139200
theorem maskCheck2686 :
    checkMaskFor missing2686 StrongPackedBucketN12A3Shard020.record2686 = true := by
  decide

def missing2687 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29489887431956103168
theorem maskCheck2687 :
    checkMaskFor missing2687 StrongPackedBucketN12A3Shard020.record2687 = true := by
  decide

def missing2560_2561 : List (BitVec (edgeCount 12)) :=
  [missing2560]
abbrev records2560_2561 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2560]
theorem aligned2560_2561 :
    AlignedValid 12 3 missing2560_2561 records2560_2561 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2560
    maskCheck2560 AlignedValid.nil

def missing2561_2562 : List (BitVec (edgeCount 12)) :=
  [missing2561]
abbrev records2561_2562 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2561]
theorem aligned2561_2562 :
    AlignedValid 12 3 missing2561_2562 records2561_2562 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2561
    maskCheck2561 AlignedValid.nil

def missing2560_2562 : List (BitVec (edgeCount 12)) :=
  missing2560_2561 ++ missing2561_2562
abbrev records2560_2562 : List Blob :=
  records2560_2561 ++ records2561_2562
theorem aligned2560_2562 :
    AlignedValid 12 3 missing2560_2562 records2560_2562 :=
  aligned2560_2561.append aligned2561_2562

def missing2562_2563 : List (BitVec (edgeCount 12)) :=
  [missing2562]
abbrev records2562_2563 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2562]
theorem aligned2562_2563 :
    AlignedValid 12 3 missing2562_2563 records2562_2563 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2562
    maskCheck2562 AlignedValid.nil

def missing2563_2564 : List (BitVec (edgeCount 12)) :=
  [missing2563]
abbrev records2563_2564 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2563]
theorem aligned2563_2564 :
    AlignedValid 12 3 missing2563_2564 records2563_2564 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2563
    maskCheck2563 AlignedValid.nil

def missing2562_2564 : List (BitVec (edgeCount 12)) :=
  missing2562_2563 ++ missing2563_2564
abbrev records2562_2564 : List Blob :=
  records2562_2563 ++ records2563_2564
theorem aligned2562_2564 :
    AlignedValid 12 3 missing2562_2564 records2562_2564 :=
  aligned2562_2563.append aligned2563_2564

def missing2560_2564 : List (BitVec (edgeCount 12)) :=
  missing2560_2562 ++ missing2562_2564
abbrev records2560_2564 : List Blob :=
  records2560_2562 ++ records2562_2564
theorem aligned2560_2564 :
    AlignedValid 12 3 missing2560_2564 records2560_2564 :=
  aligned2560_2562.append aligned2562_2564

def missing2564_2565 : List (BitVec (edgeCount 12)) :=
  [missing2564]
abbrev records2564_2565 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2564]
theorem aligned2564_2565 :
    AlignedValid 12 3 missing2564_2565 records2564_2565 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2564
    maskCheck2564 AlignedValid.nil

def missing2565_2566 : List (BitVec (edgeCount 12)) :=
  [missing2565]
abbrev records2565_2566 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2565]
theorem aligned2565_2566 :
    AlignedValid 12 3 missing2565_2566 records2565_2566 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2565
    maskCheck2565 AlignedValid.nil

def missing2564_2566 : List (BitVec (edgeCount 12)) :=
  missing2564_2565 ++ missing2565_2566
abbrev records2564_2566 : List Blob :=
  records2564_2565 ++ records2565_2566
theorem aligned2564_2566 :
    AlignedValid 12 3 missing2564_2566 records2564_2566 :=
  aligned2564_2565.append aligned2565_2566

def missing2566_2567 : List (BitVec (edgeCount 12)) :=
  [missing2566]
abbrev records2566_2567 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2566]
theorem aligned2566_2567 :
    AlignedValid 12 3 missing2566_2567 records2566_2567 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2566
    maskCheck2566 AlignedValid.nil

def missing2567_2568 : List (BitVec (edgeCount 12)) :=
  [missing2567]
abbrev records2567_2568 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2567]
theorem aligned2567_2568 :
    AlignedValid 12 3 missing2567_2568 records2567_2568 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2567
    maskCheck2567 AlignedValid.nil

def missing2566_2568 : List (BitVec (edgeCount 12)) :=
  missing2566_2567 ++ missing2567_2568
abbrev records2566_2568 : List Blob :=
  records2566_2567 ++ records2567_2568
theorem aligned2566_2568 :
    AlignedValid 12 3 missing2566_2568 records2566_2568 :=
  aligned2566_2567.append aligned2567_2568

def missing2564_2568 : List (BitVec (edgeCount 12)) :=
  missing2564_2566 ++ missing2566_2568
abbrev records2564_2568 : List Blob :=
  records2564_2566 ++ records2566_2568
theorem aligned2564_2568 :
    AlignedValid 12 3 missing2564_2568 records2564_2568 :=
  aligned2564_2566.append aligned2566_2568

def missing2560_2568 : List (BitVec (edgeCount 12)) :=
  missing2560_2564 ++ missing2564_2568
abbrev records2560_2568 : List Blob :=
  records2560_2564 ++ records2564_2568
theorem aligned2560_2568 :
    AlignedValid 12 3 missing2560_2568 records2560_2568 :=
  aligned2560_2564.append aligned2564_2568

def missing2568_2569 : List (BitVec (edgeCount 12)) :=
  [missing2568]
abbrev records2568_2569 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2568]
theorem aligned2568_2569 :
    AlignedValid 12 3 missing2568_2569 records2568_2569 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2568
    maskCheck2568 AlignedValid.nil

def missing2569_2570 : List (BitVec (edgeCount 12)) :=
  [missing2569]
abbrev records2569_2570 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2569]
theorem aligned2569_2570 :
    AlignedValid 12 3 missing2569_2570 records2569_2570 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2569
    maskCheck2569 AlignedValid.nil

def missing2568_2570 : List (BitVec (edgeCount 12)) :=
  missing2568_2569 ++ missing2569_2570
abbrev records2568_2570 : List Blob :=
  records2568_2569 ++ records2569_2570
theorem aligned2568_2570 :
    AlignedValid 12 3 missing2568_2570 records2568_2570 :=
  aligned2568_2569.append aligned2569_2570

def missing2570_2571 : List (BitVec (edgeCount 12)) :=
  [missing2570]
abbrev records2570_2571 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2570]
theorem aligned2570_2571 :
    AlignedValid 12 3 missing2570_2571 records2570_2571 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2570
    maskCheck2570 AlignedValid.nil

def missing2571_2572 : List (BitVec (edgeCount 12)) :=
  [missing2571]
abbrev records2571_2572 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2571]
theorem aligned2571_2572 :
    AlignedValid 12 3 missing2571_2572 records2571_2572 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2571
    maskCheck2571 AlignedValid.nil

def missing2570_2572 : List (BitVec (edgeCount 12)) :=
  missing2570_2571 ++ missing2571_2572
abbrev records2570_2572 : List Blob :=
  records2570_2571 ++ records2571_2572
theorem aligned2570_2572 :
    AlignedValid 12 3 missing2570_2572 records2570_2572 :=
  aligned2570_2571.append aligned2571_2572

def missing2568_2572 : List (BitVec (edgeCount 12)) :=
  missing2568_2570 ++ missing2570_2572
abbrev records2568_2572 : List Blob :=
  records2568_2570 ++ records2570_2572
theorem aligned2568_2572 :
    AlignedValid 12 3 missing2568_2572 records2568_2572 :=
  aligned2568_2570.append aligned2570_2572

def missing2572_2573 : List (BitVec (edgeCount 12)) :=
  [missing2572]
abbrev records2572_2573 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2572]
theorem aligned2572_2573 :
    AlignedValid 12 3 missing2572_2573 records2572_2573 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2572
    maskCheck2572 AlignedValid.nil

def missing2573_2574 : List (BitVec (edgeCount 12)) :=
  [missing2573]
abbrev records2573_2574 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2573]
theorem aligned2573_2574 :
    AlignedValid 12 3 missing2573_2574 records2573_2574 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2573
    maskCheck2573 AlignedValid.nil

def missing2572_2574 : List (BitVec (edgeCount 12)) :=
  missing2572_2573 ++ missing2573_2574
abbrev records2572_2574 : List Blob :=
  records2572_2573 ++ records2573_2574
theorem aligned2572_2574 :
    AlignedValid 12 3 missing2572_2574 records2572_2574 :=
  aligned2572_2573.append aligned2573_2574

def missing2574_2575 : List (BitVec (edgeCount 12)) :=
  [missing2574]
abbrev records2574_2575 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2574]
theorem aligned2574_2575 :
    AlignedValid 12 3 missing2574_2575 records2574_2575 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2574
    maskCheck2574 AlignedValid.nil

def missing2575_2576 : List (BitVec (edgeCount 12)) :=
  [missing2575]
abbrev records2575_2576 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2575]
theorem aligned2575_2576 :
    AlignedValid 12 3 missing2575_2576 records2575_2576 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2575
    maskCheck2575 AlignedValid.nil

def missing2574_2576 : List (BitVec (edgeCount 12)) :=
  missing2574_2575 ++ missing2575_2576
abbrev records2574_2576 : List Blob :=
  records2574_2575 ++ records2575_2576
theorem aligned2574_2576 :
    AlignedValid 12 3 missing2574_2576 records2574_2576 :=
  aligned2574_2575.append aligned2575_2576

def missing2572_2576 : List (BitVec (edgeCount 12)) :=
  missing2572_2574 ++ missing2574_2576
abbrev records2572_2576 : List Blob :=
  records2572_2574 ++ records2574_2576
theorem aligned2572_2576 :
    AlignedValid 12 3 missing2572_2576 records2572_2576 :=
  aligned2572_2574.append aligned2574_2576

def missing2568_2576 : List (BitVec (edgeCount 12)) :=
  missing2568_2572 ++ missing2572_2576
abbrev records2568_2576 : List Blob :=
  records2568_2572 ++ records2572_2576
theorem aligned2568_2576 :
    AlignedValid 12 3 missing2568_2576 records2568_2576 :=
  aligned2568_2572.append aligned2572_2576

def missing2560_2576 : List (BitVec (edgeCount 12)) :=
  missing2560_2568 ++ missing2568_2576
abbrev records2560_2576 : List Blob :=
  records2560_2568 ++ records2568_2576
theorem aligned2560_2576 :
    AlignedValid 12 3 missing2560_2576 records2560_2576 :=
  aligned2560_2568.append aligned2568_2576

def missing2576_2577 : List (BitVec (edgeCount 12)) :=
  [missing2576]
abbrev records2576_2577 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2576]
theorem aligned2576_2577 :
    AlignedValid 12 3 missing2576_2577 records2576_2577 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2576
    maskCheck2576 AlignedValid.nil

def missing2577_2578 : List (BitVec (edgeCount 12)) :=
  [missing2577]
abbrev records2577_2578 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2577]
theorem aligned2577_2578 :
    AlignedValid 12 3 missing2577_2578 records2577_2578 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2577
    maskCheck2577 AlignedValid.nil

def missing2576_2578 : List (BitVec (edgeCount 12)) :=
  missing2576_2577 ++ missing2577_2578
abbrev records2576_2578 : List Blob :=
  records2576_2577 ++ records2577_2578
theorem aligned2576_2578 :
    AlignedValid 12 3 missing2576_2578 records2576_2578 :=
  aligned2576_2577.append aligned2577_2578

def missing2578_2579 : List (BitVec (edgeCount 12)) :=
  [missing2578]
abbrev records2578_2579 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2578]
theorem aligned2578_2579 :
    AlignedValid 12 3 missing2578_2579 records2578_2579 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2578
    maskCheck2578 AlignedValid.nil

def missing2579_2580 : List (BitVec (edgeCount 12)) :=
  [missing2579]
abbrev records2579_2580 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2579]
theorem aligned2579_2580 :
    AlignedValid 12 3 missing2579_2580 records2579_2580 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2579
    maskCheck2579 AlignedValid.nil

def missing2578_2580 : List (BitVec (edgeCount 12)) :=
  missing2578_2579 ++ missing2579_2580
abbrev records2578_2580 : List Blob :=
  records2578_2579 ++ records2579_2580
theorem aligned2578_2580 :
    AlignedValid 12 3 missing2578_2580 records2578_2580 :=
  aligned2578_2579.append aligned2579_2580

def missing2576_2580 : List (BitVec (edgeCount 12)) :=
  missing2576_2578 ++ missing2578_2580
abbrev records2576_2580 : List Blob :=
  records2576_2578 ++ records2578_2580
theorem aligned2576_2580 :
    AlignedValid 12 3 missing2576_2580 records2576_2580 :=
  aligned2576_2578.append aligned2578_2580

def missing2580_2581 : List (BitVec (edgeCount 12)) :=
  [missing2580]
abbrev records2580_2581 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2580]
theorem aligned2580_2581 :
    AlignedValid 12 3 missing2580_2581 records2580_2581 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2580
    maskCheck2580 AlignedValid.nil

def missing2581_2582 : List (BitVec (edgeCount 12)) :=
  [missing2581]
abbrev records2581_2582 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2581]
theorem aligned2581_2582 :
    AlignedValid 12 3 missing2581_2582 records2581_2582 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2581
    maskCheck2581 AlignedValid.nil

def missing2580_2582 : List (BitVec (edgeCount 12)) :=
  missing2580_2581 ++ missing2581_2582
abbrev records2580_2582 : List Blob :=
  records2580_2581 ++ records2581_2582
theorem aligned2580_2582 :
    AlignedValid 12 3 missing2580_2582 records2580_2582 :=
  aligned2580_2581.append aligned2581_2582

def missing2582_2583 : List (BitVec (edgeCount 12)) :=
  [missing2582]
abbrev records2582_2583 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2582]
theorem aligned2582_2583 :
    AlignedValid 12 3 missing2582_2583 records2582_2583 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2582
    maskCheck2582 AlignedValid.nil

def missing2583_2584 : List (BitVec (edgeCount 12)) :=
  [missing2583]
abbrev records2583_2584 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2583]
theorem aligned2583_2584 :
    AlignedValid 12 3 missing2583_2584 records2583_2584 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2583
    maskCheck2583 AlignedValid.nil

def missing2582_2584 : List (BitVec (edgeCount 12)) :=
  missing2582_2583 ++ missing2583_2584
abbrev records2582_2584 : List Blob :=
  records2582_2583 ++ records2583_2584
theorem aligned2582_2584 :
    AlignedValid 12 3 missing2582_2584 records2582_2584 :=
  aligned2582_2583.append aligned2583_2584

def missing2580_2584 : List (BitVec (edgeCount 12)) :=
  missing2580_2582 ++ missing2582_2584
abbrev records2580_2584 : List Blob :=
  records2580_2582 ++ records2582_2584
theorem aligned2580_2584 :
    AlignedValid 12 3 missing2580_2584 records2580_2584 :=
  aligned2580_2582.append aligned2582_2584

def missing2576_2584 : List (BitVec (edgeCount 12)) :=
  missing2576_2580 ++ missing2580_2584
abbrev records2576_2584 : List Blob :=
  records2576_2580 ++ records2580_2584
theorem aligned2576_2584 :
    AlignedValid 12 3 missing2576_2584 records2576_2584 :=
  aligned2576_2580.append aligned2580_2584

def missing2584_2585 : List (BitVec (edgeCount 12)) :=
  [missing2584]
abbrev records2584_2585 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2584]
theorem aligned2584_2585 :
    AlignedValid 12 3 missing2584_2585 records2584_2585 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2584
    maskCheck2584 AlignedValid.nil

def missing2585_2586 : List (BitVec (edgeCount 12)) :=
  [missing2585]
abbrev records2585_2586 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2585]
theorem aligned2585_2586 :
    AlignedValid 12 3 missing2585_2586 records2585_2586 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2585
    maskCheck2585 AlignedValid.nil

def missing2584_2586 : List (BitVec (edgeCount 12)) :=
  missing2584_2585 ++ missing2585_2586
abbrev records2584_2586 : List Blob :=
  records2584_2585 ++ records2585_2586
theorem aligned2584_2586 :
    AlignedValid 12 3 missing2584_2586 records2584_2586 :=
  aligned2584_2585.append aligned2585_2586

def missing2586_2587 : List (BitVec (edgeCount 12)) :=
  [missing2586]
abbrev records2586_2587 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2586]
theorem aligned2586_2587 :
    AlignedValid 12 3 missing2586_2587 records2586_2587 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2586
    maskCheck2586 AlignedValid.nil

def missing2587_2588 : List (BitVec (edgeCount 12)) :=
  [missing2587]
abbrev records2587_2588 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2587]
theorem aligned2587_2588 :
    AlignedValid 12 3 missing2587_2588 records2587_2588 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2587
    maskCheck2587 AlignedValid.nil

def missing2586_2588 : List (BitVec (edgeCount 12)) :=
  missing2586_2587 ++ missing2587_2588
abbrev records2586_2588 : List Blob :=
  records2586_2587 ++ records2587_2588
theorem aligned2586_2588 :
    AlignedValid 12 3 missing2586_2588 records2586_2588 :=
  aligned2586_2587.append aligned2587_2588

def missing2584_2588 : List (BitVec (edgeCount 12)) :=
  missing2584_2586 ++ missing2586_2588
abbrev records2584_2588 : List Blob :=
  records2584_2586 ++ records2586_2588
theorem aligned2584_2588 :
    AlignedValid 12 3 missing2584_2588 records2584_2588 :=
  aligned2584_2586.append aligned2586_2588

def missing2588_2589 : List (BitVec (edgeCount 12)) :=
  [missing2588]
abbrev records2588_2589 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2588]
theorem aligned2588_2589 :
    AlignedValid 12 3 missing2588_2589 records2588_2589 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2588
    maskCheck2588 AlignedValid.nil

def missing2589_2590 : List (BitVec (edgeCount 12)) :=
  [missing2589]
abbrev records2589_2590 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2589]
theorem aligned2589_2590 :
    AlignedValid 12 3 missing2589_2590 records2589_2590 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2589
    maskCheck2589 AlignedValid.nil

def missing2588_2590 : List (BitVec (edgeCount 12)) :=
  missing2588_2589 ++ missing2589_2590
abbrev records2588_2590 : List Blob :=
  records2588_2589 ++ records2589_2590
theorem aligned2588_2590 :
    AlignedValid 12 3 missing2588_2590 records2588_2590 :=
  aligned2588_2589.append aligned2589_2590

def missing2590_2591 : List (BitVec (edgeCount 12)) :=
  [missing2590]
abbrev records2590_2591 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2590]
theorem aligned2590_2591 :
    AlignedValid 12 3 missing2590_2591 records2590_2591 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2590
    maskCheck2590 AlignedValid.nil

def missing2591_2592 : List (BitVec (edgeCount 12)) :=
  [missing2591]
abbrev records2591_2592 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2591]
theorem aligned2591_2592 :
    AlignedValid 12 3 missing2591_2592 records2591_2592 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2591
    maskCheck2591 AlignedValid.nil

def missing2590_2592 : List (BitVec (edgeCount 12)) :=
  missing2590_2591 ++ missing2591_2592
abbrev records2590_2592 : List Blob :=
  records2590_2591 ++ records2591_2592
theorem aligned2590_2592 :
    AlignedValid 12 3 missing2590_2592 records2590_2592 :=
  aligned2590_2591.append aligned2591_2592

def missing2588_2592 : List (BitVec (edgeCount 12)) :=
  missing2588_2590 ++ missing2590_2592
abbrev records2588_2592 : List Blob :=
  records2588_2590 ++ records2590_2592
theorem aligned2588_2592 :
    AlignedValid 12 3 missing2588_2592 records2588_2592 :=
  aligned2588_2590.append aligned2590_2592

def missing2584_2592 : List (BitVec (edgeCount 12)) :=
  missing2584_2588 ++ missing2588_2592
abbrev records2584_2592 : List Blob :=
  records2584_2588 ++ records2588_2592
theorem aligned2584_2592 :
    AlignedValid 12 3 missing2584_2592 records2584_2592 :=
  aligned2584_2588.append aligned2588_2592

def missing2576_2592 : List (BitVec (edgeCount 12)) :=
  missing2576_2584 ++ missing2584_2592
abbrev records2576_2592 : List Blob :=
  records2576_2584 ++ records2584_2592
theorem aligned2576_2592 :
    AlignedValid 12 3 missing2576_2592 records2576_2592 :=
  aligned2576_2584.append aligned2584_2592

def missing2560_2592 : List (BitVec (edgeCount 12)) :=
  missing2560_2576 ++ missing2576_2592
abbrev records2560_2592 : List Blob :=
  records2560_2576 ++ records2576_2592
theorem aligned2560_2592 :
    AlignedValid 12 3 missing2560_2592 records2560_2592 :=
  aligned2560_2576.append aligned2576_2592

def missing2592_2593 : List (BitVec (edgeCount 12)) :=
  [missing2592]
abbrev records2592_2593 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2592]
theorem aligned2592_2593 :
    AlignedValid 12 3 missing2592_2593 records2592_2593 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2592
    maskCheck2592 AlignedValid.nil

def missing2593_2594 : List (BitVec (edgeCount 12)) :=
  [missing2593]
abbrev records2593_2594 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2593]
theorem aligned2593_2594 :
    AlignedValid 12 3 missing2593_2594 records2593_2594 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2593
    maskCheck2593 AlignedValid.nil

def missing2592_2594 : List (BitVec (edgeCount 12)) :=
  missing2592_2593 ++ missing2593_2594
abbrev records2592_2594 : List Blob :=
  records2592_2593 ++ records2593_2594
theorem aligned2592_2594 :
    AlignedValid 12 3 missing2592_2594 records2592_2594 :=
  aligned2592_2593.append aligned2593_2594

def missing2594_2595 : List (BitVec (edgeCount 12)) :=
  [missing2594]
abbrev records2594_2595 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2594]
theorem aligned2594_2595 :
    AlignedValid 12 3 missing2594_2595 records2594_2595 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2594
    maskCheck2594 AlignedValid.nil

def missing2595_2596 : List (BitVec (edgeCount 12)) :=
  [missing2595]
abbrev records2595_2596 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2595]
theorem aligned2595_2596 :
    AlignedValid 12 3 missing2595_2596 records2595_2596 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2595
    maskCheck2595 AlignedValid.nil

def missing2594_2596 : List (BitVec (edgeCount 12)) :=
  missing2594_2595 ++ missing2595_2596
abbrev records2594_2596 : List Blob :=
  records2594_2595 ++ records2595_2596
theorem aligned2594_2596 :
    AlignedValid 12 3 missing2594_2596 records2594_2596 :=
  aligned2594_2595.append aligned2595_2596

def missing2592_2596 : List (BitVec (edgeCount 12)) :=
  missing2592_2594 ++ missing2594_2596
abbrev records2592_2596 : List Blob :=
  records2592_2594 ++ records2594_2596
theorem aligned2592_2596 :
    AlignedValid 12 3 missing2592_2596 records2592_2596 :=
  aligned2592_2594.append aligned2594_2596

def missing2596_2597 : List (BitVec (edgeCount 12)) :=
  [missing2596]
abbrev records2596_2597 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2596]
theorem aligned2596_2597 :
    AlignedValid 12 3 missing2596_2597 records2596_2597 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2596
    maskCheck2596 AlignedValid.nil

def missing2597_2598 : List (BitVec (edgeCount 12)) :=
  [missing2597]
abbrev records2597_2598 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2597]
theorem aligned2597_2598 :
    AlignedValid 12 3 missing2597_2598 records2597_2598 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2597
    maskCheck2597 AlignedValid.nil

def missing2596_2598 : List (BitVec (edgeCount 12)) :=
  missing2596_2597 ++ missing2597_2598
abbrev records2596_2598 : List Blob :=
  records2596_2597 ++ records2597_2598
theorem aligned2596_2598 :
    AlignedValid 12 3 missing2596_2598 records2596_2598 :=
  aligned2596_2597.append aligned2597_2598

def missing2598_2599 : List (BitVec (edgeCount 12)) :=
  [missing2598]
abbrev records2598_2599 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2598]
theorem aligned2598_2599 :
    AlignedValid 12 3 missing2598_2599 records2598_2599 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2598
    maskCheck2598 AlignedValid.nil

def missing2599_2600 : List (BitVec (edgeCount 12)) :=
  [missing2599]
abbrev records2599_2600 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2599]
theorem aligned2599_2600 :
    AlignedValid 12 3 missing2599_2600 records2599_2600 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2599
    maskCheck2599 AlignedValid.nil

def missing2598_2600 : List (BitVec (edgeCount 12)) :=
  missing2598_2599 ++ missing2599_2600
abbrev records2598_2600 : List Blob :=
  records2598_2599 ++ records2599_2600
theorem aligned2598_2600 :
    AlignedValid 12 3 missing2598_2600 records2598_2600 :=
  aligned2598_2599.append aligned2599_2600

def missing2596_2600 : List (BitVec (edgeCount 12)) :=
  missing2596_2598 ++ missing2598_2600
abbrev records2596_2600 : List Blob :=
  records2596_2598 ++ records2598_2600
theorem aligned2596_2600 :
    AlignedValid 12 3 missing2596_2600 records2596_2600 :=
  aligned2596_2598.append aligned2598_2600

def missing2592_2600 : List (BitVec (edgeCount 12)) :=
  missing2592_2596 ++ missing2596_2600
abbrev records2592_2600 : List Blob :=
  records2592_2596 ++ records2596_2600
theorem aligned2592_2600 :
    AlignedValid 12 3 missing2592_2600 records2592_2600 :=
  aligned2592_2596.append aligned2596_2600

def missing2600_2601 : List (BitVec (edgeCount 12)) :=
  [missing2600]
abbrev records2600_2601 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2600]
theorem aligned2600_2601 :
    AlignedValid 12 3 missing2600_2601 records2600_2601 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2600
    maskCheck2600 AlignedValid.nil

def missing2601_2602 : List (BitVec (edgeCount 12)) :=
  [missing2601]
abbrev records2601_2602 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2601]
theorem aligned2601_2602 :
    AlignedValid 12 3 missing2601_2602 records2601_2602 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2601
    maskCheck2601 AlignedValid.nil

def missing2600_2602 : List (BitVec (edgeCount 12)) :=
  missing2600_2601 ++ missing2601_2602
abbrev records2600_2602 : List Blob :=
  records2600_2601 ++ records2601_2602
theorem aligned2600_2602 :
    AlignedValid 12 3 missing2600_2602 records2600_2602 :=
  aligned2600_2601.append aligned2601_2602

def missing2602_2603 : List (BitVec (edgeCount 12)) :=
  [missing2602]
abbrev records2602_2603 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2602]
theorem aligned2602_2603 :
    AlignedValid 12 3 missing2602_2603 records2602_2603 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2602
    maskCheck2602 AlignedValid.nil

def missing2603_2604 : List (BitVec (edgeCount 12)) :=
  [missing2603]
abbrev records2603_2604 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2603]
theorem aligned2603_2604 :
    AlignedValid 12 3 missing2603_2604 records2603_2604 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2603
    maskCheck2603 AlignedValid.nil

def missing2602_2604 : List (BitVec (edgeCount 12)) :=
  missing2602_2603 ++ missing2603_2604
abbrev records2602_2604 : List Blob :=
  records2602_2603 ++ records2603_2604
theorem aligned2602_2604 :
    AlignedValid 12 3 missing2602_2604 records2602_2604 :=
  aligned2602_2603.append aligned2603_2604

def missing2600_2604 : List (BitVec (edgeCount 12)) :=
  missing2600_2602 ++ missing2602_2604
abbrev records2600_2604 : List Blob :=
  records2600_2602 ++ records2602_2604
theorem aligned2600_2604 :
    AlignedValid 12 3 missing2600_2604 records2600_2604 :=
  aligned2600_2602.append aligned2602_2604

def missing2604_2605 : List (BitVec (edgeCount 12)) :=
  [missing2604]
abbrev records2604_2605 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2604]
theorem aligned2604_2605 :
    AlignedValid 12 3 missing2604_2605 records2604_2605 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2604
    maskCheck2604 AlignedValid.nil

def missing2605_2606 : List (BitVec (edgeCount 12)) :=
  [missing2605]
abbrev records2605_2606 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2605]
theorem aligned2605_2606 :
    AlignedValid 12 3 missing2605_2606 records2605_2606 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2605
    maskCheck2605 AlignedValid.nil

def missing2604_2606 : List (BitVec (edgeCount 12)) :=
  missing2604_2605 ++ missing2605_2606
abbrev records2604_2606 : List Blob :=
  records2604_2605 ++ records2605_2606
theorem aligned2604_2606 :
    AlignedValid 12 3 missing2604_2606 records2604_2606 :=
  aligned2604_2605.append aligned2605_2606

def missing2606_2607 : List (BitVec (edgeCount 12)) :=
  [missing2606]
abbrev records2606_2607 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2606]
theorem aligned2606_2607 :
    AlignedValid 12 3 missing2606_2607 records2606_2607 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2606
    maskCheck2606 AlignedValid.nil

def missing2607_2608 : List (BitVec (edgeCount 12)) :=
  [missing2607]
abbrev records2607_2608 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2607]
theorem aligned2607_2608 :
    AlignedValid 12 3 missing2607_2608 records2607_2608 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2607
    maskCheck2607 AlignedValid.nil

def missing2606_2608 : List (BitVec (edgeCount 12)) :=
  missing2606_2607 ++ missing2607_2608
abbrev records2606_2608 : List Blob :=
  records2606_2607 ++ records2607_2608
theorem aligned2606_2608 :
    AlignedValid 12 3 missing2606_2608 records2606_2608 :=
  aligned2606_2607.append aligned2607_2608

def missing2604_2608 : List (BitVec (edgeCount 12)) :=
  missing2604_2606 ++ missing2606_2608
abbrev records2604_2608 : List Blob :=
  records2604_2606 ++ records2606_2608
theorem aligned2604_2608 :
    AlignedValid 12 3 missing2604_2608 records2604_2608 :=
  aligned2604_2606.append aligned2606_2608

def missing2600_2608 : List (BitVec (edgeCount 12)) :=
  missing2600_2604 ++ missing2604_2608
abbrev records2600_2608 : List Blob :=
  records2600_2604 ++ records2604_2608
theorem aligned2600_2608 :
    AlignedValid 12 3 missing2600_2608 records2600_2608 :=
  aligned2600_2604.append aligned2604_2608

def missing2592_2608 : List (BitVec (edgeCount 12)) :=
  missing2592_2600 ++ missing2600_2608
abbrev records2592_2608 : List Blob :=
  records2592_2600 ++ records2600_2608
theorem aligned2592_2608 :
    AlignedValid 12 3 missing2592_2608 records2592_2608 :=
  aligned2592_2600.append aligned2600_2608

def missing2608_2609 : List (BitVec (edgeCount 12)) :=
  [missing2608]
abbrev records2608_2609 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2608]
theorem aligned2608_2609 :
    AlignedValid 12 3 missing2608_2609 records2608_2609 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2608
    maskCheck2608 AlignedValid.nil

def missing2609_2610 : List (BitVec (edgeCount 12)) :=
  [missing2609]
abbrev records2609_2610 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2609]
theorem aligned2609_2610 :
    AlignedValid 12 3 missing2609_2610 records2609_2610 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2609
    maskCheck2609 AlignedValid.nil

def missing2608_2610 : List (BitVec (edgeCount 12)) :=
  missing2608_2609 ++ missing2609_2610
abbrev records2608_2610 : List Blob :=
  records2608_2609 ++ records2609_2610
theorem aligned2608_2610 :
    AlignedValid 12 3 missing2608_2610 records2608_2610 :=
  aligned2608_2609.append aligned2609_2610

def missing2610_2611 : List (BitVec (edgeCount 12)) :=
  [missing2610]
abbrev records2610_2611 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2610]
theorem aligned2610_2611 :
    AlignedValid 12 3 missing2610_2611 records2610_2611 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2610
    maskCheck2610 AlignedValid.nil

def missing2611_2612 : List (BitVec (edgeCount 12)) :=
  [missing2611]
abbrev records2611_2612 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2611]
theorem aligned2611_2612 :
    AlignedValid 12 3 missing2611_2612 records2611_2612 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2611
    maskCheck2611 AlignedValid.nil

def missing2610_2612 : List (BitVec (edgeCount 12)) :=
  missing2610_2611 ++ missing2611_2612
abbrev records2610_2612 : List Blob :=
  records2610_2611 ++ records2611_2612
theorem aligned2610_2612 :
    AlignedValid 12 3 missing2610_2612 records2610_2612 :=
  aligned2610_2611.append aligned2611_2612

def missing2608_2612 : List (BitVec (edgeCount 12)) :=
  missing2608_2610 ++ missing2610_2612
abbrev records2608_2612 : List Blob :=
  records2608_2610 ++ records2610_2612
theorem aligned2608_2612 :
    AlignedValid 12 3 missing2608_2612 records2608_2612 :=
  aligned2608_2610.append aligned2610_2612

def missing2612_2613 : List (BitVec (edgeCount 12)) :=
  [missing2612]
abbrev records2612_2613 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2612]
theorem aligned2612_2613 :
    AlignedValid 12 3 missing2612_2613 records2612_2613 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2612
    maskCheck2612 AlignedValid.nil

def missing2613_2614 : List (BitVec (edgeCount 12)) :=
  [missing2613]
abbrev records2613_2614 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2613]
theorem aligned2613_2614 :
    AlignedValid 12 3 missing2613_2614 records2613_2614 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2613
    maskCheck2613 AlignedValid.nil

def missing2612_2614 : List (BitVec (edgeCount 12)) :=
  missing2612_2613 ++ missing2613_2614
abbrev records2612_2614 : List Blob :=
  records2612_2613 ++ records2613_2614
theorem aligned2612_2614 :
    AlignedValid 12 3 missing2612_2614 records2612_2614 :=
  aligned2612_2613.append aligned2613_2614

def missing2614_2615 : List (BitVec (edgeCount 12)) :=
  [missing2614]
abbrev records2614_2615 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2614]
theorem aligned2614_2615 :
    AlignedValid 12 3 missing2614_2615 records2614_2615 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2614
    maskCheck2614 AlignedValid.nil

def missing2615_2616 : List (BitVec (edgeCount 12)) :=
  [missing2615]
abbrev records2615_2616 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2615]
theorem aligned2615_2616 :
    AlignedValid 12 3 missing2615_2616 records2615_2616 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2615
    maskCheck2615 AlignedValid.nil

def missing2614_2616 : List (BitVec (edgeCount 12)) :=
  missing2614_2615 ++ missing2615_2616
abbrev records2614_2616 : List Blob :=
  records2614_2615 ++ records2615_2616
theorem aligned2614_2616 :
    AlignedValid 12 3 missing2614_2616 records2614_2616 :=
  aligned2614_2615.append aligned2615_2616

def missing2612_2616 : List (BitVec (edgeCount 12)) :=
  missing2612_2614 ++ missing2614_2616
abbrev records2612_2616 : List Blob :=
  records2612_2614 ++ records2614_2616
theorem aligned2612_2616 :
    AlignedValid 12 3 missing2612_2616 records2612_2616 :=
  aligned2612_2614.append aligned2614_2616

def missing2608_2616 : List (BitVec (edgeCount 12)) :=
  missing2608_2612 ++ missing2612_2616
abbrev records2608_2616 : List Blob :=
  records2608_2612 ++ records2612_2616
theorem aligned2608_2616 :
    AlignedValid 12 3 missing2608_2616 records2608_2616 :=
  aligned2608_2612.append aligned2612_2616

def missing2616_2617 : List (BitVec (edgeCount 12)) :=
  [missing2616]
abbrev records2616_2617 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2616]
theorem aligned2616_2617 :
    AlignedValid 12 3 missing2616_2617 records2616_2617 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2616
    maskCheck2616 AlignedValid.nil

def missing2617_2618 : List (BitVec (edgeCount 12)) :=
  [missing2617]
abbrev records2617_2618 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2617]
theorem aligned2617_2618 :
    AlignedValid 12 3 missing2617_2618 records2617_2618 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2617
    maskCheck2617 AlignedValid.nil

def missing2616_2618 : List (BitVec (edgeCount 12)) :=
  missing2616_2617 ++ missing2617_2618
abbrev records2616_2618 : List Blob :=
  records2616_2617 ++ records2617_2618
theorem aligned2616_2618 :
    AlignedValid 12 3 missing2616_2618 records2616_2618 :=
  aligned2616_2617.append aligned2617_2618

def missing2618_2619 : List (BitVec (edgeCount 12)) :=
  [missing2618]
abbrev records2618_2619 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2618]
theorem aligned2618_2619 :
    AlignedValid 12 3 missing2618_2619 records2618_2619 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2618
    maskCheck2618 AlignedValid.nil

def missing2619_2620 : List (BitVec (edgeCount 12)) :=
  [missing2619]
abbrev records2619_2620 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2619]
theorem aligned2619_2620 :
    AlignedValid 12 3 missing2619_2620 records2619_2620 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2619
    maskCheck2619 AlignedValid.nil

def missing2618_2620 : List (BitVec (edgeCount 12)) :=
  missing2618_2619 ++ missing2619_2620
abbrev records2618_2620 : List Blob :=
  records2618_2619 ++ records2619_2620
theorem aligned2618_2620 :
    AlignedValid 12 3 missing2618_2620 records2618_2620 :=
  aligned2618_2619.append aligned2619_2620

def missing2616_2620 : List (BitVec (edgeCount 12)) :=
  missing2616_2618 ++ missing2618_2620
abbrev records2616_2620 : List Blob :=
  records2616_2618 ++ records2618_2620
theorem aligned2616_2620 :
    AlignedValid 12 3 missing2616_2620 records2616_2620 :=
  aligned2616_2618.append aligned2618_2620

def missing2620_2621 : List (BitVec (edgeCount 12)) :=
  [missing2620]
abbrev records2620_2621 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2620]
theorem aligned2620_2621 :
    AlignedValid 12 3 missing2620_2621 records2620_2621 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2620
    maskCheck2620 AlignedValid.nil

def missing2621_2622 : List (BitVec (edgeCount 12)) :=
  [missing2621]
abbrev records2621_2622 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2621]
theorem aligned2621_2622 :
    AlignedValid 12 3 missing2621_2622 records2621_2622 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2621
    maskCheck2621 AlignedValid.nil

def missing2620_2622 : List (BitVec (edgeCount 12)) :=
  missing2620_2621 ++ missing2621_2622
abbrev records2620_2622 : List Blob :=
  records2620_2621 ++ records2621_2622
theorem aligned2620_2622 :
    AlignedValid 12 3 missing2620_2622 records2620_2622 :=
  aligned2620_2621.append aligned2621_2622

def missing2622_2623 : List (BitVec (edgeCount 12)) :=
  [missing2622]
abbrev records2622_2623 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2622]
theorem aligned2622_2623 :
    AlignedValid 12 3 missing2622_2623 records2622_2623 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2622
    maskCheck2622 AlignedValid.nil

def missing2623_2624 : List (BitVec (edgeCount 12)) :=
  [missing2623]
abbrev records2623_2624 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2623]
theorem aligned2623_2624 :
    AlignedValid 12 3 missing2623_2624 records2623_2624 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2623
    maskCheck2623 AlignedValid.nil

def missing2622_2624 : List (BitVec (edgeCount 12)) :=
  missing2622_2623 ++ missing2623_2624
abbrev records2622_2624 : List Blob :=
  records2622_2623 ++ records2623_2624
theorem aligned2622_2624 :
    AlignedValid 12 3 missing2622_2624 records2622_2624 :=
  aligned2622_2623.append aligned2623_2624

def missing2620_2624 : List (BitVec (edgeCount 12)) :=
  missing2620_2622 ++ missing2622_2624
abbrev records2620_2624 : List Blob :=
  records2620_2622 ++ records2622_2624
theorem aligned2620_2624 :
    AlignedValid 12 3 missing2620_2624 records2620_2624 :=
  aligned2620_2622.append aligned2622_2624

def missing2616_2624 : List (BitVec (edgeCount 12)) :=
  missing2616_2620 ++ missing2620_2624
abbrev records2616_2624 : List Blob :=
  records2616_2620 ++ records2620_2624
theorem aligned2616_2624 :
    AlignedValid 12 3 missing2616_2624 records2616_2624 :=
  aligned2616_2620.append aligned2620_2624

def missing2608_2624 : List (BitVec (edgeCount 12)) :=
  missing2608_2616 ++ missing2616_2624
abbrev records2608_2624 : List Blob :=
  records2608_2616 ++ records2616_2624
theorem aligned2608_2624 :
    AlignedValid 12 3 missing2608_2624 records2608_2624 :=
  aligned2608_2616.append aligned2616_2624

def missing2592_2624 : List (BitVec (edgeCount 12)) :=
  missing2592_2608 ++ missing2608_2624
abbrev records2592_2624 : List Blob :=
  records2592_2608 ++ records2608_2624
theorem aligned2592_2624 :
    AlignedValid 12 3 missing2592_2624 records2592_2624 :=
  aligned2592_2608.append aligned2608_2624

def missing2560_2624 : List (BitVec (edgeCount 12)) :=
  missing2560_2592 ++ missing2592_2624
abbrev records2560_2624 : List Blob :=
  records2560_2592 ++ records2592_2624
theorem aligned2560_2624 :
    AlignedValid 12 3 missing2560_2624 records2560_2624 :=
  aligned2560_2592.append aligned2592_2624

def missing2624_2625 : List (BitVec (edgeCount 12)) :=
  [missing2624]
abbrev records2624_2625 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2624]
theorem aligned2624_2625 :
    AlignedValid 12 3 missing2624_2625 records2624_2625 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2624
    maskCheck2624 AlignedValid.nil

def missing2625_2626 : List (BitVec (edgeCount 12)) :=
  [missing2625]
abbrev records2625_2626 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2625]
theorem aligned2625_2626 :
    AlignedValid 12 3 missing2625_2626 records2625_2626 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2625
    maskCheck2625 AlignedValid.nil

def missing2624_2626 : List (BitVec (edgeCount 12)) :=
  missing2624_2625 ++ missing2625_2626
abbrev records2624_2626 : List Blob :=
  records2624_2625 ++ records2625_2626
theorem aligned2624_2626 :
    AlignedValid 12 3 missing2624_2626 records2624_2626 :=
  aligned2624_2625.append aligned2625_2626

def missing2626_2627 : List (BitVec (edgeCount 12)) :=
  [missing2626]
abbrev records2626_2627 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2626]
theorem aligned2626_2627 :
    AlignedValid 12 3 missing2626_2627 records2626_2627 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2626
    maskCheck2626 AlignedValid.nil

def missing2627_2628 : List (BitVec (edgeCount 12)) :=
  [missing2627]
abbrev records2627_2628 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2627]
theorem aligned2627_2628 :
    AlignedValid 12 3 missing2627_2628 records2627_2628 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2627
    maskCheck2627 AlignedValid.nil

def missing2626_2628 : List (BitVec (edgeCount 12)) :=
  missing2626_2627 ++ missing2627_2628
abbrev records2626_2628 : List Blob :=
  records2626_2627 ++ records2627_2628
theorem aligned2626_2628 :
    AlignedValid 12 3 missing2626_2628 records2626_2628 :=
  aligned2626_2627.append aligned2627_2628

def missing2624_2628 : List (BitVec (edgeCount 12)) :=
  missing2624_2626 ++ missing2626_2628
abbrev records2624_2628 : List Blob :=
  records2624_2626 ++ records2626_2628
theorem aligned2624_2628 :
    AlignedValid 12 3 missing2624_2628 records2624_2628 :=
  aligned2624_2626.append aligned2626_2628

def missing2628_2629 : List (BitVec (edgeCount 12)) :=
  [missing2628]
abbrev records2628_2629 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2628]
theorem aligned2628_2629 :
    AlignedValid 12 3 missing2628_2629 records2628_2629 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2628
    maskCheck2628 AlignedValid.nil

def missing2629_2630 : List (BitVec (edgeCount 12)) :=
  [missing2629]
abbrev records2629_2630 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2629]
theorem aligned2629_2630 :
    AlignedValid 12 3 missing2629_2630 records2629_2630 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2629
    maskCheck2629 AlignedValid.nil

def missing2628_2630 : List (BitVec (edgeCount 12)) :=
  missing2628_2629 ++ missing2629_2630
abbrev records2628_2630 : List Blob :=
  records2628_2629 ++ records2629_2630
theorem aligned2628_2630 :
    AlignedValid 12 3 missing2628_2630 records2628_2630 :=
  aligned2628_2629.append aligned2629_2630

def missing2630_2631 : List (BitVec (edgeCount 12)) :=
  [missing2630]
abbrev records2630_2631 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2630]
theorem aligned2630_2631 :
    AlignedValid 12 3 missing2630_2631 records2630_2631 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2630
    maskCheck2630 AlignedValid.nil

def missing2631_2632 : List (BitVec (edgeCount 12)) :=
  [missing2631]
abbrev records2631_2632 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2631]
theorem aligned2631_2632 :
    AlignedValid 12 3 missing2631_2632 records2631_2632 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2631
    maskCheck2631 AlignedValid.nil

def missing2630_2632 : List (BitVec (edgeCount 12)) :=
  missing2630_2631 ++ missing2631_2632
abbrev records2630_2632 : List Blob :=
  records2630_2631 ++ records2631_2632
theorem aligned2630_2632 :
    AlignedValid 12 3 missing2630_2632 records2630_2632 :=
  aligned2630_2631.append aligned2631_2632

def missing2628_2632 : List (BitVec (edgeCount 12)) :=
  missing2628_2630 ++ missing2630_2632
abbrev records2628_2632 : List Blob :=
  records2628_2630 ++ records2630_2632
theorem aligned2628_2632 :
    AlignedValid 12 3 missing2628_2632 records2628_2632 :=
  aligned2628_2630.append aligned2630_2632

def missing2624_2632 : List (BitVec (edgeCount 12)) :=
  missing2624_2628 ++ missing2628_2632
abbrev records2624_2632 : List Blob :=
  records2624_2628 ++ records2628_2632
theorem aligned2624_2632 :
    AlignedValid 12 3 missing2624_2632 records2624_2632 :=
  aligned2624_2628.append aligned2628_2632

def missing2632_2633 : List (BitVec (edgeCount 12)) :=
  [missing2632]
abbrev records2632_2633 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2632]
theorem aligned2632_2633 :
    AlignedValid 12 3 missing2632_2633 records2632_2633 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2632
    maskCheck2632 AlignedValid.nil

def missing2633_2634 : List (BitVec (edgeCount 12)) :=
  [missing2633]
abbrev records2633_2634 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2633]
theorem aligned2633_2634 :
    AlignedValid 12 3 missing2633_2634 records2633_2634 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2633
    maskCheck2633 AlignedValid.nil

def missing2632_2634 : List (BitVec (edgeCount 12)) :=
  missing2632_2633 ++ missing2633_2634
abbrev records2632_2634 : List Blob :=
  records2632_2633 ++ records2633_2634
theorem aligned2632_2634 :
    AlignedValid 12 3 missing2632_2634 records2632_2634 :=
  aligned2632_2633.append aligned2633_2634

def missing2634_2635 : List (BitVec (edgeCount 12)) :=
  [missing2634]
abbrev records2634_2635 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2634]
theorem aligned2634_2635 :
    AlignedValid 12 3 missing2634_2635 records2634_2635 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2634
    maskCheck2634 AlignedValid.nil

def missing2635_2636 : List (BitVec (edgeCount 12)) :=
  [missing2635]
abbrev records2635_2636 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2635]
theorem aligned2635_2636 :
    AlignedValid 12 3 missing2635_2636 records2635_2636 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2635
    maskCheck2635 AlignedValid.nil

def missing2634_2636 : List (BitVec (edgeCount 12)) :=
  missing2634_2635 ++ missing2635_2636
abbrev records2634_2636 : List Blob :=
  records2634_2635 ++ records2635_2636
theorem aligned2634_2636 :
    AlignedValid 12 3 missing2634_2636 records2634_2636 :=
  aligned2634_2635.append aligned2635_2636

def missing2632_2636 : List (BitVec (edgeCount 12)) :=
  missing2632_2634 ++ missing2634_2636
abbrev records2632_2636 : List Blob :=
  records2632_2634 ++ records2634_2636
theorem aligned2632_2636 :
    AlignedValid 12 3 missing2632_2636 records2632_2636 :=
  aligned2632_2634.append aligned2634_2636

def missing2636_2637 : List (BitVec (edgeCount 12)) :=
  [missing2636]
abbrev records2636_2637 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2636]
theorem aligned2636_2637 :
    AlignedValid 12 3 missing2636_2637 records2636_2637 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2636
    maskCheck2636 AlignedValid.nil

def missing2637_2638 : List (BitVec (edgeCount 12)) :=
  [missing2637]
abbrev records2637_2638 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2637]
theorem aligned2637_2638 :
    AlignedValid 12 3 missing2637_2638 records2637_2638 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2637
    maskCheck2637 AlignedValid.nil

def missing2636_2638 : List (BitVec (edgeCount 12)) :=
  missing2636_2637 ++ missing2637_2638
abbrev records2636_2638 : List Blob :=
  records2636_2637 ++ records2637_2638
theorem aligned2636_2638 :
    AlignedValid 12 3 missing2636_2638 records2636_2638 :=
  aligned2636_2637.append aligned2637_2638

def missing2638_2639 : List (BitVec (edgeCount 12)) :=
  [missing2638]
abbrev records2638_2639 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2638]
theorem aligned2638_2639 :
    AlignedValid 12 3 missing2638_2639 records2638_2639 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2638
    maskCheck2638 AlignedValid.nil

def missing2639_2640 : List (BitVec (edgeCount 12)) :=
  [missing2639]
abbrev records2639_2640 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2639]
theorem aligned2639_2640 :
    AlignedValid 12 3 missing2639_2640 records2639_2640 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2639
    maskCheck2639 AlignedValid.nil

def missing2638_2640 : List (BitVec (edgeCount 12)) :=
  missing2638_2639 ++ missing2639_2640
abbrev records2638_2640 : List Blob :=
  records2638_2639 ++ records2639_2640
theorem aligned2638_2640 :
    AlignedValid 12 3 missing2638_2640 records2638_2640 :=
  aligned2638_2639.append aligned2639_2640

def missing2636_2640 : List (BitVec (edgeCount 12)) :=
  missing2636_2638 ++ missing2638_2640
abbrev records2636_2640 : List Blob :=
  records2636_2638 ++ records2638_2640
theorem aligned2636_2640 :
    AlignedValid 12 3 missing2636_2640 records2636_2640 :=
  aligned2636_2638.append aligned2638_2640

def missing2632_2640 : List (BitVec (edgeCount 12)) :=
  missing2632_2636 ++ missing2636_2640
abbrev records2632_2640 : List Blob :=
  records2632_2636 ++ records2636_2640
theorem aligned2632_2640 :
    AlignedValid 12 3 missing2632_2640 records2632_2640 :=
  aligned2632_2636.append aligned2636_2640

def missing2624_2640 : List (BitVec (edgeCount 12)) :=
  missing2624_2632 ++ missing2632_2640
abbrev records2624_2640 : List Blob :=
  records2624_2632 ++ records2632_2640
theorem aligned2624_2640 :
    AlignedValid 12 3 missing2624_2640 records2624_2640 :=
  aligned2624_2632.append aligned2632_2640

def missing2640_2641 : List (BitVec (edgeCount 12)) :=
  [missing2640]
abbrev records2640_2641 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2640]
theorem aligned2640_2641 :
    AlignedValid 12 3 missing2640_2641 records2640_2641 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2640
    maskCheck2640 AlignedValid.nil

def missing2641_2642 : List (BitVec (edgeCount 12)) :=
  [missing2641]
abbrev records2641_2642 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2641]
theorem aligned2641_2642 :
    AlignedValid 12 3 missing2641_2642 records2641_2642 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2641
    maskCheck2641 AlignedValid.nil

def missing2640_2642 : List (BitVec (edgeCount 12)) :=
  missing2640_2641 ++ missing2641_2642
abbrev records2640_2642 : List Blob :=
  records2640_2641 ++ records2641_2642
theorem aligned2640_2642 :
    AlignedValid 12 3 missing2640_2642 records2640_2642 :=
  aligned2640_2641.append aligned2641_2642

def missing2642_2643 : List (BitVec (edgeCount 12)) :=
  [missing2642]
abbrev records2642_2643 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2642]
theorem aligned2642_2643 :
    AlignedValid 12 3 missing2642_2643 records2642_2643 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2642
    maskCheck2642 AlignedValid.nil

def missing2643_2644 : List (BitVec (edgeCount 12)) :=
  [missing2643]
abbrev records2643_2644 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2643]
theorem aligned2643_2644 :
    AlignedValid 12 3 missing2643_2644 records2643_2644 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2643
    maskCheck2643 AlignedValid.nil

def missing2642_2644 : List (BitVec (edgeCount 12)) :=
  missing2642_2643 ++ missing2643_2644
abbrev records2642_2644 : List Blob :=
  records2642_2643 ++ records2643_2644
theorem aligned2642_2644 :
    AlignedValid 12 3 missing2642_2644 records2642_2644 :=
  aligned2642_2643.append aligned2643_2644

def missing2640_2644 : List (BitVec (edgeCount 12)) :=
  missing2640_2642 ++ missing2642_2644
abbrev records2640_2644 : List Blob :=
  records2640_2642 ++ records2642_2644
theorem aligned2640_2644 :
    AlignedValid 12 3 missing2640_2644 records2640_2644 :=
  aligned2640_2642.append aligned2642_2644

def missing2644_2645 : List (BitVec (edgeCount 12)) :=
  [missing2644]
abbrev records2644_2645 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2644]
theorem aligned2644_2645 :
    AlignedValid 12 3 missing2644_2645 records2644_2645 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2644
    maskCheck2644 AlignedValid.nil

def missing2645_2646 : List (BitVec (edgeCount 12)) :=
  [missing2645]
abbrev records2645_2646 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2645]
theorem aligned2645_2646 :
    AlignedValid 12 3 missing2645_2646 records2645_2646 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2645
    maskCheck2645 AlignedValid.nil

def missing2644_2646 : List (BitVec (edgeCount 12)) :=
  missing2644_2645 ++ missing2645_2646
abbrev records2644_2646 : List Blob :=
  records2644_2645 ++ records2645_2646
theorem aligned2644_2646 :
    AlignedValid 12 3 missing2644_2646 records2644_2646 :=
  aligned2644_2645.append aligned2645_2646

def missing2646_2647 : List (BitVec (edgeCount 12)) :=
  [missing2646]
abbrev records2646_2647 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2646]
theorem aligned2646_2647 :
    AlignedValid 12 3 missing2646_2647 records2646_2647 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2646
    maskCheck2646 AlignedValid.nil

def missing2647_2648 : List (BitVec (edgeCount 12)) :=
  [missing2647]
abbrev records2647_2648 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2647]
theorem aligned2647_2648 :
    AlignedValid 12 3 missing2647_2648 records2647_2648 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2647
    maskCheck2647 AlignedValid.nil

def missing2646_2648 : List (BitVec (edgeCount 12)) :=
  missing2646_2647 ++ missing2647_2648
abbrev records2646_2648 : List Blob :=
  records2646_2647 ++ records2647_2648
theorem aligned2646_2648 :
    AlignedValid 12 3 missing2646_2648 records2646_2648 :=
  aligned2646_2647.append aligned2647_2648

def missing2644_2648 : List (BitVec (edgeCount 12)) :=
  missing2644_2646 ++ missing2646_2648
abbrev records2644_2648 : List Blob :=
  records2644_2646 ++ records2646_2648
theorem aligned2644_2648 :
    AlignedValid 12 3 missing2644_2648 records2644_2648 :=
  aligned2644_2646.append aligned2646_2648

def missing2640_2648 : List (BitVec (edgeCount 12)) :=
  missing2640_2644 ++ missing2644_2648
abbrev records2640_2648 : List Blob :=
  records2640_2644 ++ records2644_2648
theorem aligned2640_2648 :
    AlignedValid 12 3 missing2640_2648 records2640_2648 :=
  aligned2640_2644.append aligned2644_2648

def missing2648_2649 : List (BitVec (edgeCount 12)) :=
  [missing2648]
abbrev records2648_2649 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2648]
theorem aligned2648_2649 :
    AlignedValid 12 3 missing2648_2649 records2648_2649 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2648
    maskCheck2648 AlignedValid.nil

def missing2649_2650 : List (BitVec (edgeCount 12)) :=
  [missing2649]
abbrev records2649_2650 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2649]
theorem aligned2649_2650 :
    AlignedValid 12 3 missing2649_2650 records2649_2650 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2649
    maskCheck2649 AlignedValid.nil

def missing2648_2650 : List (BitVec (edgeCount 12)) :=
  missing2648_2649 ++ missing2649_2650
abbrev records2648_2650 : List Blob :=
  records2648_2649 ++ records2649_2650
theorem aligned2648_2650 :
    AlignedValid 12 3 missing2648_2650 records2648_2650 :=
  aligned2648_2649.append aligned2649_2650

def missing2650_2651 : List (BitVec (edgeCount 12)) :=
  [missing2650]
abbrev records2650_2651 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2650]
theorem aligned2650_2651 :
    AlignedValid 12 3 missing2650_2651 records2650_2651 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2650
    maskCheck2650 AlignedValid.nil

def missing2651_2652 : List (BitVec (edgeCount 12)) :=
  [missing2651]
abbrev records2651_2652 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2651]
theorem aligned2651_2652 :
    AlignedValid 12 3 missing2651_2652 records2651_2652 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2651
    maskCheck2651 AlignedValid.nil

def missing2650_2652 : List (BitVec (edgeCount 12)) :=
  missing2650_2651 ++ missing2651_2652
abbrev records2650_2652 : List Blob :=
  records2650_2651 ++ records2651_2652
theorem aligned2650_2652 :
    AlignedValid 12 3 missing2650_2652 records2650_2652 :=
  aligned2650_2651.append aligned2651_2652

def missing2648_2652 : List (BitVec (edgeCount 12)) :=
  missing2648_2650 ++ missing2650_2652
abbrev records2648_2652 : List Blob :=
  records2648_2650 ++ records2650_2652
theorem aligned2648_2652 :
    AlignedValid 12 3 missing2648_2652 records2648_2652 :=
  aligned2648_2650.append aligned2650_2652

def missing2652_2653 : List (BitVec (edgeCount 12)) :=
  [missing2652]
abbrev records2652_2653 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2652]
theorem aligned2652_2653 :
    AlignedValid 12 3 missing2652_2653 records2652_2653 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2652
    maskCheck2652 AlignedValid.nil

def missing2653_2654 : List (BitVec (edgeCount 12)) :=
  [missing2653]
abbrev records2653_2654 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2653]
theorem aligned2653_2654 :
    AlignedValid 12 3 missing2653_2654 records2653_2654 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2653
    maskCheck2653 AlignedValid.nil

def missing2652_2654 : List (BitVec (edgeCount 12)) :=
  missing2652_2653 ++ missing2653_2654
abbrev records2652_2654 : List Blob :=
  records2652_2653 ++ records2653_2654
theorem aligned2652_2654 :
    AlignedValid 12 3 missing2652_2654 records2652_2654 :=
  aligned2652_2653.append aligned2653_2654

def missing2654_2655 : List (BitVec (edgeCount 12)) :=
  [missing2654]
abbrev records2654_2655 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2654]
theorem aligned2654_2655 :
    AlignedValid 12 3 missing2654_2655 records2654_2655 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2654
    maskCheck2654 AlignedValid.nil

def missing2655_2656 : List (BitVec (edgeCount 12)) :=
  [missing2655]
abbrev records2655_2656 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2655]
theorem aligned2655_2656 :
    AlignedValid 12 3 missing2655_2656 records2655_2656 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2655
    maskCheck2655 AlignedValid.nil

def missing2654_2656 : List (BitVec (edgeCount 12)) :=
  missing2654_2655 ++ missing2655_2656
abbrev records2654_2656 : List Blob :=
  records2654_2655 ++ records2655_2656
theorem aligned2654_2656 :
    AlignedValid 12 3 missing2654_2656 records2654_2656 :=
  aligned2654_2655.append aligned2655_2656

def missing2652_2656 : List (BitVec (edgeCount 12)) :=
  missing2652_2654 ++ missing2654_2656
abbrev records2652_2656 : List Blob :=
  records2652_2654 ++ records2654_2656
theorem aligned2652_2656 :
    AlignedValid 12 3 missing2652_2656 records2652_2656 :=
  aligned2652_2654.append aligned2654_2656

def missing2648_2656 : List (BitVec (edgeCount 12)) :=
  missing2648_2652 ++ missing2652_2656
abbrev records2648_2656 : List Blob :=
  records2648_2652 ++ records2652_2656
theorem aligned2648_2656 :
    AlignedValid 12 3 missing2648_2656 records2648_2656 :=
  aligned2648_2652.append aligned2652_2656

def missing2640_2656 : List (BitVec (edgeCount 12)) :=
  missing2640_2648 ++ missing2648_2656
abbrev records2640_2656 : List Blob :=
  records2640_2648 ++ records2648_2656
theorem aligned2640_2656 :
    AlignedValid 12 3 missing2640_2656 records2640_2656 :=
  aligned2640_2648.append aligned2648_2656

def missing2624_2656 : List (BitVec (edgeCount 12)) :=
  missing2624_2640 ++ missing2640_2656
abbrev records2624_2656 : List Blob :=
  records2624_2640 ++ records2640_2656
theorem aligned2624_2656 :
    AlignedValid 12 3 missing2624_2656 records2624_2656 :=
  aligned2624_2640.append aligned2640_2656

def missing2656_2657 : List (BitVec (edgeCount 12)) :=
  [missing2656]
abbrev records2656_2657 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2656]
theorem aligned2656_2657 :
    AlignedValid 12 3 missing2656_2657 records2656_2657 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2656
    maskCheck2656 AlignedValid.nil

def missing2657_2658 : List (BitVec (edgeCount 12)) :=
  [missing2657]
abbrev records2657_2658 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2657]
theorem aligned2657_2658 :
    AlignedValid 12 3 missing2657_2658 records2657_2658 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2657
    maskCheck2657 AlignedValid.nil

def missing2656_2658 : List (BitVec (edgeCount 12)) :=
  missing2656_2657 ++ missing2657_2658
abbrev records2656_2658 : List Blob :=
  records2656_2657 ++ records2657_2658
theorem aligned2656_2658 :
    AlignedValid 12 3 missing2656_2658 records2656_2658 :=
  aligned2656_2657.append aligned2657_2658

def missing2658_2659 : List (BitVec (edgeCount 12)) :=
  [missing2658]
abbrev records2658_2659 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2658]
theorem aligned2658_2659 :
    AlignedValid 12 3 missing2658_2659 records2658_2659 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2658
    maskCheck2658 AlignedValid.nil

def missing2659_2660 : List (BitVec (edgeCount 12)) :=
  [missing2659]
abbrev records2659_2660 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2659]
theorem aligned2659_2660 :
    AlignedValid 12 3 missing2659_2660 records2659_2660 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2659
    maskCheck2659 AlignedValid.nil

def missing2658_2660 : List (BitVec (edgeCount 12)) :=
  missing2658_2659 ++ missing2659_2660
abbrev records2658_2660 : List Blob :=
  records2658_2659 ++ records2659_2660
theorem aligned2658_2660 :
    AlignedValid 12 3 missing2658_2660 records2658_2660 :=
  aligned2658_2659.append aligned2659_2660

def missing2656_2660 : List (BitVec (edgeCount 12)) :=
  missing2656_2658 ++ missing2658_2660
abbrev records2656_2660 : List Blob :=
  records2656_2658 ++ records2658_2660
theorem aligned2656_2660 :
    AlignedValid 12 3 missing2656_2660 records2656_2660 :=
  aligned2656_2658.append aligned2658_2660

def missing2660_2661 : List (BitVec (edgeCount 12)) :=
  [missing2660]
abbrev records2660_2661 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2660]
theorem aligned2660_2661 :
    AlignedValid 12 3 missing2660_2661 records2660_2661 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2660
    maskCheck2660 AlignedValid.nil

def missing2661_2662 : List (BitVec (edgeCount 12)) :=
  [missing2661]
abbrev records2661_2662 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2661]
theorem aligned2661_2662 :
    AlignedValid 12 3 missing2661_2662 records2661_2662 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2661
    maskCheck2661 AlignedValid.nil

def missing2660_2662 : List (BitVec (edgeCount 12)) :=
  missing2660_2661 ++ missing2661_2662
abbrev records2660_2662 : List Blob :=
  records2660_2661 ++ records2661_2662
theorem aligned2660_2662 :
    AlignedValid 12 3 missing2660_2662 records2660_2662 :=
  aligned2660_2661.append aligned2661_2662

def missing2662_2663 : List (BitVec (edgeCount 12)) :=
  [missing2662]
abbrev records2662_2663 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2662]
theorem aligned2662_2663 :
    AlignedValid 12 3 missing2662_2663 records2662_2663 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2662
    maskCheck2662 AlignedValid.nil

def missing2663_2664 : List (BitVec (edgeCount 12)) :=
  [missing2663]
abbrev records2663_2664 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2663]
theorem aligned2663_2664 :
    AlignedValid 12 3 missing2663_2664 records2663_2664 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2663
    maskCheck2663 AlignedValid.nil

def missing2662_2664 : List (BitVec (edgeCount 12)) :=
  missing2662_2663 ++ missing2663_2664
abbrev records2662_2664 : List Blob :=
  records2662_2663 ++ records2663_2664
theorem aligned2662_2664 :
    AlignedValid 12 3 missing2662_2664 records2662_2664 :=
  aligned2662_2663.append aligned2663_2664

def missing2660_2664 : List (BitVec (edgeCount 12)) :=
  missing2660_2662 ++ missing2662_2664
abbrev records2660_2664 : List Blob :=
  records2660_2662 ++ records2662_2664
theorem aligned2660_2664 :
    AlignedValid 12 3 missing2660_2664 records2660_2664 :=
  aligned2660_2662.append aligned2662_2664

def missing2656_2664 : List (BitVec (edgeCount 12)) :=
  missing2656_2660 ++ missing2660_2664
abbrev records2656_2664 : List Blob :=
  records2656_2660 ++ records2660_2664
theorem aligned2656_2664 :
    AlignedValid 12 3 missing2656_2664 records2656_2664 :=
  aligned2656_2660.append aligned2660_2664

def missing2664_2665 : List (BitVec (edgeCount 12)) :=
  [missing2664]
abbrev records2664_2665 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2664]
theorem aligned2664_2665 :
    AlignedValid 12 3 missing2664_2665 records2664_2665 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2664
    maskCheck2664 AlignedValid.nil

def missing2665_2666 : List (BitVec (edgeCount 12)) :=
  [missing2665]
abbrev records2665_2666 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2665]
theorem aligned2665_2666 :
    AlignedValid 12 3 missing2665_2666 records2665_2666 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2665
    maskCheck2665 AlignedValid.nil

def missing2664_2666 : List (BitVec (edgeCount 12)) :=
  missing2664_2665 ++ missing2665_2666
abbrev records2664_2666 : List Blob :=
  records2664_2665 ++ records2665_2666
theorem aligned2664_2666 :
    AlignedValid 12 3 missing2664_2666 records2664_2666 :=
  aligned2664_2665.append aligned2665_2666

def missing2666_2667 : List (BitVec (edgeCount 12)) :=
  [missing2666]
abbrev records2666_2667 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2666]
theorem aligned2666_2667 :
    AlignedValid 12 3 missing2666_2667 records2666_2667 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2666
    maskCheck2666 AlignedValid.nil

def missing2667_2668 : List (BitVec (edgeCount 12)) :=
  [missing2667]
abbrev records2667_2668 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2667]
theorem aligned2667_2668 :
    AlignedValid 12 3 missing2667_2668 records2667_2668 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2667
    maskCheck2667 AlignedValid.nil

def missing2666_2668 : List (BitVec (edgeCount 12)) :=
  missing2666_2667 ++ missing2667_2668
abbrev records2666_2668 : List Blob :=
  records2666_2667 ++ records2667_2668
theorem aligned2666_2668 :
    AlignedValid 12 3 missing2666_2668 records2666_2668 :=
  aligned2666_2667.append aligned2667_2668

def missing2664_2668 : List (BitVec (edgeCount 12)) :=
  missing2664_2666 ++ missing2666_2668
abbrev records2664_2668 : List Blob :=
  records2664_2666 ++ records2666_2668
theorem aligned2664_2668 :
    AlignedValid 12 3 missing2664_2668 records2664_2668 :=
  aligned2664_2666.append aligned2666_2668

def missing2668_2669 : List (BitVec (edgeCount 12)) :=
  [missing2668]
abbrev records2668_2669 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2668]
theorem aligned2668_2669 :
    AlignedValid 12 3 missing2668_2669 records2668_2669 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2668
    maskCheck2668 AlignedValid.nil

def missing2669_2670 : List (BitVec (edgeCount 12)) :=
  [missing2669]
abbrev records2669_2670 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2669]
theorem aligned2669_2670 :
    AlignedValid 12 3 missing2669_2670 records2669_2670 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2669
    maskCheck2669 AlignedValid.nil

def missing2668_2670 : List (BitVec (edgeCount 12)) :=
  missing2668_2669 ++ missing2669_2670
abbrev records2668_2670 : List Blob :=
  records2668_2669 ++ records2669_2670
theorem aligned2668_2670 :
    AlignedValid 12 3 missing2668_2670 records2668_2670 :=
  aligned2668_2669.append aligned2669_2670

def missing2670_2671 : List (BitVec (edgeCount 12)) :=
  [missing2670]
abbrev records2670_2671 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2670]
theorem aligned2670_2671 :
    AlignedValid 12 3 missing2670_2671 records2670_2671 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2670
    maskCheck2670 AlignedValid.nil

def missing2671_2672 : List (BitVec (edgeCount 12)) :=
  [missing2671]
abbrev records2671_2672 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2671]
theorem aligned2671_2672 :
    AlignedValid 12 3 missing2671_2672 records2671_2672 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2671
    maskCheck2671 AlignedValid.nil

def missing2670_2672 : List (BitVec (edgeCount 12)) :=
  missing2670_2671 ++ missing2671_2672
abbrev records2670_2672 : List Blob :=
  records2670_2671 ++ records2671_2672
theorem aligned2670_2672 :
    AlignedValid 12 3 missing2670_2672 records2670_2672 :=
  aligned2670_2671.append aligned2671_2672

def missing2668_2672 : List (BitVec (edgeCount 12)) :=
  missing2668_2670 ++ missing2670_2672
abbrev records2668_2672 : List Blob :=
  records2668_2670 ++ records2670_2672
theorem aligned2668_2672 :
    AlignedValid 12 3 missing2668_2672 records2668_2672 :=
  aligned2668_2670.append aligned2670_2672

def missing2664_2672 : List (BitVec (edgeCount 12)) :=
  missing2664_2668 ++ missing2668_2672
abbrev records2664_2672 : List Blob :=
  records2664_2668 ++ records2668_2672
theorem aligned2664_2672 :
    AlignedValid 12 3 missing2664_2672 records2664_2672 :=
  aligned2664_2668.append aligned2668_2672

def missing2656_2672 : List (BitVec (edgeCount 12)) :=
  missing2656_2664 ++ missing2664_2672
abbrev records2656_2672 : List Blob :=
  records2656_2664 ++ records2664_2672
theorem aligned2656_2672 :
    AlignedValid 12 3 missing2656_2672 records2656_2672 :=
  aligned2656_2664.append aligned2664_2672

def missing2672_2673 : List (BitVec (edgeCount 12)) :=
  [missing2672]
abbrev records2672_2673 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2672]
theorem aligned2672_2673 :
    AlignedValid 12 3 missing2672_2673 records2672_2673 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2672
    maskCheck2672 AlignedValid.nil

def missing2673_2674 : List (BitVec (edgeCount 12)) :=
  [missing2673]
abbrev records2673_2674 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2673]
theorem aligned2673_2674 :
    AlignedValid 12 3 missing2673_2674 records2673_2674 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2673
    maskCheck2673 AlignedValid.nil

def missing2672_2674 : List (BitVec (edgeCount 12)) :=
  missing2672_2673 ++ missing2673_2674
abbrev records2672_2674 : List Blob :=
  records2672_2673 ++ records2673_2674
theorem aligned2672_2674 :
    AlignedValid 12 3 missing2672_2674 records2672_2674 :=
  aligned2672_2673.append aligned2673_2674

def missing2674_2675 : List (BitVec (edgeCount 12)) :=
  [missing2674]
abbrev records2674_2675 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2674]
theorem aligned2674_2675 :
    AlignedValid 12 3 missing2674_2675 records2674_2675 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2674
    maskCheck2674 AlignedValid.nil

def missing2675_2676 : List (BitVec (edgeCount 12)) :=
  [missing2675]
abbrev records2675_2676 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2675]
theorem aligned2675_2676 :
    AlignedValid 12 3 missing2675_2676 records2675_2676 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2675
    maskCheck2675 AlignedValid.nil

def missing2674_2676 : List (BitVec (edgeCount 12)) :=
  missing2674_2675 ++ missing2675_2676
abbrev records2674_2676 : List Blob :=
  records2674_2675 ++ records2675_2676
theorem aligned2674_2676 :
    AlignedValid 12 3 missing2674_2676 records2674_2676 :=
  aligned2674_2675.append aligned2675_2676

def missing2672_2676 : List (BitVec (edgeCount 12)) :=
  missing2672_2674 ++ missing2674_2676
abbrev records2672_2676 : List Blob :=
  records2672_2674 ++ records2674_2676
theorem aligned2672_2676 :
    AlignedValid 12 3 missing2672_2676 records2672_2676 :=
  aligned2672_2674.append aligned2674_2676

def missing2676_2677 : List (BitVec (edgeCount 12)) :=
  [missing2676]
abbrev records2676_2677 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2676]
theorem aligned2676_2677 :
    AlignedValid 12 3 missing2676_2677 records2676_2677 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2676
    maskCheck2676 AlignedValid.nil

def missing2677_2678 : List (BitVec (edgeCount 12)) :=
  [missing2677]
abbrev records2677_2678 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2677]
theorem aligned2677_2678 :
    AlignedValid 12 3 missing2677_2678 records2677_2678 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2677
    maskCheck2677 AlignedValid.nil

def missing2676_2678 : List (BitVec (edgeCount 12)) :=
  missing2676_2677 ++ missing2677_2678
abbrev records2676_2678 : List Blob :=
  records2676_2677 ++ records2677_2678
theorem aligned2676_2678 :
    AlignedValid 12 3 missing2676_2678 records2676_2678 :=
  aligned2676_2677.append aligned2677_2678

def missing2678_2679 : List (BitVec (edgeCount 12)) :=
  [missing2678]
abbrev records2678_2679 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2678]
theorem aligned2678_2679 :
    AlignedValid 12 3 missing2678_2679 records2678_2679 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2678
    maskCheck2678 AlignedValid.nil

def missing2679_2680 : List (BitVec (edgeCount 12)) :=
  [missing2679]
abbrev records2679_2680 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2679]
theorem aligned2679_2680 :
    AlignedValid 12 3 missing2679_2680 records2679_2680 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2679
    maskCheck2679 AlignedValid.nil

def missing2678_2680 : List (BitVec (edgeCount 12)) :=
  missing2678_2679 ++ missing2679_2680
abbrev records2678_2680 : List Blob :=
  records2678_2679 ++ records2679_2680
theorem aligned2678_2680 :
    AlignedValid 12 3 missing2678_2680 records2678_2680 :=
  aligned2678_2679.append aligned2679_2680

def missing2676_2680 : List (BitVec (edgeCount 12)) :=
  missing2676_2678 ++ missing2678_2680
abbrev records2676_2680 : List Blob :=
  records2676_2678 ++ records2678_2680
theorem aligned2676_2680 :
    AlignedValid 12 3 missing2676_2680 records2676_2680 :=
  aligned2676_2678.append aligned2678_2680

def missing2672_2680 : List (BitVec (edgeCount 12)) :=
  missing2672_2676 ++ missing2676_2680
abbrev records2672_2680 : List Blob :=
  records2672_2676 ++ records2676_2680
theorem aligned2672_2680 :
    AlignedValid 12 3 missing2672_2680 records2672_2680 :=
  aligned2672_2676.append aligned2676_2680

def missing2680_2681 : List (BitVec (edgeCount 12)) :=
  [missing2680]
abbrev records2680_2681 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2680]
theorem aligned2680_2681 :
    AlignedValid 12 3 missing2680_2681 records2680_2681 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2680
    maskCheck2680 AlignedValid.nil

def missing2681_2682 : List (BitVec (edgeCount 12)) :=
  [missing2681]
abbrev records2681_2682 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2681]
theorem aligned2681_2682 :
    AlignedValid 12 3 missing2681_2682 records2681_2682 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2681
    maskCheck2681 AlignedValid.nil

def missing2680_2682 : List (BitVec (edgeCount 12)) :=
  missing2680_2681 ++ missing2681_2682
abbrev records2680_2682 : List Blob :=
  records2680_2681 ++ records2681_2682
theorem aligned2680_2682 :
    AlignedValid 12 3 missing2680_2682 records2680_2682 :=
  aligned2680_2681.append aligned2681_2682

def missing2682_2683 : List (BitVec (edgeCount 12)) :=
  [missing2682]
abbrev records2682_2683 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2682]
theorem aligned2682_2683 :
    AlignedValid 12 3 missing2682_2683 records2682_2683 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2682
    maskCheck2682 AlignedValid.nil

def missing2683_2684 : List (BitVec (edgeCount 12)) :=
  [missing2683]
abbrev records2683_2684 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2683]
theorem aligned2683_2684 :
    AlignedValid 12 3 missing2683_2684 records2683_2684 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2683
    maskCheck2683 AlignedValid.nil

def missing2682_2684 : List (BitVec (edgeCount 12)) :=
  missing2682_2683 ++ missing2683_2684
abbrev records2682_2684 : List Blob :=
  records2682_2683 ++ records2683_2684
theorem aligned2682_2684 :
    AlignedValid 12 3 missing2682_2684 records2682_2684 :=
  aligned2682_2683.append aligned2683_2684

def missing2680_2684 : List (BitVec (edgeCount 12)) :=
  missing2680_2682 ++ missing2682_2684
abbrev records2680_2684 : List Blob :=
  records2680_2682 ++ records2682_2684
theorem aligned2680_2684 :
    AlignedValid 12 3 missing2680_2684 records2680_2684 :=
  aligned2680_2682.append aligned2682_2684

def missing2684_2685 : List (BitVec (edgeCount 12)) :=
  [missing2684]
abbrev records2684_2685 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2684]
theorem aligned2684_2685 :
    AlignedValid 12 3 missing2684_2685 records2684_2685 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2684
    maskCheck2684 AlignedValid.nil

def missing2685_2686 : List (BitVec (edgeCount 12)) :=
  [missing2685]
abbrev records2685_2686 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2685]
theorem aligned2685_2686 :
    AlignedValid 12 3 missing2685_2686 records2685_2686 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2685
    maskCheck2685 AlignedValid.nil

def missing2684_2686 : List (BitVec (edgeCount 12)) :=
  missing2684_2685 ++ missing2685_2686
abbrev records2684_2686 : List Blob :=
  records2684_2685 ++ records2685_2686
theorem aligned2684_2686 :
    AlignedValid 12 3 missing2684_2686 records2684_2686 :=
  aligned2684_2685.append aligned2685_2686

def missing2686_2687 : List (BitVec (edgeCount 12)) :=
  [missing2686]
abbrev records2686_2687 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2686]
theorem aligned2686_2687 :
    AlignedValid 12 3 missing2686_2687 records2686_2687 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2686
    maskCheck2686 AlignedValid.nil

def missing2687_2688 : List (BitVec (edgeCount 12)) :=
  [missing2687]
abbrev records2687_2688 : List Blob :=
  [StrongPackedBucketN12A3Shard020.record2687]
theorem aligned2687_2688 :
    AlignedValid 12 3 missing2687_2688 records2687_2688 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard020.check2687
    maskCheck2687 AlignedValid.nil

def missing2686_2688 : List (BitVec (edgeCount 12)) :=
  missing2686_2687 ++ missing2687_2688
abbrev records2686_2688 : List Blob :=
  records2686_2687 ++ records2687_2688
theorem aligned2686_2688 :
    AlignedValid 12 3 missing2686_2688 records2686_2688 :=
  aligned2686_2687.append aligned2687_2688

def missing2684_2688 : List (BitVec (edgeCount 12)) :=
  missing2684_2686 ++ missing2686_2688
abbrev records2684_2688 : List Blob :=
  records2684_2686 ++ records2686_2688
theorem aligned2684_2688 :
    AlignedValid 12 3 missing2684_2688 records2684_2688 :=
  aligned2684_2686.append aligned2686_2688

def missing2680_2688 : List (BitVec (edgeCount 12)) :=
  missing2680_2684 ++ missing2684_2688
abbrev records2680_2688 : List Blob :=
  records2680_2684 ++ records2684_2688
theorem aligned2680_2688 :
    AlignedValid 12 3 missing2680_2688 records2680_2688 :=
  aligned2680_2684.append aligned2684_2688

def missing2672_2688 : List (BitVec (edgeCount 12)) :=
  missing2672_2680 ++ missing2680_2688
abbrev records2672_2688 : List Blob :=
  records2672_2680 ++ records2680_2688
theorem aligned2672_2688 :
    AlignedValid 12 3 missing2672_2688 records2672_2688 :=
  aligned2672_2680.append aligned2680_2688

def missing2656_2688 : List (BitVec (edgeCount 12)) :=
  missing2656_2672 ++ missing2672_2688
abbrev records2656_2688 : List Blob :=
  records2656_2672 ++ records2672_2688
theorem aligned2656_2688 :
    AlignedValid 12 3 missing2656_2688 records2656_2688 :=
  aligned2656_2672.append aligned2672_2688

def missing2624_2688 : List (BitVec (edgeCount 12)) :=
  missing2624_2656 ++ missing2656_2688
abbrev records2624_2688 : List Blob :=
  records2624_2656 ++ records2656_2688
theorem aligned2624_2688 :
    AlignedValid 12 3 missing2624_2688 records2624_2688 :=
  aligned2624_2656.append aligned2656_2688

def missing2560_2688 : List (BitVec (edgeCount 12)) :=
  missing2560_2624 ++ missing2624_2688
abbrev records2560_2688 : List Blob :=
  records2560_2624 ++ records2624_2688
theorem aligned2560_2688 :
    AlignedValid 12 3 missing2560_2688 records2560_2688 :=
  aligned2560_2624.append aligned2624_2688

abbrev missing : List (BitVec (edgeCount 12)) := missing2560_2688
abbrev records : List Blob := records2560_2688
theorem aligned : AlignedValid 12 3 missing records := aligned2560_2688

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A3AlignedShard020
