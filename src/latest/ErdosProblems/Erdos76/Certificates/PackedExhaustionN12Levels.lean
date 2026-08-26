/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedExhaustion

/-! Balanced representative levels for the n=12 packed exhaustion. -/
namespace Erdos76.CertificateExhaustion.Certificates.PackedExhaustionN12

open CertificateChecker
open Packed

def level0MaskAt (i : ℕ) : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 0

def level0 : Level 12 := ⟨1, level0MaskAt⟩

def level1MaskAt (i : ℕ) : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 36028797018963968

def level1 : Level 12 := ⟨1, level1MaskAt⟩

def level2MaskAt (i : ℕ) : BitVec (edgeCount 12) :=
  if i < 1 then
    BitVec.ofNat (edgeCount 12) 108086391056891904
  else
    BitVec.ofNat (edgeCount 12) 72092778410016768

def level2 : Level 12 := ⟨2, level2MaskAt⟩

def level3MaskAt (i : ℕ) : BitVec (edgeCount 12) :=
  if i < 2 then
    if i < 1 then
      BitVec.ofNat (edgeCount 12) 252201579132747776
    else
      BitVec.ofNat (edgeCount 12) 108121575428980736
  else
    if i < 3 then
      BitVec.ofNat (edgeCount 12) 216207966485872640
    else
      if i < 4 then
        BitVec.ofNat (edgeCount 12) 36929552128810156032
      else
        BitVec.ofNat (edgeCount 12) 144185625539510272

def level3 : Level 12 := ⟨5, level3MaskAt⟩

def level4MaskAt (i : ℕ) : BitVec (edgeCount 12) :=
  if i < 5 then
    if i < 2 then
      if i < 1 then
        BitVec.ofNat (edgeCount 12) 540431955284459520
      else
        BitVec.ofNat (edgeCount 12) 252236763504836608
    else
      if i < 3 then
        BitVec.ofNat (edgeCount 12) 504438342637584384
      else
        if i < 4 then
          BitVec.ofNat (edgeCount 12) 37001609722848083968
        else
          BitVec.ofNat (edgeCount 12) 108191944173158400
  else
    if i < 8 then
      if i < 6 then
        BitVec.ofNat (edgeCount 12) 432451117343834112
      else
        if i < 7 then
          BitVec.ofNat (edgeCount 12) 108156828520546304
        else
          BitVec.ofNat (edgeCount 12) 180214422558474240
    else
      if i < 9 then
        BitVec.ofNat (edgeCount 12) 432416001691222016
      else
        if i < 10 then
          BitVec.ofNat (edgeCount 12) 18482843308192169984
        else
          BitVec.ofNat (edgeCount 12) 288371251347456000

def level4 : Level 12 := ⟨11, level4MaskAt⟩

def level5MaskAt (i : ℕ) : BitVec (edgeCount 12) :=
  if i < 13 then
    if i < 6 then
      if i < 3 then
        if i < 1 then
          BitVec.ofNat (edgeCount 12) 1116892707587883008
        else
          if i < 2 then
            BitVec.ofNat (edgeCount 12) 540467139656548352
          else
            BitVec.ofNat (edgeCount 12) 1080899094941007872
      else
        if i < 4 then
          BitVec.ofNat (edgeCount 12) 37145724910923939840
        else
          if i < 5 then
            BitVec.ofNat (edgeCount 12) 252307132249014272
          else
            BitVec.ofNat (edgeCount 12) 468479914362798080
    else
      if i < 9 then
        if i < 7 then
          BitVec.ofNat (edgeCount 12) 1008911869647257600
        else
          if i < 8 then
            BitVec.ofNat (edgeCount 12) 37001680091592261632
          else
            BitVec.ofNat (edgeCount 12) 37073737685630189568
      else
        if i < 11 then
          if i < 10 then
            BitVec.ofNat (edgeCount 12) 37325939264762937344
          else
            BitVec.ofNat (edgeCount 12) 252272016596402176
        else
          if i < 12 then
            BitVec.ofNat (edgeCount 12) 468444798710185984
          else
            BitVec.ofNat (edgeCount 12) 1008876753994645504
  else
    if i < 19 then
      if i < 16 then
        if i < 14 then
          BitVec.ofNat (edgeCount 12) 18554900902230097920
        else
          if i < 15 then
            BitVec.ofNat (edgeCount 12) 18626958496268025856
          else
            BitVec.ofNat (edgeCount 12) 18518907289583222784
      else
        if i < 17 then
          BitVec.ofNat (edgeCount 12) 108297566008901632
        else
          if i < 18 then
            BitVec.ofNat (edgeCount 12) 216383957065793536
          else
            BitVec.ofNat (edgeCount 12) 324470348122685440
    else
      if i < 22 then
        if i < 20 then
          BitVec.ofNat (edgeCount 12) 864902303407144960
        else
          if i < 21 then
            BitVec.ofNat (edgeCount 12) 18482984045680525312
          else
            BitVec.ofNat (edgeCount 12) 108227266252636160
      else
        if i < 24 then
          if i < 23 then
            BitVec.ofNat (edgeCount 12) 324400048366419968
          else
            BitVec.ofNat (edgeCount 12) 864832003650879488
        else
          if i < 25 then
            BitVec.ofNat (edgeCount 12) 9259541709069484032
          else
            BitVec.ofNat (edgeCount 12) 576742502697009152

def level5 : Level 12 := ⟨26, level5MaskAt⟩

def level6MaskAt (i : ℕ) : BitVec (edgeCount 12) :=
  if i < 34 then
    if i < 17 then
      if i < 8 then
        if i < 4 then
          if i < 2 then
            if i < 1 then
              BitVec.ofNat (edgeCount 12) 2269814212194729984
            else
              BitVec.ofNat (edgeCount 12) 1116927891959971840
          else
            if i < 3 then
              BitVec.ofNat (edgeCount 12) 2233820599547854848
            else
              BitVec.ofNat (edgeCount 12) 37433955287075651584
        else
          if i < 6 then
            if i < 5 then
              BitVec.ofNat (edgeCount 12) 540537508400726016
            else
              BitVec.ofNat (edgeCount 12) 1044940666666221568
          else
            if i < 7 then
              BitVec.ofNat (edgeCount 12) 2161833374254104576
            else
              BitVec.ofNat (edgeCount 12) 37145795279668117504
      else
        if i < 12 then
          if i < 10 then
            if i < 9 then
              BitVec.ofNat (edgeCount 12) 37361968061781901312
            else
              BitVec.ofNat (edgeCount 12) 37902400017066360832
          else
            if i < 11 then
              BitVec.ofNat (edgeCount 12) 252447869737369600
            else
              BitVec.ofNat (edgeCount 12) 396563057813225472
        else
          if i < 14 then
            if i < 13 then
              BitVec.ofNat (edgeCount 12) 900966216078721024
            else
              BitVec.ofNat (edgeCount 12) 2017858923666604032
          else
            if i < 15 then
              BitVec.ofNat (edgeCount 12) 540502392748113920
            else
              if i < 16 then
                BitVec.ofNat (edgeCount 12) 1044905551013609472
              else
                BitVec.ofNat (edgeCount 12) 2161798258601492480
    else
      if i < 25 then
        if i < 21 then
          if i < 19 then
            if i < 18 then
              BitVec.ofNat (edgeCount 12) 18699016090305953792
            else
              BitVec.ofNat (edgeCount 12) 18915188872419737600
          else
            if i < 20 then
              BitVec.ofNat (edgeCount 12) 55448389049649201152
            else
              BitVec.ofNat (edgeCount 12) 252307200968491008
        else
          if i < 23 then
            if i < 22 then
              BitVec.ofNat (edgeCount 12) 504508780101238784
            else
              BitVec.ofNat (edgeCount 12) 1008911938366734336
          else
            if i < 24 then
              BitVec.ofNat (edgeCount 12) 18554936086602186752
            else
              BitVec.ofNat (edgeCount 12) 18663022477659078656
      else
        if i < 29 then
          if i < 27 then
            if i < 26 then
              BitVec.ofNat (edgeCount 12) 37001680160311738368
            else
              BitVec.ofNat (edgeCount 12) 37073737754349666304
          else
            if i < 28 then
              BitVec.ofNat (edgeCount 12) 252412754084757504
            else
              BitVec.ofNat (edgeCount 12) 396527942160613376
        else
          if i < 31 then
            if i < 30 then
              BitVec.ofNat (edgeCount 12) 504614333217505280
            else
              BitVec.ofNat (edgeCount 12) 900931100426108928
          else
            if i < 32 then
              BitVec.ofNat (edgeCount 12) 936959897445072896
            else
              if i < 33 then
                BitVec.ofNat (edgeCount 12) 2017823808013991936
              else
                BitVec.ofNat (edgeCount 12) 18555041639718453248
  else
    if i < 51 then
      if i < 42 then
        if i < 38 then
          if i < 36 then
            if i < 35 then
              BitVec.ofNat (edgeCount 12) 18771214421832237056
            else
              BitVec.ofNat (edgeCount 12) 37001785713428004864
          else
            if i < 37 then
              BitVec.ofNat (edgeCount 12) 37109872104484896768
            else
              BitVec.ofNat (edgeCount 12) 37217958495541788672
        else
          if i < 40 then
            if i < 39 then
              BitVec.ofNat (edgeCount 12) 37253987292560752640
            else
              BitVec.ofNat (edgeCount 12) 37758390450826248192
          else
            if i < 41 then
              BitVec.ofNat (edgeCount 12) 55376472193099628544
            else
              BitVec.ofNat (edgeCount 12) 522452809866543104
      else
        if i < 46 then
          if i < 44 then
            if i < 43 then
              BitVec.ofNat (edgeCount 12) 55394310669748666368
            else
              BitVec.ofNat (edgeCount 12) 216348910132658176
          else
            if i < 45 then
              BitVec.ofNat (edgeCount 12) 108508809680388096
            else
              BitVec.ofNat (edgeCount 12) 1729804675533766656
        else
          if i < 48 then
            if i < 47 then
              BitVec.ofNat (edgeCount 12) 252342454328492032
            else
              BitVec.ofNat (edgeCount 12) 396457642404347904
          else
            if i < 49 then
              BitVec.ofNat (edgeCount 12) 900860800669843456
            else
              if i < 50 then
                BitVec.ofNat (edgeCount 12) 2017753508257726464
              else
                BitVec.ofNat (edgeCount 12) 9331599303107411968
    else
      if i < 59 then
        if i < 55 then
          if i < 53 then
            if i < 52 then
              BitVec.ofNat (edgeCount 12) 9547772085221195776
            else
              BitVec.ofNat (edgeCount 12) 216348841681616896
          else
            if i < 54 then
              BitVec.ofNat (edgeCount 12) 360464029757472768
            else
              BitVec.ofNat (edgeCount 12) 9367663284498464768
        else
          if i < 57 then
            if i < 56 then
              BitVec.ofNat (edgeCount 12) 18518977727315312640
            else
              BitVec.ofNat (edgeCount 12) 108508741229346816
          else
            if i < 58 then
              BitVec.ofNat (edgeCount 12) 180566335267274752
            else
              BitVec.ofNat (edgeCount 12) 432767914400022528
      else
        if i < 63 then
          if i < 61 then
            if i < 60 then
              BitVec.ofNat (edgeCount 12) 612911899494842368
            else
              BitVec.ofNat (edgeCount 12) 1729804607082725376
          else
            if i < 62 then
              BitVec.ofNat (edgeCount 12) 9259823184046194688
            else
              BitVec.ofNat (edgeCount 12) 18527844189081698304
        else
          if i < 65 then
            if i < 64 then
              BitVec.ofNat (edgeCount 12) 108368141450477568
            else
              BitVec.ofNat (edgeCount 12) 612771299715973120
          else
            if i < 66 then
              BitVec.ofNat (edgeCount 12) 1729664007303856128
            else
              if i < 67 then
                BitVec.ofNat (edgeCount 12) 4647996565839937536
              else
                BitVec.ofNat (edgeCount 12) 1153485005394051072

def level6 : Level 12 := ⟨68, level6MaskAt⟩

def level7MaskAt (i : ℕ) : BitVec (edgeCount 12) :=
  if i < 87 then
    if i < 43 then
      if i < 21 then
        if i < 10 then
          if i < 5 then
            if i < 2 then
              if i < 1 then
                BitVec.ofNat (edgeCount 12) 4575657221408423936
              else
                BitVec.ofNat (edgeCount 12) 2269849396566818816
            else
              if i < 3 then
                BitVec.ofNat (edgeCount 12) 4539663608761548800
              else
                if i < 4 then
                  BitVec.ofNat (edgeCount 12) 38010416039379075072
                else
                  BitVec.ofNat (edgeCount 12) 1116998260704149504
          else
            if i < 7 then
              if i < 6 then
                BitVec.ofNat (edgeCount 12) 2197862171273068544
              else
                BitVec.ofNat (edgeCount 12) 4467676383467798528
            else
              if i < 8 then
                BitVec.ofNat (edgeCount 12) 37434025655819829248
              else
                if i < 9 then
                  BitVec.ofNat (edgeCount 12) 37938428814085324800
                else
                  BitVec.ofNat (edgeCount 12) 39055321521673207808
        else
          if i < 15 then
            if i < 12 then
              if i < 11 then
                BitVec.ofNat (edgeCount 12) 540678245889081344
              else
                BitVec.ofNat (edgeCount 12) 973023810116648960
            else
              if i < 13 then
                BitVec.ofNat (edgeCount 12) 2053887720685568000
              else
                if i < 14 then
                  BitVec.ofNat (edgeCount 12) 4323701932880297984
                else
                  BitVec.ofNat (edgeCount 12) 37145936017156472832
          else
            if i < 18 then
              if i < 16 then
                BitVec.ofNat (edgeCount 12) 37290051205232328704
              else
                if i < 17 then
                  BitVec.ofNat (edgeCount 12) 37794454363497824256
                else
                  BitVec.ofNat (edgeCount 12) 38911347071085707264
            else
              if i < 19 then
                BitVec.ofNat (edgeCount 12) 1116963145051537408
              else
                if i < 20 then
                  BitVec.ofNat (edgeCount 12) 2197827055620456448
                else
                  BitVec.ofNat (edgeCount 12) 4467641267815186432
      else
        if i < 32 then
          if i < 26 then
            if i < 23 then
              if i < 22 then
                BitVec.ofNat (edgeCount 12) 18987246466457665536
              else
                BitVec.ofNat (edgeCount 12) 19491649624723161088
            else
              if i < 24 then
                BitVec.ofNat (edgeCount 12) 55592504237725057024
              else
                if i < 25 then
                  BitVec.ofNat (edgeCount 12) 540537577120202752
                else
                  BitVec.ofNat (edgeCount 12) 1044940735385698304
          else
            if i < 29 then
              if i < 27 then
                BitVec.ofNat (edgeCount 12) 1080969532404662272
              else
                if i < 28 then
                  BitVec.ofNat (edgeCount 12) 2161833442973581312
                else
                  BitVec.ofNat (edgeCount 12) 18699051274678042624
            else
              if i < 30 then
                BitVec.ofNat (edgeCount 12) 18915224056791826432
              else
                if i < 31 then
                  BitVec.ofNat (edgeCount 12) 18951252853810790400
                else
                  BitVec.ofNat (edgeCount 12) 37145795348387594240
        else
          if i < 37 then
            if i < 34 then
              if i < 33 then
                BitVec.ofNat (edgeCount 12) 37361968130501378048
              else
                BitVec.ofNat (edgeCount 12) 55448424234021289984
            else
              if i < 35 then
                BitVec.ofNat (edgeCount 12) 540643130236469248
              else
                if i < 36 then
                  BitVec.ofNat (edgeCount 12) 972988694464036864
                else
                  BitVec.ofNat (edgeCount 12) 1081075085520928768
          else
            if i < 40 then
              if i < 38 then
                BitVec.ofNat (edgeCount 12) 2053852605032955904
              else
                if i < 39 then
                  BitVec.ofNat (edgeCount 12) 2089881402051919872
                else
                  BitVec.ofNat (edgeCount 12) 4323666817227685888
            else
              if i < 41 then
                BitVec.ofNat (edgeCount 12) 18699156827794309120
              else
                if i < 42 then
                  BitVec.ofNat (edgeCount 12) 18843272015870164992
                else
                  BitVec.ofNat (edgeCount 12) 19347675174135660544
    else
      if i < 65 then
        if i < 54 then
          if i < 48 then
            if i < 45 then
              if i < 44 then
                BitVec.ofNat (edgeCount 12) 37145900901503860736
              else
                BitVec.ofNat (edgeCount 12) 37290016089579716608
            else
              if i < 46 then
                BitVec.ofNat (edgeCount 12) 37398102480636608512
              else
                if i < 47 then
                  BitVec.ofNat (edgeCount 12) 37794419247845212160
                else
                  BitVec.ofNat (edgeCount 12) 37830448044864176128
          else
            if i < 51 then
              if i < 49 then
                BitVec.ofNat (edgeCount 12) 38911311955433095168
              else
                if i < 50 then
                  BitVec.ofNat (edgeCount 12) 55448529787137556480
                else
                  BitVec.ofNat (edgeCount 12) 55664702569251340288
            else
              if i < 52 then
                BitVec.ofNat (edgeCount 12) 558481606885507072
              else
                if i < 53 then
                  BitVec.ofNat (edgeCount 12) 1098913562169966592
                else
                  BitVec.ofNat (edgeCount 12) 18716995304443346944
        else
          if i < 59 then
            if i < 56 then
              if i < 55 then
                BitVec.ofNat (edgeCount 12) 55466368263786594304
              else
                BitVec.ofNat (edgeCount 12) 18663163215147433984
            else
              if i < 57 then
                BitVec.ofNat (edgeCount 12) 18807278403223289856
              else
                if i < 58 then
                  BitVec.ofNat (edgeCount 12) 19311681561488785408
                else
                  BitVec.ofNat (edgeCount 12) 252694229061468160
          else
            if i < 62 then
              if i < 60 then
                BitVec.ofNat (edgeCount 12) 504895808194215936
              else
                if i < 61 then
                  BitVec.ofNat (edgeCount 12) 685039793289035776
                else
                  BitVec.ofNat (edgeCount 12) 793126184345927680
            else
              if i < 63 then
                BitVec.ofNat (edgeCount 12) 1765903703857954816
              else
                if i < 64 then
                  BitVec.ofNat (edgeCount 12) 1801932500876918784
                else
                  BitVec.ofNat (edgeCount 12) 4035717916052684800
      else
        if i < 76 then
          if i < 70 then
            if i < 67 then
              if i < 66 then
                BitVec.ofNat (edgeCount 12) 18555323114695163904
              else
                BitVec.ofNat (edgeCount 12) 19059726272960659456
            else
              if i < 68 then
                BitVec.ofNat (edgeCount 12) 252307338407444480
              else
                if i < 69 then
                  BitVec.ofNat (edgeCount 12) 1008912075805687808
                else
                  BitVec.ofNat (edgeCount 12) 18554936224041140224
          else
            if i < 73 then
              if i < 71 then
                BitVec.ofNat (edgeCount 12) 252377707151622144
              else
                if i < 72 then
                  BitVec.ofNat (edgeCount 12) 504579286284369920
                else
                  BitVec.ofNat (edgeCount 12) 936924850511937536
            else
              if i < 74 then
                BitVec.ofNat (edgeCount 12) 2017788761080856576
              else
                if i < 75 then
                  BitVec.ofNat (edgeCount 12) 18627064186823245824
                else
                  BitVec.ofNat (edgeCount 12) 18663092983842209792
        else
          if i < 81 then
            if i < 78 then
              if i < 77 then
                BitVec.ofNat (edgeCount 12) 18879265765955993600
              else
                BitVec.ofNat (edgeCount 12) 55376437146166493184
            else
              if i < 79 then
                BitVec.ofNat (edgeCount 12) 55412465943185457152
              else
                if i < 80 then
                  BitVec.ofNat (edgeCount 12) 55628638725299240960
                else
                  BitVec.ofNat (edgeCount 12) 252623997756243968
          else
            if i < 84 then
              if i < 82 then
                BitVec.ofNat (edgeCount 12) 684969561983811584
              else
                if i < 83 then
                  BitVec.ofNat (edgeCount 12) 757027156021739520
                else
                  BitVec.ofNat (edgeCount 12) 1765833472552730624
            else
              if i < 85 then
                BitVec.ofNat (edgeCount 12) 4035647684747460608
              else
                if i < 86 then
                  BitVec.ofNat (edgeCount 12) 18555252883389939712
                else
                  BitVec.ofNat (edgeCount 12) 18627310477427867648
  else
    if i < 131 then
      if i < 109 then
        if i < 98 then
          if i < 92 then
            if i < 89 then
              if i < 88 then
                BitVec.ofNat (edgeCount 12) 18879512056560615424
              else
                BitVec.ofNat (edgeCount 12) 19059656041655435264
            else
              if i < 90 then
                BitVec.ofNat (edgeCount 12) 19167742432712327168
              else
                if i < 91 then
                  BitVec.ofNat (edgeCount 12) 20176548749243318272
                else
                  BitVec.ofNat (edgeCount 12) 55376683436771115008
          else
            if i < 95 then
              if i < 93 then
                BitVec.ofNat (edgeCount 12) 55917115392055574528
              else
                if i < 94 then
                  BitVec.ofNat (edgeCount 12) 540572830480203776
                else
                  BitVec.ofNat (edgeCount 12) 972918394707771392
            else
              if i < 96 then
                BitVec.ofNat (edgeCount 12) 2053782305276690432
              else
                if i < 97 then
                  BitVec.ofNat (edgeCount 12) 4323596517471420416
                else
                  BitVec.ofNat (edgeCount 12) 9475714491183267840
        else
          if i < 103 then
            if i < 100 then
              if i < 99 then
                BitVec.ofNat (edgeCount 12) 9619829679259123712
              else
                BitVec.ofNat (edgeCount 12) 10124232837524619264
            else
              if i < 101 then
                BitVec.ofNat (edgeCount 12) 27778343376816963584
              else
                if i < 102 then
                  BitVec.ofNat (edgeCount 12) 252377638700580864
                else
                  BitVec.ofNat (edgeCount 12) 396492826776436736
          else
            if i < 106 then
              if i < 104 then
                BitVec.ofNat (edgeCount 12) 468550420814364672
              else
                if i < 105 then
                  BitVec.ofNat (edgeCount 12) 504579217833328640
                else
                  BitVec.ofNat (edgeCount 12) 936924782060896256
            else
              if i < 107 then
                BitVec.ofNat (edgeCount 12) 1008982376098824192
              else
                if i < 108 then
                  BitVec.ofNat (edgeCount 12) 2017788692629815296
                else
                  BitVec.ofNat (edgeCount 12) 9331634487479500800
      else
        if i < 120 then
          if i < 114 then
            if i < 111 then
              if i < 110 then
                BitVec.ofNat (edgeCount 12) 9403692081517428736
              else
                BitVec.ofNat (edgeCount 12) 9439720878536392704
            else
              if i < 112 then
                BitVec.ofNat (edgeCount 12) 9655893660650176512
              else
                if i < 113 then
                  BitVec.ofNat (edgeCount 12) 18555006524334276608
                else
                  BitVec.ofNat (edgeCount 12) 18663092915391168512
          else
            if i < 117 then
              if i < 115 then
                BitVec.ofNat (edgeCount 12) 18807208103467024384
              else
                if i < 116 then
                  BitVec.ofNat (edgeCount 12) 37001750598043828224
                else
                  BitVec.ofNat (edgeCount 12) 37073808192081756160
            else
              if i < 118 then
                BitVec.ofNat (edgeCount 12) 37217923380157612032
              else
                if i < 119 then
                  BitVec.ofNat (edgeCount 12) 252623929305202688
                else
                  BitVec.ofNat (edgeCount 12) 468796711418986496
        else
          if i < 125 then
            if i < 122 then
              if i < 121 then
                BitVec.ofNat (edgeCount 12) 684969493532770304
              else
                BitVec.ofNat (edgeCount 12) 757027087570698240
            else
              if i < 123 then
                BitVec.ofNat (edgeCount 12) 1009228666703446016
              else
                if i < 124 then
                  BitVec.ofNat (edgeCount 12) 1765833404101689344
                else
                  BitVec.ofNat (edgeCount 12) 1873919795158581248
          else
            if i < 128 then
              if i < 126 then
                BitVec.ofNat (edgeCount 12) 4035647616296419328
              else
                if i < 127 then
                  BitVec.ofNat (edgeCount 12) 9331880778084122624
                else
                  BitVec.ofNat (edgeCount 12) 9403938372122050560
            else
              if i < 129 then
                BitVec.ofNat (edgeCount 12) 9836283936349618176
              else
                if i < 130 then
                  BitVec.ofNat (edgeCount 12) 37001996888648450048
                else
                  BitVec.ofNat (edgeCount 12) 37074054482686377984
    else
      if i < 153 then
        if i < 142 then
          if i < 136 then
            if i < 133 then
              if i < 132 then
                BitVec.ofNat (edgeCount 12) 37326256061819125760
              else
                BitVec.ofNat (edgeCount 12) 37506400046913945600
            else
              if i < 134 then
                BitVec.ofNat (edgeCount 12) 37614486437970837504
              else
                if i < 135 then
                  BitVec.ofNat (edgeCount 12) 38623292754501828608
                else
                  BitVec.ofNat (edgeCount 12) 46153311331465297920
          else
            if i < 139 then
              if i < 137 then
                BitVec.ofNat (edgeCount 12) 513445679599714304
              else
                if i < 138 then
                  BitVec.ofNat (edgeCount 12) 1017848837865209856
                else
                  BitVec.ofNat (edgeCount 12) 9340500949245886464
            else
              if i < 140 then
                BitVec.ofNat (edgeCount 12) 18563872986100662272
              else
                if i < 141 then
                  BitVec.ofNat (edgeCount 12) 18671959377157554176
                else
                  BitVec.ofNat (edgeCount 12) 46161931502627061760
        else
          if i < 147 then
            if i < 144 then
              if i < 143 then
                BitVec.ofNat (edgeCount 12) 9367698537590030336
              else
                BitVec.ofNat (edgeCount 12) 432767983119499264
            else
              if i < 145 then
                BitVec.ofNat (edgeCount 12) 9295852049784635392
              else
                if i < 146 then
                  BitVec.ofNat (edgeCount 12) 180496241401004032
                else
                  BitVec.ofNat (edgeCount 12) 432697820533751808
          else
            if i < 150 then
              if i < 148 then
                BitVec.ofNat (edgeCount 12) 108931228572319744
              else
                if i < 149 then
                  BitVec.ofNat (edgeCount 12) 217017619629211648
                else
                  BitVec.ofNat (edgeCount 12) 1189795139141238784
            else
              if i < 151 then
                BitVec.ofNat (edgeCount 12) 3459609351335968768
              else
                if i < 152 then
                  BitVec.ofNat (edgeCount 12) 9260245671389167616
                else
                  BitVec.ofNat (edgeCount 12) 216401549520273408
      else
        if i < 164 then
          if i < 158 then
            if i < 155 then
              if i < 154 then
                BitVec.ofNat (edgeCount 12) 252483329526333440
              else
                BitVec.ofNat (edgeCount 12) 684828893753901056
            else
              if i < 156 then
                BitVec.ofNat (edgeCount 12) 1765692804322820096
              else
                if i < 157 then
                  BitVec.ofNat (edgeCount 12) 4035507016517550080
                else
                  BitVec.ofNat (edgeCount 12) 4720054159877865472
          else
            if i < 161 then
              if i < 159 then
                BitVec.ofNat (edgeCount 12) 5224457318143361024
              else
                if i < 160 then
                  BitVec.ofNat (edgeCount 12) 216489716879458304
                else
                  BitVec.ofNat (edgeCount 12) 360604904955314176
            else
              if i < 162 then
                BitVec.ofNat (edgeCount 12) 648835281107025920
              else
                if i < 163 then
                  BitVec.ofNat (edgeCount 12) 4900233329344774144
                else
                  BitVec.ofNat (edgeCount 12) 9295746565658378240
        else
          if i < 169 then
            if i < 166 then
              if i < 165 then
                BitVec.ofNat (edgeCount 12) 108931091403898880
              else
                BitVec.ofNat (edgeCount 12) 325103873517682688
            else
              if i < 167 then
                BitVec.ofNat (edgeCount 12) 865535828802142208
              else
                if i < 168 then
                  BitVec.ofNat (edgeCount 12) 1189795001972817920
                else
                  BitVec.ofNat (edgeCount 12) 3459609214167547904
          else
            if i < 172 then
              if i < 170 then
                BitVec.ofNat (edgeCount 12) 4648559515793358848
              else
                if i < 171 then
                  BitVec.ofNat (edgeCount 12) 220711841530118144
                else
                  BitVec.ofNat (edgeCount 12) 9299968690309038080
            else
              if i < 173 then
                BitVec.ofNat (edgeCount 12) 108649891844096000
              else
                if i < 174 then
                  BitVec.ofNat (edgeCount 12) 1189513802413015040
                else
                  BitVec.ofNat (edgeCount 12) 2342435307019862016

def level7 : Level 12 := ⟨175, level7MaskAt⟩

def level8MaskAt (i : ℕ) : BitVec (edgeCount 12) :=
  if i < 242 then
    if i < 121 then
      if i < 60 then
        if i < 30 then
          if i < 15 then
            if i < 7 then
              if i < 3 then
                if i < 1 then
                  BitVec.ofNat (edgeCount 12) 9187343239835811840
                else
                  if i < 2 then
                    BitVec.ofNat (edgeCount 12) 4575692405780512768
                  else
                    BitVec.ofNat (edgeCount 12) 9151349627188936704
              else
                if i < 5 then
                  if i < 4 then
                    BitVec.ofNat (edgeCount 12) 39163337543985922048
                  else
                    BitVec.ofNat (edgeCount 12) 2269919765310996480
                else
                  if i < 6 then
                    BitVec.ofNat (edgeCount 12) 4503705180486762496
                  else
                    BitVec.ofNat (edgeCount 12) 9079362401895186432
            else
              if i < 11 then
                if i < 9 then
                  if i < 8 then
                    BitVec.ofNat (edgeCount 12) 38010486408123252736
                  else
                    BitVec.ofNat (edgeCount 12) 39091350318692171776
                else
                  if i < 10 then
                    BitVec.ofNat (edgeCount 12) 41361164530886901760
                  else
                    BitVec.ofNat (edgeCount 12) 1117138998192504832
              else
                if i < 13 then
                  if i < 12 then
                    BitVec.ofNat (edgeCount 12) 2125945314723495936
                  else
                    BitVec.ofNat (edgeCount 12) 4359730729899261952
                else
                  if i < 14 then
                    BitVec.ofNat (edgeCount 12) 8935387951307685888
                  else
                    BitVec.ofNat (edgeCount 12) 37434166393308184576
          else
            if i < 22 then
              if i < 18 then
                if i < 16 then
                  BitVec.ofNat (edgeCount 12) 37866511957535752192
                else
                  if i < 17 then
                    BitVec.ofNat (edgeCount 12) 38947375868104671232
                  else
                    BitVec.ofNat (edgeCount 12) 41217190080299401216
              else
                if i < 20 then
                  if i < 19 then
                    BitVec.ofNat (edgeCount 12) 540959720865792000
                  else
                    BitVec.ofNat (edgeCount 12) 829190097017503744
                else
                  if i < 21 then
                    BitVec.ofNat (edgeCount 12) 1837996413548494848
                  else
                    BitVec.ofNat (edgeCount 12) 4071781828724260864
            else
              if i < 26 then
                if i < 24 then
                  if i < 23 then
                    BitVec.ofNat (edgeCount 12) 8647439050132684800
                  else
                    BitVec.ofNat (edgeCount 12) 2269884649658384384
                else
                  if i < 25 then
                    BitVec.ofNat (edgeCount 12) 4503670064834150400
                  else
                    BitVec.ofNat (edgeCount 12) 9079327286242574336
              else
                if i < 28 then
                  if i < 27 then
                    BitVec.ofNat (edgeCount 12) 19563707218761089024
                  else
                    BitVec.ofNat (edgeCount 12) 20644571129330008064
                else
                  if i < 29 then
                    BitVec.ofNat (edgeCount 12) 55880734613876768768
                  else
                    BitVec.ofNat (edgeCount 12) 1116998329423626240
        else
          if i < 45 then
            if i < 37 then
              if i < 33 then
                if i < 31 then
                  BitVec.ofNat (edgeCount 12) 2197862239992545280
                else
                  if i < 32 then
                    BitVec.ofNat (edgeCount 12) 2233891037011509248
                  else
                    BitVec.ofNat (edgeCount 12) 4467676452187275264
              else
                if i < 35 then
                  if i < 34 then
                    BitVec.ofNat (edgeCount 12) 18987281650829754368
                  else
                    BitVec.ofNat (edgeCount 12) 19491684809095249920
                else
                  if i < 36 then
                    BitVec.ofNat (edgeCount 12) 19527713606114213888
                  else
                    BitVec.ofNat (edgeCount 12) 37434025724539305984
            else
              if i < 41 then
                if i < 39 then
                  if i < 38 then
                    BitVec.ofNat (edgeCount 12) 37938428882804801536
                  else
                    BitVec.ofNat (edgeCount 12) 55592539422097145856
                else
                  if i < 40 then
                    BitVec.ofNat (edgeCount 12) 1117103882539892736
                  else
                    BitVec.ofNat (edgeCount 12) 2125910199070883840
              else
                if i < 43 then
                  if i < 42 then
                    BitVec.ofNat (edgeCount 12) 2233996590127775744
                  else
                    BitVec.ofNat (edgeCount 12) 4359695614246649856
                else
                  if i < 44 then
                    BitVec.ofNat (edgeCount 12) 4395724411265613824
                  else
                    BitVec.ofNat (edgeCount 12) 8935352835655073792
          else
            if i < 52 then
              if i < 48 then
                if i < 46 then
                  BitVec.ofNat (edgeCount 12) 18987387203946020864
                else
                  if i < 47 then
                    BitVec.ofNat (edgeCount 12) 19419732768173588480
                  else
                    BitVec.ofNat (edgeCount 12) 20500596678742507520
              else
                if i < 50 then
                  if i < 49 then
                    BitVec.ofNat (edgeCount 12) 37434131277655572480
                  else
                    BitVec.ofNat (edgeCount 12) 37866476841883140096
                else
                  if i < 51 then
                    BitVec.ofNat (edgeCount 12) 37974563232940032000
                  else
                    BitVec.ofNat (edgeCount 12) 38947340752452059136
            else
              if i < 56 then
                if i < 54 then
                  if i < 53 then
                    BitVec.ofNat (edgeCount 12) 38983369549471023104
                  else
                    BitVec.ofNat (edgeCount 12) 41217154964646789120
                else
                  if i < 55 then
                    BitVec.ofNat (edgeCount 12) 55592644975213412352
                  else
                    BitVec.ofNat (edgeCount 12) 55736760163289268224
              else
                if i < 58 then
                  if i < 57 then
                    BitVec.ofNat (edgeCount 12) 56241163321554763776
                  else
                    BitVec.ofNat (edgeCount 12) 1134942359188930560
                else
                  if i < 59 then
                    BitVec.ofNat (edgeCount 12) 2251835066776813568
                  else
                    BitVec.ofNat (edgeCount 12) 19005225680595058688
      else
        if i < 90 then
          if i < 75 then
            if i < 67 then
              if i < 63 then
                if i < 61 then
                  BitVec.ofNat (edgeCount 12) 55610483451862450176
                else
                  if i < 62 then
                    BitVec.ofNat (edgeCount 12) 540678314608558080
                  else
                    BitVec.ofNat (edgeCount 12) 973023878836125696
              else
                if i < 65 then
                  if i < 64 then
                    BitVec.ofNat (edgeCount 12) 1081110269893017600
                  else
                    BitVec.ofNat (edgeCount 12) 2053887789405044736
                else
                  if i < 66 then
                    BitVec.ofNat (edgeCount 12) 2089916586424008704
                  else
                    BitVec.ofNat (edgeCount 12) 4323702001599774720
            else
              if i < 71 then
                if i < 69 then
                  if i < 68 then
                    BitVec.ofNat (edgeCount 12) 18699192012166397952
                  else
                    BitVec.ofNat (edgeCount 12) 18843307200242253824
                else
                  if i < 70 then
                    BitVec.ofNat (edgeCount 12) 18951393591299145728
                  else
                    BitVec.ofNat (edgeCount 12) 19347710358507749376
              else
                if i < 73 then
                  if i < 72 then
                    BitVec.ofNat (edgeCount 12) 19383739155526713344
                  else
                    BitVec.ofNat (edgeCount 12) 20464603066095632384
                else
                  if i < 74 then
                    BitVec.ofNat (edgeCount 12) 37145936085875949568
                  else
                    BitVec.ofNat (edgeCount 12) 37290051273951805440
          else
            if i < 82 then
              if i < 78 then
                if i < 76 then
                  BitVec.ofNat (edgeCount 12) 37794454432217300992
                else
                  if i < 77 then
                    BitVec.ofNat (edgeCount 12) 55448564971509645312
                  else
                    BitVec.ofNat (edgeCount 12) 55556651362566537216
              else
                if i < 80 then
                  if i < 79 then
                    BitVec.ofNat (edgeCount 12) 55664737753623429120
                  else
                    BitVec.ofNat (edgeCount 12) 55700766550642393088
                else
                  if i < 81 then
                    BitVec.ofNat (edgeCount 12) 56205169708907888640
                  else
                    BitVec.ofNat (edgeCount 12) 540924605213179904
            else
              if i < 86 then
                if i < 84 then
                  if i < 83 then
                    BitVec.ofNat (edgeCount 12) 829154981364891648
                  else
                    BitVec.ofNat (edgeCount 12) 1081356560497639424
                else
                  if i < 85 then
                    BitVec.ofNat (edgeCount 12) 1837961297895882752
                  else
                    BitVec.ofNat (edgeCount 12) 1946047688952774656
              else
                if i < 88 then
                  if i < 87 then
                    BitVec.ofNat (edgeCount 12) 4071746713071648768
                  else
                    BitVec.ofNat (edgeCount 12) 4107775510090612736
                else
                  if i < 89 then
                    BitVec.ofNat (edgeCount 12) 8647403934480072704
                  else
                    BitVec.ofNat (edgeCount 12) 18699438302771019776
        else
          if i < 105 then
            if i < 97 then
              if i < 93 then
                if i < 91 then
                  BitVec.ofNat (edgeCount 12) 19131783866998587392
                else
                  if i < 92 then
                    BitVec.ofNat (edgeCount 12) 20212647777567506432
                  else
                    BitVec.ofNat (edgeCount 12) 37146182376480571392
              else
                if i < 95 then
                  if i < 94 then
                    BitVec.ofNat (edgeCount 12) 37398383955613319168
                  else
                    BitVec.ofNat (edgeCount 12) 37578527940708139008
                else
                  if i < 96 then
                    BitVec.ofNat (edgeCount 12) 37686614331765030912
                  else
                    BitVec.ofNat (edgeCount 12) 38659391851277058048
            else
              if i < 101 then
                if i < 99 then
                  if i < 98 then
                    BitVec.ofNat (edgeCount 12) 38695420648296022016
                  else
                    BitVec.ofNat (edgeCount 12) 40929206063471788032
                else
                  if i < 100 then
                    BitVec.ofNat (edgeCount 12) 55448811262114267136
                  else
                    BitVec.ofNat (edgeCount 12) 55953214420379762688
              else
                if i < 103 then
                  if i < 102 then
                    BitVec.ofNat (edgeCount 12) 558551975629684736
                  else
                    BitVec.ofNat (edgeCount 12) 1062955133895180288
                else
                  if i < 104 then
                    BitVec.ofNat (edgeCount 12) 1098983930914144256
                  else
                    BitVec.ofNat (edgeCount 12) 2179847841483063296
          else
            if i < 113 then
              if i < 109 then
                if i < 107 then
                  if i < 106 then
                    BitVec.ofNat (edgeCount 12) 18717065673187524608
                  else
                    BitVec.ofNat (edgeCount 12) 18933238455301308416
                else
                  if i < 108 then
                    BitVec.ofNat (edgeCount 12) 55466438632530771968
                  else
                    BitVec.ofNat (edgeCount 12) 55538496226568699904
              else
                if i < 111 then
                  if i < 110 then
                    BitVec.ofNat (edgeCount 12) 540537714559156224
                  else
                    BitVec.ofNat (edgeCount 12) 1044940872824651776
                else
                  if i < 112 then
                    BitVec.ofNat (edgeCount 12) 2161833580412534784
                  else
                    BitVec.ofNat (edgeCount 12) 18699051412116996096
            else
              if i < 117 then
                if i < 115 then
                  if i < 114 then
                    BitVec.ofNat (edgeCount 12) 18915224194230779904
                  else
                    BitVec.ofNat (edgeCount 12) 55448424371460243456
                else
                  if i < 116 then
                    BitVec.ofNat (edgeCount 12) 540608083303333888
                  else
                    BitVec.ofNat (edgeCount 12) 972953647530901504
              else
                if i < 119 then
                  if i < 118 then
                    BitVec.ofNat (edgeCount 12) 1081040038587793408
                  else
                    BitVec.ofNat (edgeCount 12) 2053817558099820544
                else
                  if i < 120 then
                    BitVec.ofNat (edgeCount 12) 2089846355118784512
                  else
                    BitVec.ofNat (edgeCount 12) 4323631770294550528
    else
      if i < 181 then
        if i < 151 then
          if i < 136 then
            if i < 128 then
              if i < 124 then
                if i < 122 then
                  BitVec.ofNat (edgeCount 12) 18699121780861173760
                else
                  if i < 123 then
                    BitVec.ofNat (edgeCount 12) 18843236968937029632
                  else
                    BitVec.ofNat (edgeCount 12) 18915294562974957568
              else
                if i < 126 then
                  if i < 125 then
                    BitVec.ofNat (edgeCount 12) 18951323359993921536
                  else
                    BitVec.ofNat (edgeCount 12) 19347640127202525184
                else
                  if i < 127 then
                    BitVec.ofNat (edgeCount 12) 19383668924221489152
                  else
                    BitVec.ofNat (edgeCount 12) 19455726518259417088
            else
              if i < 132 then
                if i < 130 then
                  if i < 129 then
                    BitVec.ofNat (edgeCount 12) 20464532834790408192
                  else
                    BitVec.ofNat (edgeCount 12) 55448494740204421120
                else
                  if i < 131 then
                    BitVec.ofNat (edgeCount 12) 55556581131261313024
                  else
                    BitVec.ofNat (edgeCount 12) 55664667522318204928
              else
                if i < 134 then
                  if i < 133 then
                    BitVec.ofNat (edgeCount 12) 55700696319337168896
                  else
                    BitVec.ofNat (edgeCount 12) 56205099477602664448
                else
                  if i < 135 then
                    BitVec.ofNat (edgeCount 12) 540854373907955712
                  else
                    BitVec.ofNat (edgeCount 12) 829084750059667456
          else
            if i < 143 then
              if i < 139 then
                if i < 137 then
                  BitVec.ofNat (edgeCount 12) 1837891066590658560
                else
                  if i < 138 then
                    BitVec.ofNat (edgeCount 12) 1909948660628586496
                  else
                    BitVec.ofNat (edgeCount 12) 4071676481766424576
              else
                if i < 141 then
                  if i < 140 then
                    BitVec.ofNat (edgeCount 12) 8647333703174848512
                  else
                    BitVec.ofNat (edgeCount 12) 18699368071465795584
                else
                  if i < 142 then
                    BitVec.ofNat (edgeCount 12) 18915540853579579392
                  else
                    BitVec.ofNat (edgeCount 12) 19131713635693363200
            else
              if i < 147 then
                if i < 145 then
                  if i < 144 then
                    BitVec.ofNat (edgeCount 12) 19203771229731291136
                  else
                    BitVec.ofNat (edgeCount 12) 19455972808864038912
                else
                  if i < 146 then
                    BitVec.ofNat (edgeCount 12) 20212577546262282240
                  else
                    BitVec.ofNat (edgeCount 12) 20320663937319174144
              else
                if i < 149 then
                  if i < 148 then
                    BitVec.ofNat (edgeCount 12) 22482391758457012224
                  else
                    BitVec.ofNat (edgeCount 12) 55448741030809042944
                else
                  if i < 150 then
                    BitVec.ofNat (edgeCount 12) 55520798624846970880
                  else
                    BitVec.ofNat (edgeCount 12) 55953144189074538496
        else
          if i < 166 then
            if i < 158 then
              if i < 154 then
                if i < 152 then
                  BitVec.ofNat (edgeCount 12) 57070036896662421504
                else
                  if i < 153 then
                    BitVec.ofNat (edgeCount 12) 252448075895799808
                  else
                    BitVec.ofNat (edgeCount 12) 396563263971655680
              else
                if i < 156 then
                  if i < 155 then
                    BitVec.ofNat (edgeCount 12) 18555076961529495552
                  else
                    BitVec.ofNat (edgeCount 12) 18879336134700171264
                else
                  if i < 157 then
                    BitVec.ofNat (edgeCount 12) 19311681698927738880
                  else
                    BitVec.ofNat (edgeCount 12) 504860761261080576
            else
              if i < 162 then
                if i < 160 then
                  if i < 159 then
                    BitVec.ofNat (edgeCount 12) 793091137412792320
                  else
                    BitVec.ofNat (edgeCount 12) 1801897453943783424
                else
                  if i < 161 then
                    BitVec.ofNat (edgeCount 12) 18663374458818920448
                  else
                    BitVec.ofNat (edgeCount 12) 19095720023046488064
              else
                if i < 164 then
                  if i < 163 then
                    BitVec.ofNat (edgeCount 12) 19167777617084416000
                  else
                    BitVec.ofNat (edgeCount 12) 20176583933615407104
                else
                  if i < 165 then
                    BitVec.ofNat (edgeCount 12) 253186947709665280
                  else
                    BitVec.ofNat (edgeCount 12) 469359729823449088
          else
            if i < 173 then
              if i < 169 then
                if i < 167 then
                  BitVec.ofNat (edgeCount 12) 1009791685107908608
                else
                  if i < 168 then
                    BitVec.ofNat (edgeCount 12) 1261993264240656384
                  else
                    BitVec.ofNat (edgeCount 12) 1334050858278584320
              else
                if i < 171 then
                  if i < 170 then
                    BitVec.ofNat (edgeCount 12) 1586252437411332096
                  else
                    BitVec.ofNat (edgeCount 12) 3495778679416422400
                else
                  if i < 172 then
                    BitVec.ofNat (edgeCount 12) 3603865070473314304
                  else
                    BitVec.ofNat (edgeCount 12) 8071435900824846336
            else
              if i < 177 then
                if i < 175 then
                  if i < 174 then
                    BitVec.ofNat (edgeCount 12) 18555815833343361024
                  else
                    BitVec.ofNat (edgeCount 12) 19636679743912280064
                else
                  if i < 176 then
                    BitVec.ofNat (edgeCount 12) 21906493956107010048
                  else
                    BitVec.ofNat (edgeCount 12) 1117033582783627264
              else
                if i < 179 then
                  if i < 178 then
                    BitVec.ofNat (edgeCount 12) 2125839899314618368
                  else
                    BitVec.ofNat (edgeCount 12) 4359625314490384384
                else
                  if i < 180 then
                    BitVec.ofNat (edgeCount 12) 8935282535898808320
                  else
                    BitVec.ofNat (edgeCount 12) 9763944867334979584
      else
        if i < 211 then
          if i < 196 then
            if i < 188 then
              if i < 184 then
                if i < 182 then
                  BitVec.ofNat (edgeCount 12) 10196290431562547200
                else
                  if i < 183 then
                    BitVec.ofNat (edgeCount 12) 11277154342131466240
                  else
                    BitVec.ofNat (edgeCount 12) 27922458564892819456
              else
                if i < 186 then
                  if i < 185 then
                    BitVec.ofNat (edgeCount 12) 28066573752968675328
                  else
                    BitVec.ofNat (edgeCount 12) 540608014852292608
                else
                  if i < 187 then
                    BitVec.ofNat (edgeCount 12) 972953579079860224
                  else
                    BitVec.ofNat (edgeCount 12) 1045011173117788160
            else
              if i < 192 then
                if i < 190 then
                  if i < 189 then
                    BitVec.ofNat (edgeCount 12) 1081039970136752128
                  else
                    BitVec.ofNat (edgeCount 12) 2053817489648779264
                else
                  if i < 191 then
                    BitVec.ofNat (edgeCount 12) 2089846286667743232
                  else
                    BitVec.ofNat (edgeCount 12) 2161903880705671168
              else
                if i < 194 then
                  if i < 193 then
                    BitVec.ofNat (edgeCount 12) 4323631701843509248
                  else
                    BitVec.ofNat (edgeCount 12) 9475749675555356672
                else
                  if i < 195 then
                    BitVec.ofNat (edgeCount 12) 9619864863631212544
                  else
                    BitVec.ofNat (edgeCount 12) 9691922457669140480
          else
            if i < 203 then
              if i < 199 then
                if i < 197 then
                  BitVec.ofNat (edgeCount 12) 9727951254688104448
                else
                  if i < 198 then
                    BitVec.ofNat (edgeCount 12) 10124268021896708096
                  else
                    BitVec.ofNat (edgeCount 12) 10232354412953600000
              else
                if i < 201 then
                  if i < 200 then
                    BitVec.ofNat (edgeCount 12) 18699121712410132480
                  else
                    BitVec.ofNat (edgeCount 12) 18843236900485988352
                else
                  if i < 202 then
                    BitVec.ofNat (edgeCount 12) 18951323291542880256
                  else
                    BitVec.ofNat (edgeCount 12) 19383668855770447872
            else
              if i < 207 then
                if i < 205 then
                  if i < 204 then
                    BitVec.ofNat (edgeCount 12) 27778378561189052416
                  else
                    BitVec.ofNat (edgeCount 12) 27886464952245944320
                else
                  if i < 206 then
                    BitVec.ofNat (edgeCount 12) 37145865786119684096
                  else
                    BitVec.ofNat (edgeCount 12) 37289980974195539968
              else
                if i < 209 then
                  if i < 208 then
                    BitVec.ofNat (edgeCount 12) 37362038568233467904
                  else
                    BitVec.ofNat (edgeCount 12) 37794384132461035520
                else
                  if i < 210 then
                    BitVec.ofNat (edgeCount 12) 46297180228936531968
                  else
                    BitVec.ofNat (edgeCount 12) 55448494671753379840
        else
          if i < 226 then
            if i < 218 then
              if i < 214 then
                if i < 212 then
                  BitVec.ofNat (edgeCount 12) 540854305456914432
                else
                  if i < 213 then
                    BitVec.ofNat (edgeCount 12) 829084681608626176
                  else
                    BitVec.ofNat (edgeCount 12) 1045257463722409984
              else
                if i < 216 then
                  if i < 215 then
                    BitVec.ofNat (edgeCount 12) 1837890998139617280
                  else
                    BitVec.ofNat (edgeCount 12) 1909948592177545216
                else
                  if i < 217 then
                    BitVec.ofNat (edgeCount 12) 2162150171310292992
                  else
                    BitVec.ofNat (edgeCount 12) 4071676413315383296
            else
              if i < 222 then
                if i < 220 then
                  if i < 219 then
                    BitVec.ofNat (edgeCount 12) 4179762804372275200
                  else
                    BitVec.ofNat (edgeCount 12) 8647333634723807232
                else
                  if i < 221 then
                    BitVec.ofNat (edgeCount 12) 9475995966159978496
                  else
                    BitVec.ofNat (edgeCount 12) 9692168748273762304
              else
                if i < 224 then
                  if i < 223 then
                    BitVec.ofNat (edgeCount 12) 9908341530387546112
                  else
                    BitVec.ofNat (edgeCount 12) 9980399124425474048
                else
                  if i < 225 then
                    BitVec.ofNat (edgeCount 12) 10989205440956465152
                  else
                    BitVec.ofNat (edgeCount 12) 27778624851793674240
          else
            if i < 234 then
              if i < 230 then
                if i < 228 then
                  if i < 227 then
                    BitVec.ofNat (edgeCount 12) 37146112076724305920
                  else
                    BitVec.ofNat (edgeCount 12) 37362284858838089728
                else
                  if i < 229 then
                    BitVec.ofNat (edgeCount 12) 37578457640951873536
                  else
                    BitVec.ofNat (edgeCount 12) 37650515234989801472
              else
                if i < 232 then
                  if i < 231 then
                    BitVec.ofNat (edgeCount 12) 37902716814122549248
                  else
                    BitVec.ofNat (edgeCount 12) 38659321551520792576
                else
                  if i < 233 then
                    BitVec.ofNat (edgeCount 12) 38767407942577684480
                  else
                    BitVec.ofNat (edgeCount 12) 40929135763715522560
            else
              if i < 238 then
                if i < 236 then
                  if i < 235 then
                    BitVec.ofNat (edgeCount 12) 46225368925503225856
                  else
                    BitVec.ofNat (edgeCount 12) 46297426519541153792
                else
                  if i < 237 then
                    BitVec.ofNat (edgeCount 12) 46729772083768721408
                  else
                    BitVec.ofNat (edgeCount 12) 549474476618678272
              else
                if i < 240 then
                  if i < 239 then
                    BitVec.ofNat (edgeCount 12) 1053877634884173824
                  else
                    BitVec.ofNat (edgeCount 12) 1089906431903137792
                else
                  if i < 241 then
                    BitVec.ofNat (edgeCount 12) 2170770342472056832
                  else
                    BitVec.ofNat (edgeCount 12) 9484616137321742336
  else
    if i < 363 then
      if i < 302 then
        if i < 272 then
          if i < 257 then
            if i < 249 then
              if i < 245 then
                if i < 243 then
                  BitVec.ofNat (edgeCount 12) 9700788919435526144
                else
                  if i < 244 then
                    BitVec.ofNat (edgeCount 12) 18707988174176518144
                  else
                    BitVec.ofNat (edgeCount 12) 18960189753309265920
              else
                if i < 247 then
                  if i < 246 then
                    BitVec.ofNat (edgeCount 12) 27787245022955438080
                  else
                    BitVec.ofNat (edgeCount 12) 46233989096664989696
                else
                  if i < 248 then
                    BitVec.ofNat (edgeCount 12) 46306046690702917632
                  else
                    BitVec.ofNat (edgeCount 12) 396563195520614400
            else
              if i < 253 then
                if i < 251 then
                  if i < 250 then
                    BitVec.ofNat (edgeCount 12) 27814477726952194048
                  else
                    BitVec.ofNat (edgeCount 12) 27958592915028049920
                else
                  if i < 252 then
                    BitVec.ofNat (edgeCount 12) 504860692810039296
                  else
                    BitVec.ofNat (edgeCount 12) 793091068961751040
              else
                if i < 255 then
                  if i < 254 then
                    BitVec.ofNat (edgeCount 12) 1801897385492742144
                  else
                    BitVec.ofNat (edgeCount 12) 9440002353513103360
                else
                  if i < 256 then
                    BitVec.ofNat (edgeCount 12) 9656175135626887168
                  else
                    BitVec.ofNat (edgeCount 12) 9872347917740670976
          else
            if i < 264 then
              if i < 260 then
                if i < 258 then
                  BitVec.ofNat (edgeCount 12) 9944405511778598912
                else
                  if i < 259 then
                    BitVec.ofNat (edgeCount 12) 10953211828309590016
                  else
                    BitVec.ofNat (edgeCount 12) 18663374390367879168
              else
                if i < 262 then
                  if i < 261 then
                    BitVec.ofNat (edgeCount 12) 19095719954595446784
                  else
                    BitVec.ofNat (edgeCount 12) 27742631239146799104
                else
                  if i < 263 then
                    BitVec.ofNat (edgeCount 12) 253186879258624000
                  else
                    BitVec.ofNat (edgeCount 12) 469359661372407808
            else
              if i < 268 then
                if i < 266 then
                  if i < 265 then
                    BitVec.ofNat (edgeCount 12) 1009791616656867328
                  else
                    BitVec.ofNat (edgeCount 12) 1261993195789615104
                else
                  if i < 267 then
                    BitVec.ofNat (edgeCount 12) 1334050789827543040
                  else
                    BitVec.ofNat (edgeCount 12) 1586252368960290816
              else
                if i < 270 then
                  if i < 269 then
                    BitVec.ofNat (edgeCount 12) 3495778610965381120
                  else
                    BitVec.ofNat (edgeCount 12) 3603865002022273024
                else
                  if i < 271 then
                    BitVec.ofNat (edgeCount 12) 8071435832373805056
                  else
                    BitVec.ofNat (edgeCount 12) 9332443728037543936
        else
          if i < 287 then
            if i < 279 then
              if i < 275 then
                if i < 273 then
                  BitVec.ofNat (edgeCount 12) 9404501322075471872
                else
                  if i < 274 then
                    BitVec.ofNat (edgeCount 12) 10413307638606462976
                  else
                    BitVec.ofNat (edgeCount 12) 261314469211144192
              else
                if i < 277 then
                  if i < 276 then
                    BitVec.ofNat (edgeCount 12) 18563943354844839936
                  else
                    BitVec.ofNat (edgeCount 12) 18672100114645909504
                else
                  if i < 278 then
                    BitVec.ofNat (edgeCount 12) 18816215302721765376
                  else
                    BitVec.ofNat (edgeCount 12) 252412891792146432
            else
              if i < 283 then
                if i < 281 then
                  if i < 280 then
                    BitVec.ofNat (edgeCount 12) 396528079868002304
                  else
                    BitVec.ofNat (edgeCount 12) 468585673905930240
                else
                  if i < 282 then
                    BitVec.ofNat (edgeCount 12) 1009017629190389760
                  else
                    BitVec.ofNat (edgeCount 12) 2017823945721380864
              else
                if i < 285 then
                  if i < 284 then
                    BitVec.ofNat (edgeCount 12) 9331669740571066368
                  else
                    BitVec.ofNat (edgeCount 12) 9403727334608994304
                else
                  if i < 286 then
                    BitVec.ofNat (edgeCount 12) 9439756131627958272
                  else
                    BitVec.ofNat (edgeCount 12) 9655928913741742080
          else
            if i < 294 then
              if i < 290 then
                if i < 288 then
                  BitVec.ofNat (edgeCount 12) 18555041777425842176
                else
                  if i < 289 then
                    BitVec.ofNat (edgeCount 12) 18627099371463770112
                  else
                    BitVec.ofNat (edgeCount 12) 18663128168482734080
              else
                if i < 292 then
                  if i < 291 then
                    BitVec.ofNat (edgeCount 12) 37001785851135393792
                  else
                    BitVec.ofNat (edgeCount 12) 37073843445173321728
                else
                  if i < 293 then
                    BitVec.ofNat (edgeCount 12) 37217958633249177600
                  else
                    BitVec.ofNat (edgeCount 12) 252623998024679424
            else
              if i < 298 then
                if i < 296 then
                  if i < 295 then
                    BitVec.ofNat (edgeCount 12) 468796780138463232
                  else
                    BitVec.ofNat (edgeCount 12) 504825577157427200
                else
                  if i < 297 then
                    BitVec.ofNat (edgeCount 12) 684969562252247040
                  else
                    BitVec.ofNat (edgeCount 12) 793055953309138944
              else
                if i < 300 then
                  if i < 299 then
                    BitVec.ofNat (edgeCount 12) 1009228735422922752
                  else
                    BitVec.ofNat (edgeCount 12) 1801862269840130048
                else
                  if i < 301 then
                    BitVec.ofNat (edgeCount 12) 1873919863878057984
                  else
                    BitVec.ofNat (edgeCount 12) 4035647685015896064
      else
        if i < 332 then
          if i < 317 then
            if i < 309 then
              if i < 305 then
                if i < 303 then
                  BitVec.ofNat (edgeCount 12) 9331880846803599360
                else
                  if i < 304 then
                    BitVec.ofNat (edgeCount 12) 9439967237860491264
                  else
                    BitVec.ofNat (edgeCount 12) 9872312802088058880
              else
                if i < 307 then
                  if i < 306 then
                    BitVec.ofNat (edgeCount 12) 18555252883658375168
                  else
                    BitVec.ofNat (edgeCount 12) 18627310477696303104
                else
                  if i < 308 then
                    BitVec.ofNat (edgeCount 12) 19059656041923870720
                  else
                    BitVec.ofNat (edgeCount 12) 37001996957367926784
            else
              if i < 313 then
                if i < 311 then
                  if i < 310 then
                    BitVec.ofNat (edgeCount 12) 37074054551405854720
                  else
                    BitVec.ofNat (edgeCount 12) 37110083348424818688
                else
                  if i < 312 then
                    BitVec.ofNat (edgeCount 12) 37326256130538602496
                  else
                    BitVec.ofNat (edgeCount 12) 37506400115633422336
              else
                if i < 315 then
                  if i < 314 then
                    BitVec.ofNat (edgeCount 12) 37542428912652386304
                  else
                    BitVec.ofNat (edgeCount 12) 37614486506690314240
                else
                  if i < 316 then
                    BitVec.ofNat (edgeCount 12) 38623292823221305344
                  else
                    BitVec.ofNat (edgeCount 12) 46153311400184774656
          else
            if i < 324 then
              if i < 320 then
                if i < 318 then
                  BitVec.ofNat (edgeCount 12) 46189340197203738624
                else
                  if i < 319 then
                    BitVec.ofNat (edgeCount 12) 55376683437039550464
                  else
                    BitVec.ofNat (edgeCount 12) 261279353558532096
              else
                if i < 322 then
                  if i < 321 then
                    BitVec.ofNat (edgeCount 12) 1017884090956775424
                  else
                    BitVec.ofNat (edgeCount 12) 9340536202337452032
                else
                  if i < 323 then
                    BitVec.ofNat (edgeCount 12) 18563908239192227840
                  else
                    BitVec.ofNat (edgeCount 12) 252413097950576640
            else
              if i < 328 then
                if i < 326 then
                  if i < 325 then
                    BitVec.ofNat (edgeCount 12) 504614677083324416
                  else
                    BitVec.ofNat (edgeCount 12) 900931444291928064
                else
                  if i < 327 then
                    BitVec.ofNat (edgeCount 12) 2017824151879811072
                  else
                    BitVec.ofNat (edgeCount 12) 9331669946729496576
              else
                if i < 330 then
                  if i < 329 then
                    BitVec.ofNat (edgeCount 12) 9547842728843280384
                  else
                    BitVec.ofNat (edgeCount 12) 18663128374641164288
                else
                  if i < 331 then
                    BitVec.ofNat (edgeCount 12) 252553835438931968
                  else
                    BitVec.ofNat (edgeCount 12) 468726617552715776
        else
          if i < 347 then
            if i < 339 then
              if i < 335 then
                if i < 333 then
                  BitVec.ofNat (edgeCount 12) 504755414571679744
                else
                  if i < 334 then
                    BitVec.ofNat (edgeCount 12) 756956993704427520
                  else
                    BitVec.ofNat (edgeCount 12) 1009158572837175296
              else
                if i < 337 then
                  if i < 336 then
                    BitVec.ofNat (edgeCount 12) 1765763310235418624
                  else
                    BitVec.ofNat (edgeCount 12) 1873849701292310528
                else
                  if i < 338 then
                    BitVec.ofNat (edgeCount 12) 4035577522430148608
                  else
                    BitVec.ofNat (edgeCount 12) 9331810684217851904
            else
              if i < 343 then
                if i < 341 then
                  if i < 340 then
                    BitVec.ofNat (edgeCount 12) 9403868278255779840
                  else
                    BitVec.ofNat (edgeCount 12) 9836213842483347456
                else
                  if i < 342 then
                    BitVec.ofNat (edgeCount 12) 18555182721072627712
                  else
                    BitVec.ofNat (edgeCount 12) 18627240315110555648
              else
                if i < 345 then
                  if i < 344 then
                    BitVec.ofNat (edgeCount 12) 18771355503186411520
                  else
                    BitVec.ofNat (edgeCount 12) 18807384300205375488
                else
                  if i < 346 then
                    BitVec.ofNat (edgeCount 12) 18879441894243303424
                  else
                    BitVec.ofNat (edgeCount 12) 19059585879338123264
          else
            if i < 355 then
              if i < 351 then
                if i < 349 then
                  if i < 348 then
                    BitVec.ofNat (edgeCount 12) 19311787458470871040
                  else
                    BitVec.ofNat (edgeCount 12) 27706497163889475584
                else
                  if i < 350 then
                    BitVec.ofNat (edgeCount 12) 55376613274453803008
                  else
                    BitVec.ofNat (edgeCount 12) 55412642071472766976
              else
                if i < 353 then
                  if i < 352 then
                    BitVec.ofNat (edgeCount 12) 55484699665510694912
                  else
                    BitVec.ofNat (edgeCount 12) 55917045229738262528
                else
                  if i < 354 then
                    BitVec.ofNat (edgeCount 12) 253046416648175616
                  else
                    BitVec.ofNat (edgeCount 12) 397161604724031488
            else
              if i < 359 then
                if i < 357 then
                  if i < 356 then
                    BitVec.ofNat (edgeCount 12) 505247995780923392
                  else
                    BitVec.ofNat (edgeCount 12) 1261852733179166720
                else
                  if i < 358 then
                    BitVec.ofNat (edgeCount 12) 1369939124236058624
                  else
                    BitVec.ofNat (edgeCount 12) 1514054312311914496
              else
                if i < 361 then
                  if i < 360 then
                    BitVec.ofNat (edgeCount 12) 3495638148354932736
                  else
                    BitVec.ofNat (edgeCount 12) 3531666945373896704
                else
                  if i < 362 then
                    BitVec.ofNat (edgeCount 12) 8071295369763356672
                  else
                    BitVec.ofNat (edgeCount 12) 9332303265427095552
    else
      if i < 424 then
        if i < 393 then
          if i < 378 then
            if i < 370 then
              if i < 366 then
                if i < 364 then
                  BitVec.ofNat (edgeCount 12) 10413167175996014592
                else
                  if i < 365 then
                    BitVec.ofNat (edgeCount 12) 18555675302281871360
                  else
                    BitVec.ofNat (edgeCount 12) 18663761693338763264
              else
                if i < 368 then
                  if i < 367 then
                    BitVec.ofNat (edgeCount 12) 18771848084395655168
                  else
                    BitVec.ofNat (edgeCount 12) 18807876881414619136
                else
                  if i < 369 then
                    BitVec.ofNat (edgeCount 12) 19312280039680114688
                  else
                    BitVec.ofNat (edgeCount 12) 19636539212850790400
            else
              if i < 374 then
                if i < 372 then
                  if i < 371 then
                    BitVec.ofNat (edgeCount 12) 19672568009869754368
                  else
                    BitVec.ofNat (edgeCount 12) 19888740791983538176
                else
                  if i < 373 then
                    BitVec.ofNat (edgeCount 12) 21906353425045520384
                  else
                    BitVec.ofNat (edgeCount 12) 27706989745098719232
              else
                if i < 376 then
                  if i < 375 then
                    BitVec.ofNat (edgeCount 12) 55377105855663046656
                  else
                    BitVec.ofNat (edgeCount 12) 55413134652682010624
                else
                  if i < 377 then
                    BitVec.ofNat (edgeCount 12) 56493998563250929664
                  else
                    BitVec.ofNat (edgeCount 12) 504631925671985152
          else
            if i < 385 then
              if i < 381 then
                if i < 379 then
                  BitVec.ofNat (edgeCount 12) 936977489899552768
                else
                  if i < 380 then
                    BitVec.ofNat (edgeCount 12) 2017841400468471808
                  else
                    BitVec.ofNat (edgeCount 12) 9331687195318157312
              else
                if i < 383 then
                  if i < 382 then
                    BitVec.ofNat (edgeCount 12) 27706373674989780992
                  else
                    BitVec.ofNat (edgeCount 12) 37001803305882484736
                else
                  if i < 384 then
                    BitVec.ofNat (edgeCount 12) 37109889696939376640
                  else
                    BitVec.ofNat (edgeCount 12) 37217976087996268544
            else
              if i < 389 then
                if i < 387 then
                  if i < 386 then
                    BitVec.ofNat (edgeCount 12) 37254004885015232512
                  else
                    BitVec.ofNat (edgeCount 12) 37758408043280728064
                else
                  if i < 388 then
                    BitVec.ofNat (edgeCount 12) 46153117748699332608
                  else
                    BitVec.ofNat (edgeCount 12) 432767983656370176
              else
                if i < 391 then
                  if i < 390 then
                    BitVec.ofNat (edgeCount 12) 432697752351145984
                  else
                    BitVec.ofNat (edgeCount 12) 217017551446605824
                else
                  if i < 392 then
                    BitVec.ofNat (edgeCount 12) 109776066356183040
                  else
                    BitVec.ofNat (edgeCount 12) 6919218702940372992
        else
          if i < 408 then
            if i < 400 then
              if i < 396 then
                if i < 394 then
                  BitVec.ofNat (edgeCount 12) 540713705678045184
                else
                  if i < 395 then
                    BitVec.ofNat (edgeCount 12) 828944081829756928
                  else
                    BitVec.ofNat (edgeCount 12) 1837750398360748032
              else
                if i < 398 then
                  if i < 397 then
                    BitVec.ofNat (edgeCount 12) 4071535813536514048
                  else
                    BitVec.ofNat (edgeCount 12) 4864169347953721344
                else
                  if i < 399 then
                    BitVec.ofNat (edgeCount 12) 5296514912181288960
                  else
                    BitVec.ofNat (edgeCount 12) 6377378822750208000
            else
              if i < 404 then
                if i < 402 then
                  if i < 401 then
                    BitVec.ofNat (edgeCount 12) 13943426196732641280
                  else
                    BitVec.ofNat (edgeCount 12) 252518513898422272
                else
                  if i < 403 then
                    BitVec.ofNat (edgeCount 12) 396633701974278144
                  else
                    BitVec.ofNat (edgeCount 12) 504720093031170048
              else
                if i < 406 then
                  if i < 405 then
                    BitVec.ofNat (edgeCount 12) 684864078125989888
                  else
                    BitVec.ofNat (edgeCount 12) 792950469182881792
                else
                  if i < 407 then
                    BitVec.ofNat (edgeCount 12) 901036860239773696
                  else
                    BitVec.ofNat (edgeCount 12) 937065657258737664
          else
            if i < 416 then
              if i < 412 then
                if i < 410 then
                  if i < 409 then
                    BitVec.ofNat (edgeCount 12) 1801756785713872896
                  else
                    BitVec.ofNat (edgeCount 12) 2017929567827656704
                else
                  if i < 411 then
                    BitVec.ofNat (edgeCount 12) 4035542200889638912
                  else
                    BitVec.ofNat (edgeCount 12) 4720089344249954304
              else
                if i < 414 then
                  if i < 413 then
                    BitVec.ofNat (edgeCount 12) 4936262126363738112
                  else
                    BitVec.ofNat (edgeCount 12) 4972290923382702080
                else
                  if i < 415 then
                    BitVec.ofNat (edgeCount 12) 5476694081648197632
                  else
                    BitVec.ofNat (edgeCount 12) 9331775362677342208
            else
              if i < 420 then
                if i < 418 then
                  if i < 417 then
                    BitVec.ofNat (edgeCount 12) 9439861753734234112
                  else
                    BitVec.ofNat (edgeCount 12) 9583976941810089984
                else
                  if i < 419 then
                    BitVec.ofNat (edgeCount 12) 9872207317961801728
                  else
                    BitVec.ofNat (edgeCount 12) 37001891473241669632
              else
                if i < 422 then
                  if i < 421 then
                    BitVec.ofNat (edgeCount 12) 37218064255355453440
                  else
                    BitVec.ofNat (edgeCount 12) 37506294631507165184
                else
                  if i < 423 then
                    BitVec.ofNat (edgeCount 12) 253046279479754752
                  else
                    BitVec.ofNat (edgeCount 12) 397161467555610624
      else
        if i < 454 then
          if i < 439 then
            if i < 431 then
              if i < 427 then
                if i < 425 then
                  BitVec.ofNat (edgeCount 12) 901564625821106176
                else
                  if i < 426 then
                    BitVec.ofNat (edgeCount 12) 1261852596010745856
                  else
                    BitVec.ofNat (edgeCount 12) 1478025378124529664
              else
                if i < 429 then
                  if i < 428 then
                    BitVec.ofNat (edgeCount 12) 2018457333408989184
                  else
                    BitVec.ofNat (edgeCount 12) 3495638011186511872
                else
                  if i < 430 then
                    BitVec.ofNat (edgeCount 12) 3747839590319259648
                  else
                    BitVec.ofNat (edgeCount 12) 4720617109831286784
            else
              if i < 435 then
                if i < 433 then
                  if i < 432 then
                    BitVec.ofNat (edgeCount 12) 4936789891945070592
                  else
                    BitVec.ofNat (edgeCount 12) 5801481020400205824
                else
                  if i < 434 then
                    BitVec.ofNat (edgeCount 12) 37002419238823002112
                  else
                    BitVec.ofNat (edgeCount 12) 37218592020936785920
              else
                if i < 437 then
                  if i < 436 then
                    BitVec.ofNat (edgeCount 12) 37759023976221245440
                  else
                    BitVec.ofNat (edgeCount 12) 38083283149391921152
                else
                  if i < 438 then
                    BitVec.ofNat (edgeCount 12) 38335484728524668928
                  else
                    BitVec.ofNat (edgeCount 12) 40353097361586651136
          else
            if i < 446 then
              if i < 442 then
                if i < 440 then
                  BitVec.ofNat (edgeCount 12) 41542047663212462080
                else
                  if i < 441 then
                    BitVec.ofNat (edgeCount 12) 508942217681829888
                  else
                    BitVec.ofNat (edgeCount 12) 941287781909397504
              else
                if i < 444 then
                  if i < 443 then
                    BitVec.ofNat (edgeCount 12) 2022151692478316544
                  else
                    BitVec.ofNat (edgeCount 12) 4724311468900614144
                else
                  if i < 445 then
                    BitVec.ofNat (edgeCount 12) 9335997487328002048
                  else
                    BitVec.ofNat (edgeCount 12) 9444083878384893952
            else
              if i < 450 then
                if i < 448 then
                  if i < 447 then
                    BitVec.ofNat (edgeCount 12) 9588199066460749824
                  else
                    BitVec.ofNat (edgeCount 12) 41545742022281789440
                else
                  if i < 449 then
                    BitVec.ofNat (edgeCount 12) 4756153394360483840
                  else
                    BitVec.ofNat (edgeCount 12) 360710526791057408
              else
                if i < 452 then
                  if i < 451 then
                    BitVec.ofNat (edgeCount 12) 4900338951180517376
                  else
                    BitVec.ofNat (edgeCount 12) 217017551180267520
                else
                  if i < 453 then
                    BitVec.ofNat (edgeCount 12) 361132739256123392
                  else
                    BitVec.ofNat (edgeCount 12) 865535897521618944
        else
          if i < 469 then
            if i < 461 then
              if i < 457 then
                if i < 455 then
                  BitVec.ofNat (edgeCount 12) 1225823867711258624
                else
                  if i < 456 then
                    BitVec.ofNat (edgeCount 12) 4756645975569727488
                  else
                    BitVec.ofNat (edgeCount 12) 9296274399959187456
              else
                if i < 459 then
                  if i < 458 then
                    BitVec.ofNat (edgeCount 12) 108509428694646784
                  else
                    BitVec.ofNat (edgeCount 12) 108790903671357440
                else
                  if i < 460 then
                    BitVec.ofNat (edgeCount 12) 324963685785141248
                  else
                    BitVec.ofNat (edgeCount 12) 865395641069600768
            else
              if i < 465 then
                if i < 463 then
                  if i < 462 then
                    BitVec.ofNat (edgeCount 12) 109776066089844736
                  else
                    BitVec.ofNat (edgeCount 12) 181833660127772672
                else
                  if i < 464 then
                    BitVec.ofNat (edgeCount 12) 434035239260520448
                  else
                    BitVec.ofNat (edgeCount 12) 2343561481265610752
              else
                if i < 467 then
                  if i < 466 then
                    BitVec.ofNat (edgeCount 12) 4649404490479304704
                  else
                    BitVec.ofNat (edgeCount 12) 9367707196514631680
                else
                  if i < 468 then
                    BitVec.ofNat (edgeCount 12) 216603859930316800
                  else
                    BitVec.ofNat (edgeCount 12) 432776642044100608
          else
            if i < 477 then
              if i < 473 then
                if i < 471 then
                  if i < 470 then
                    BitVec.ofNat (edgeCount 12) 9295860708709236736
                  else
                    BitVec.ofNat (edgeCount 12) 252765079919951872
                else
                  if i < 472 then
                    BitVec.ofNat (edgeCount 12) 1261571396450942976
                  else
                    BitVec.ofNat (edgeCount 12) 2414492901057789952
              else
                if i < 475 then
                  if i < 474 then
                    BitVec.ofNat (edgeCount 12) 3495356811626708992
                  else
                    BitVec.ofNat (edgeCount 12) 216771467273076736
                else
                  if i < 476 then
                    BitVec.ofNat (edgeCount 12) 649117031500644352
                  else
                    BitVec.ofNat (edgeCount 12) 1225577783804067840
            else
              if i < 481 then
                if i < 479 then
                  if i < 478 then
                    BitVec.ofNat (edgeCount 12) 2882902446676410368
                  else
                    BitVec.ofNat (edgeCount 12) 4684342297624608768
                else
                  if i < 480 then
                    BitVec.ofNat (edgeCount 12) 109775791750938624
                  else
                    BitVec.ofNat (edgeCount 12) 614178950016434176
              else
                if i < 483 then
                  if i < 482 then
                    BitVec.ofNat (edgeCount 12) 1731071657604317184
                  else
                    BitVec.ofNat (edgeCount 12) 2343561206926704640
                else
                  if i < 484 then
                    BitVec.ofNat (edgeCount 12) 218460317133340672
                  else
                    BitVec.ofNat (edgeCount 12) 4686031147484872704

def level8 : Level 12 := ⟨485, level8MaskAt⟩

def level9MaskAt (i : ℕ) : BitVec (edgeCount 12) :=
  if i < 702 then
    if i < 351 then
      if i < 175 then
        if i < 87 then
          if i < 43 then
            if i < 21 then
              if i < 10 then
                if i < 5 then
                  if i < 2 then
                    if i < 1 then
                      BitVec.ofNat (edgeCount 12) 18410715276690587648
                    else
                      BitVec.ofNat (edgeCount 12) 9187378424207900672
                  else
                    if i < 3 then
                      BitVec.ofNat (edgeCount 12) 18374721664043712512
                    else
                      if i < 4 then
                        BitVec.ofNat (edgeCount 12) 41469180553199616000
                      else
                        BitVec.ofNat (edgeCount 12) 4575762774524690432
                else
                  if i < 7 then
                    if i < 6 then
                      BitVec.ofNat (edgeCount 12) 9115391198914150400
                    else
                      BitVec.ofNat (edgeCount 12) 18302734438749962240
                  else
                    if i < 8 then
                      BitVec.ofNat (edgeCount 12) 39163407912730099712
                    else
                      if i < 9 then
                        BitVec.ofNat (edgeCount 12) 41397193327905865728
                      else
                        BitVec.ofNat (edgeCount 12) 45972850549314289664
              else
                if i < 15 then
                  if i < 12 then
                    if i < 11 then
                      BitVec.ofNat (edgeCount 12) 2270060502799351808
                    else
                      BitVec.ofNat (edgeCount 12) 4431788323937189888
                  else
                    if i < 13 then
                      BitVec.ofNat (edgeCount 12) 8971416748326649856
                    else
                      if i < 14 then
                        BitVec.ofNat (edgeCount 12) 18158759988162461696
                      else
                        BitVec.ofNat (edgeCount 12) 38010627145611608064
                else
                  if i < 18 then
                    if i < 16 then
                      BitVec.ofNat (edgeCount 12) 39019433462142599168
                    else
                      if i < 17 then
                        BitVec.ofNat (edgeCount 12) 41253218877318365184
                      else
                        BitVec.ofNat (edgeCount 12) 45828876098726789120
                  else
                    if i < 19 then
                      BitVec.ofNat (edgeCount 12) 1117420473169215488
                    else
                      if i < 20 then
                        BitVec.ofNat (edgeCount 12) 1982111601624350720
                      else
                        BitVec.ofNat (edgeCount 12) 4143839422762188800
            else
              if i < 32 then
                if i < 26 then
                  if i < 23 then
                    if i < 22 then
                      BitVec.ofNat (edgeCount 12) 8683467847151648768
                    else
                      BitVec.ofNat (edgeCount 12) 17870811086987460608
                  else
                    if i < 24 then
                      BitVec.ofNat (edgeCount 12) 37434447868284895232
                    else
                      if i < 25 then
                        BitVec.ofNat (edgeCount 12) 37722678244436606976
                      else
                        BitVec.ofNat (edgeCount 12) 38731484560967598080
                else
                  if i < 29 then
                    if i < 27 then
                      BitVec.ofNat (edgeCount 12) 40965269976143364096
                    else
                      if i < 28 then
                        BitVec.ofNat (edgeCount 12) 45540927197551788032
                      else
                        BitVec.ofNat (edgeCount 12) 4575727658872078336
                  else
                    if i < 30 then
                      BitVec.ofNat (edgeCount 12) 9115356083261538304
                    else
                      if i < 31 then
                        BitVec.ofNat (edgeCount 12) 18302699323097350144
                      else
                        BitVec.ofNat (edgeCount 12) 20716628723367936000
              else
                if i < 37 then
                  if i < 34 then
                    if i < 33 then
                      BitVec.ofNat (edgeCount 12) 22950414138543702016
                    else
                      BitVec.ofNat (edgeCount 12) 56457195366180192256
                  else
                    if i < 35 then
                      BitVec.ofNat (edgeCount 12) 2269919834030473216
                    else
                      if i < 36 then
                        BitVec.ofNat (edgeCount 12) 4503705249206239232
                      else
                        BitVec.ofNat (edgeCount 12) 4539734046225203200
                else
                  if i < 40 then
                    if i < 38 then
                      BitVec.ofNat (edgeCount 12) 9079362470614663168
                    else
                      if i < 39 then
                        BitVec.ofNat (edgeCount 12) 19563742403133177856
                      else
                        BitVec.ofNat (edgeCount 12) 20644606313702096896
                  else
                    if i < 41 then
                      BitVec.ofNat (edgeCount 12) 20680635110721060864
                    else
                      if i < 42 then
                        BitVec.ofNat (edgeCount 12) 38010486476842729472
                      else
                        BitVec.ofNat (edgeCount 12) 39091350387411648512
          else
            if i < 65 then
              if i < 54 then
                if i < 48 then
                  if i < 45 then
                    if i < 44 then
                      BitVec.ofNat (edgeCount 12) 55880769798248857600
                    else
                      BitVec.ofNat (edgeCount 12) 2270025387146739712
                  else
                    if i < 46 then
                      BitVec.ofNat (edgeCount 12) 4431753208284577792
                    else
                      if i < 47 then
                        BitVec.ofNat (edgeCount 12) 4539839599341469696
                      else
                        BitVec.ofNat (edgeCount 12) 8971381632674037760
                else
                  if i < 51 then
                    if i < 49 then
                      BitVec.ofNat (edgeCount 12) 9007410429693001728
                    else
                      if i < 50 then
                        BitVec.ofNat (edgeCount 12) 18158724872509849600
                      else
                        BitVec.ofNat (edgeCount 12) 19563847956249444352
                  else
                    if i < 52 then
                      BitVec.ofNat (edgeCount 12) 20572654272780435456
                    else
                      if i < 53 then
                        BitVec.ofNat (edgeCount 12) 22806439687956201472
                      else
                        BitVec.ofNat (edgeCount 12) 38010592029958995968
              else
                if i < 59 then
                  if i < 56 then
                    if i < 55 then
                      BitVec.ofNat (edgeCount 12) 39019398346489987072
                    else
                      BitVec.ofNat (edgeCount 12) 39127484737546878976
                  else
                    if i < 57 then
                      BitVec.ofNat (edgeCount 12) 41253183761665753088
                    else
                      if i < 58 then
                        BitVec.ofNat (edgeCount 12) 41289212558684717056
                      else
                        BitVec.ofNat (edgeCount 12) 45828840983074177024
                else
                  if i < 62 then
                    if i < 60 then
                      BitVec.ofNat (edgeCount 12) 55880875351365124096
                    else
                      if i < 61 then
                        BitVec.ofNat (edgeCount 12) 56313220915592691712
                      else
                        BitVec.ofNat (edgeCount 12) 57394084826161610752
                  else
                    if i < 63 then
                      BitVec.ofNat (edgeCount 12) 2287863863795777536
                    else
                      if i < 64 then
                        BitVec.ofNat (edgeCount 12) 4557678075990507520
                      else
                        BitVec.ofNat (edgeCount 12) 19581686432898482176
            else
              if i < 76 then
                if i < 70 then
                  if i < 67 then
                    if i < 66 then
                      BitVec.ofNat (edgeCount 12) 55898713828014161920
                    else
                      BitVec.ofNat (edgeCount 12) 1117139066911981568
                  else
                    if i < 68 then
                      BitVec.ofNat (edgeCount 12) 2125945383442972672
                    else
                      if i < 69 then
                        BitVec.ofNat (edgeCount 12) 2234031774499864576
                      else
                        BitVec.ofNat (edgeCount 12) 4359730798618738688
                else
                  if i < 73 then
                    if i < 71 then
                      BitVec.ofNat (edgeCount 12) 4395759595637702656
                    else
                      if i < 72 then
                        BitVec.ofNat (edgeCount 12) 8935388020027162624
                      else
                        BitVec.ofNat (edgeCount 12) 18987422388318109696
                  else
                    if i < 74 then
                      BitVec.ofNat (edgeCount 12) 19419767952545677312
                    else
                      if i < 75 then
                        BitVec.ofNat (edgeCount 12) 19527854343602569216
                      else
                        BitVec.ofNat (edgeCount 12) 20500631863114596352
              else
                if i < 81 then
                  if i < 78 then
                    if i < 77 then
                      BitVec.ofNat (edgeCount 12) 20536660660133560320
                    else
                      BitVec.ofNat (edgeCount 12) 22770446075309326336
                  else
                    if i < 79 then
                      BitVec.ofNat (edgeCount 12) 37434166462027661312
                    else
                      if i < 80 then
                        BitVec.ofNat (edgeCount 12) 37866512026255228928
                      else
                        BitVec.ofNat (edgeCount 12) 37974598417312120832
                else
                  if i < 84 then
                    if i < 82 then
                      BitVec.ofNat (edgeCount 12) 38947375936824147968
                    else
                      if i < 83 then
                        BitVec.ofNat (edgeCount 12) 38983404733843111936
                      else
                        BitVec.ofNat (edgeCount 12) 41217190149018877952
                  else
                    if i < 85 then
                      BitVec.ofNat (edgeCount 12) 55592680159585501184
                    else
                      if i < 86 then
                        BitVec.ofNat (edgeCount 12) 55736795347661357056
                      else
                        BitVec.ofNat (edgeCount 12) 55844881738718248960
        else
          if i < 131 then
            if i < 109 then
              if i < 98 then
                if i < 92 then
                  if i < 89 then
                    if i < 88 then
                      BitVec.ofNat (edgeCount 12) 56241198505926852608
                    else
                      BitVec.ofNat (edgeCount 12) 56277227302945816576
                  else
                    if i < 90 then
                      BitVec.ofNat (edgeCount 12) 57358091213514735616
                    else
                      if i < 91 then
                        BitVec.ofNat (edgeCount 12) 1117385357516603392
                      else
                        BitVec.ofNat (edgeCount 12) 1982076485971738624
                else
                  if i < 95 then
                    if i < 93 then
                      BitVec.ofNat (edgeCount 12) 2234278065104486400
                    else
                      if i < 94 then
                        BitVec.ofNat (edgeCount 12) 4143804307109576704
                      else
                        BitVec.ofNat (edgeCount 12) 4251890698166468608
                  else
                    if i < 96 then
                      BitVec.ofNat (edgeCount 12) 8683432731499036672
                    else
                      if i < 97 then
                        BitVec.ofNat (edgeCount 12) 8719461528518000640
                      else
                        BitVec.ofNat (edgeCount 12) 17870775971334848512
              else
                if i < 103 then
                  if i < 100 then
                    if i < 99 then
                      BitVec.ofNat (edgeCount 12) 18987668678922731520
                    else
                      BitVec.ofNat (edgeCount 12) 19275899055074443264
                  else
                    if i < 101 then
                      BitVec.ofNat (edgeCount 12) 20284705371605434368
                    else
                      if i < 102 then
                        BitVec.ofNat (edgeCount 12) 22518490786781200384
                      else
                        BitVec.ofNat (edgeCount 12) 37434412752632283136
                else
                  if i < 106 then
                    if i < 104 then
                      BitVec.ofNat (edgeCount 12) 37722643128783994880
                    else
                      if i < 105 then
                        BitVec.ofNat (edgeCount 12) 37974844707916742656
                      else
                        BitVec.ofNat (edgeCount 12) 38731449445314985984
                  else
                    if i < 107 then
                      BitVec.ofNat (edgeCount 12) 38839535836371877888
                    else
                      if i < 108 then
                        BitVec.ofNat (edgeCount 12) 40965234860490752000
                      else
                        BitVec.ofNat (edgeCount 12) 41001263657509715968
            else
              if i < 120 then
                if i < 114 then
                  if i < 111 then
                    if i < 110 then
                      BitVec.ofNat (edgeCount 12) 45540892081899175936
                    else
                      BitVec.ofNat (edgeCount 12) 55592926450190123008
                  else
                    if i < 112 then
                      BitVec.ofNat (edgeCount 12) 56025272014417690624
                    else
                      if i < 113 then
                        BitVec.ofNat (edgeCount 12) 57106135924986609664
                      else
                        BitVec.ofNat (edgeCount 12) 1135012727933108224
                else
                  if i < 117 then
                    if i < 115 then
                      BitVec.ofNat (edgeCount 12) 2215876638502027264
                    else
                      if i < 116 then
                        BitVec.ofNat (edgeCount 12) 2251905435520991232
                      else
                        BitVec.ofNat (edgeCount 12) 4485690850696757248
                  else
                    if i < 118 then
                      BitVec.ofNat (edgeCount 12) 19005296049339236352
                    else
                      if i < 119 then
                        BitVec.ofNat (edgeCount 12) 19509699207604731904
                      else
                        BitVec.ofNat (edgeCount 12) 37452040123048787968
              else
                if i < 125 then
                  if i < 122 then
                    if i < 121 then
                      BitVec.ofNat (edgeCount 12) 37956443281314283520
                    else
                      BitVec.ofNat (edgeCount 12) 37992472078333247488
                  else
                    if i < 123 then
                      BitVec.ofNat (edgeCount 12) 39073335988902166528
                    else
                      if i < 124 then
                        BitVec.ofNat (edgeCount 12) 55610553820606627840
                      else
                        BitVec.ofNat (edgeCount 12) 55826726602720411648
                else
                  if i < 128 then
                    if i < 126 then
                      BitVec.ofNat (edgeCount 12) 540959789585268736
                    else
                      if i < 127 then
                        BitVec.ofNat (edgeCount 12) 829190165736980480
                      else
                        BitVec.ofNat (edgeCount 12) 1837996482267971584
                  else
                    if i < 129 then
                      BitVec.ofNat (edgeCount 12) 4071781897443737600
                    else
                      if i < 130 then
                        BitVec.ofNat (edgeCount 12) 18699473487143108608
                      else
                        BitVec.ofNat (edgeCount 12) 18951675066275856384
          else
            if i < 153 then
              if i < 142 then
                if i < 136 then
                  if i < 133 then
                    if i < 132 then
                      BitVec.ofNat (edgeCount 12) 19131819051370676224
                    else
                      BitVec.ofNat (edgeCount 12) 19239905442427568128
                  else
                    if i < 134 then
                      BitVec.ofNat (edgeCount 12) 20212682961939595264
                    else
                      if i < 135 then
                        BitVec.ofNat (edgeCount 12) 20248711758958559232
                      else
                        BitVec.ofNat (edgeCount 12) 22482497174134325248
                else
                  if i < 139 then
                    if i < 137 then
                      BitVec.ofNat (edgeCount 12) 541487555166601216
                    else
                      if i < 138 then
                        BitVec.ofNat (edgeCount 12) 1081919510451060736
                      else
                        BitVec.ofNat (edgeCount 12) 1406178683621736448
                  else
                    if i < 140 then
                      BitVec.ofNat (edgeCount 12) 1658380262754484224
                    else
                      if i < 141 then
                        BitVec.ofNat (edgeCount 12) 3567906504759574528
                      else
                        BitVec.ofNat (edgeCount 12) 3675992895816466432
              else
                if i < 147 then
                  if i < 144 then
                    if i < 143 then
                      BitVec.ofNat (edgeCount 12) 8107534929149034496
                    else
                      BitVec.ofNat (edgeCount 12) 8143563726167998464
                  else
                    if i < 145 then
                      BitVec.ofNat (edgeCount 12) 17294878168984846336
                    else
                      if i < 146 then
                        BitVec.ofNat (edgeCount 12) 18700001252724441088
                      else
                        BitVec.ofNat (edgeCount 12) 19708807569255432192
                else
                  if i < 150 then
                    if i < 148 then
                      BitVec.ofNat (edgeCount 12) 21942592984431198208
                    else
                      if i < 149 then
                        BitVec.ofNat (edgeCount 12) 18717206410675879936
                      else
                        BitVec.ofNat (edgeCount 12) 18861321598751735808
                  else
                    if i < 151 then
                      BitVec.ofNat (edgeCount 12) 19365724757017231360
                    else
                      if i < 152 then
                        BitVec.ofNat (edgeCount 12) 1116998466862579712
                      else
                        BitVec.ofNat (edgeCount 12) 2197862377431498752
            else
              if i < 164 then
                if i < 158 then
                  if i < 155 then
                    if i < 154 then
                      BitVec.ofNat (edgeCount 12) 4467676589626228736
                    else
                      BitVec.ofNat (edgeCount 12) 18987281788268707840
                  else
                    if i < 156 then
                      BitVec.ofNat (edgeCount 12) 19491684946534203392
                    else
                      if i < 157 then
                        BitVec.ofNat (edgeCount 12) 55592539559536099328
                      else
                        BitVec.ofNat (edgeCount 12) 1117068835606757376
                else
                  if i < 161 then
                    if i < 159 then
                      BitVec.ofNat (edgeCount 12) 2125875152137748480
                    else
                      if i < 160 then
                        BitVec.ofNat (edgeCount 12) 2233961543194640384
                      else
                        BitVec.ofNat (edgeCount 12) 4359660567313514496
                  else
                    if i < 162 then
                      BitVec.ofNat (edgeCount 12) 4395689364332478464
                    else
                      if i < 163 then
                        BitVec.ofNat (edgeCount 12) 8935317788721938432
                      else
                        BitVec.ofNat (edgeCount 12) 18987352157012885504
              else
                if i < 169 then
                  if i < 166 then
                    if i < 165 then
                      BitVec.ofNat (edgeCount 12) 19419697721240453120
                    else
                      BitVec.ofNat (edgeCount 12) 19491755315278381056
                  else
                    if i < 167 then
                      BitVec.ofNat (edgeCount 12) 19527784112297345024
                    else
                      if i < 168 then
                        BitVec.ofNat (edgeCount 12) 20500561631809372160
                      else
                        BitVec.ofNat (edgeCount 12) 20536590428828336128
                else
                  if i < 172 then
                    if i < 170 then
                      BitVec.ofNat (edgeCount 12) 20608648022866264064
                    else
                      if i < 171 then
                        BitVec.ofNat (edgeCount 12) 22770375844004102144
                      else
                        BitVec.ofNat (edgeCount 12) 55592609928280276992
                  else
                    if i < 173 then
                      BitVec.ofNat (edgeCount 12) 55736725116356132864
                    else
                      if i < 174 then
                        BitVec.ofNat (edgeCount 12) 55844811507413024768
                      else
                        BitVec.ofNat (edgeCount 12) 56241128274621628416
      else
        if i < 263 then
          if i < 219 then
            if i < 197 then
              if i < 186 then
                if i < 180 then
                  if i < 177 then
                    if i < 176 then
                      BitVec.ofNat (edgeCount 12) 56277157071640592384
                    else
                      BitVec.ofNat (edgeCount 12) 57358020982209511424
                  else
                    if i < 178 then
                      BitVec.ofNat (edgeCount 12) 1117315126211379200
                    else
                      if i < 179 then
                        BitVec.ofNat (edgeCount 12) 1982006254666514432
                      else
                        BitVec.ofNat (edgeCount 12) 4143734075804352512
                else
                  if i < 183 then
                    if i < 181 then
                      BitVec.ofNat (edgeCount 12) 4215791669842280448
                    else
                      if i < 182 then
                        BitVec.ofNat (edgeCount 12) 8683362500193812480
                      else
                        BitVec.ofNat (edgeCount 12) 17870705740029624320
                  else
                    if i < 184 then
                      BitVec.ofNat (edgeCount 12) 18987598447617507328
                    else
                      if i < 185 then
                        BitVec.ofNat (edgeCount 12) 19275828823769219072
                      else
                        BitVec.ofNat (edgeCount 12) 19492001605883002880
              else
                if i < 191 then
                  if i < 188 then
                    if i < 187 then
                      BitVec.ofNat (edgeCount 12) 20284635140300210176
                    else
                      BitVec.ofNat (edgeCount 12) 20356692734338138112
                  else
                    if i < 189 then
                      BitVec.ofNat (edgeCount 12) 20608894313470885888
                    else
                      if i < 190 then
                        BitVec.ofNat (edgeCount 12) 22518420555475976192
                      else
                        BitVec.ofNat (edgeCount 12) 22626506946532868096
                else
                  if i < 194 then
                    if i < 192 then
                      BitVec.ofNat (edgeCount 12) 27094077776884400128
                    else
                      if i < 193 then
                        BitVec.ofNat (edgeCount 12) 55592856218884898816
                      else
                        BitVec.ofNat (edgeCount 12) 56025201783112466432
                  else
                    if i < 195 then
                      BitVec.ofNat (edgeCount 12) 56097259377150394368
                    else
                      if i < 196 then
                        BitVec.ofNat (edgeCount 12) 57106065693681385472
                      else
                        BitVec.ofNat (edgeCount 12) 59375879905876115456
            else
              if i < 208 then
                if i < 202 then
                  if i < 199 then
                    if i < 198 then
                      BitVec.ofNat (edgeCount 12) 540678452047511552
                    else
                      BitVec.ofNat (edgeCount 12) 973024016275079168
                  else
                    if i < 200 then
                      BitVec.ofNat (edgeCount 12) 1045081610313007104
                    else
                      if i < 201 then
                        BitVec.ofNat (edgeCount 12) 2053887926843998208
                      else
                        BitVec.ofNat (edgeCount 12) 2161974317900890112
                else
                  if i < 205 then
                    if i < 203 then
                      BitVec.ofNat (edgeCount 12) 4323702139038728192
                    else
                      if i < 204 then
                        BitVec.ofNat (edgeCount 12) 18699192149605351424
                      else
                        BitVec.ofNat (edgeCount 12) 18843307337681207296
                  else
                    if i < 206 then
                      BitVec.ofNat (edgeCount 12) 18915364931719135232
                    else
                      if i < 207 then
                        BitVec.ofNat (edgeCount 12) 19347710495946702848
                      else
                        BitVec.ofNat (edgeCount 12) 19455796887003594752
              else
                if i < 213 then
                  if i < 210 then
                    if i < 209 then
                      BitVec.ofNat (edgeCount 12) 20464603203534585856
                    else
                      BitVec.ofNat (edgeCount 12) 37145936223314903040
                  else
                    if i < 211 then
                      BitVec.ofNat (edgeCount 12) 37290051411390758912
                    else
                      if i < 212 then
                        BitVec.ofNat (edgeCount 12) 540889558280044544
                      else
                        BitVec.ofNat (edgeCount 12) 829119934431756288
                else
                  if i < 216 then
                    if i < 214 then
                      BitVec.ofNat (edgeCount 12) 1045292716545540096
                    else
                      if i < 215 then
                        BitVec.ofNat (edgeCount 12) 1081321513564504064
                      else
                        BitVec.ofNat (edgeCount 12) 1837926250962747392
                  else
                    if i < 217 then
                      BitVec.ofNat (edgeCount 12) 1909983845000675328
                    else
                      if i < 218 then
                        BitVec.ofNat (edgeCount 12) 1946012642019639296
                      else
                        BitVec.ofNat (edgeCount 12) 2162185424133423104
          else
            if i < 241 then
              if i < 230 then
                if i < 224 then
                  if i < 221 then
                    if i < 220 then
                      BitVec.ofNat (edgeCount 12) 4071711666138513408
                    else
                      BitVec.ofNat (edgeCount 12) 4107740463157477376
                  else
                    if i < 222 then
                      BitVec.ofNat (edgeCount 12) 4179798057195405312
                    else
                      if i < 223 then
                        BitVec.ofNat (edgeCount 12) 8647368887546937344
                      else
                        BitVec.ofNat (edgeCount 12) 18699403255837884416
                else
                  if i < 227 then
                    if i < 225 then
                      BitVec.ofNat (edgeCount 12) 18915576037951668224
                    else
                      if i < 226 then
                        BitVec.ofNat (edgeCount 12) 18951604834970632192
                      else
                        BitVec.ofNat (edgeCount 12) 19131748820065452032
                  else
                    if i < 228 then
                      BitVec.ofNat (edgeCount 12) 19203806414103379968
                    else
                      if i < 229 then
                        BitVec.ofNat (edgeCount 12) 19239835211122343936
                      else
                        BitVec.ofNat (edgeCount 12) 19456007993236127744
              else
                if i < 235 then
                  if i < 232 then
                    if i < 231 then
                      BitVec.ofNat (edgeCount 12) 20212612730634371072
                    else
                      BitVec.ofNat (edgeCount 12) 20248641527653335040
                  else
                    if i < 233 then
                      BitVec.ofNat (edgeCount 12) 20320699121691262976
                    else
                      if i < 234 then
                        BitVec.ofNat (edgeCount 12) 22482426942829101056
                      else
                        BitVec.ofNat (edgeCount 12) 37146147329547436032
                else
                  if i < 238 then
                    if i < 236 then
                      BitVec.ofNat (edgeCount 12) 37362320111661219840
                    else
                      if i < 237 then
                        BitVec.ofNat (edgeCount 12) 37398348908680183808
                      else
                        BitVec.ofNat (edgeCount 12) 37578492893775003648
                  else
                    if i < 239 then
                      BitVec.ofNat (edgeCount 12) 37650550487812931584
                    else
                      if i < 240 then
                        BitVec.ofNat (edgeCount 12) 37686579284831895552
                      else
                        BitVec.ofNat (edgeCount 12) 38659356804343922688
            else
              if i < 252 then
                if i < 246 then
                  if i < 243 then
                    if i < 242 then
                      BitVec.ofNat (edgeCount 12) 38695385601362886656
                    else
                      BitVec.ofNat (edgeCount 12) 55448776215181131776
                  else
                    if i < 244 then
                      BitVec.ofNat (edgeCount 12) 541417323861377024
                    else
                      if i < 245 then
                        BitVec.ofNat (edgeCount 12) 1045820482126872576
                      else
                        BitVec.ofNat (edgeCount 12) 1406108452316512256
                else
                  if i < 249 then
                    if i < 247 then
                      BitVec.ofNat (edgeCount 12) 1622281234430296064
                    else
                      if i < 248 then
                        BitVec.ofNat (edgeCount 12) 2162713189714755584
                      else
                        BitVec.ofNat (edgeCount 12) 3567836273454350336
                  else
                    if i < 250 then
                      BitVec.ofNat (edgeCount 12) 3639893867492278272
                    else
                      if i < 251 then
                        BitVec.ofNat (edgeCount 12) 3892095446625026048
                      else
                        BitVec.ofNat (edgeCount 12) 8107464697843810304
              else
                if i < 257 then
                  if i < 254 then
                    if i < 253 then
                      BitVec.ofNat (edgeCount 12) 8215551088900702208
                    else
                      BitVec.ofNat (edgeCount 12) 17294807937679622144
                  else
                    if i < 255 then
                      BitVec.ofNat (edgeCount 12) 18699931021419216896
                    else
                      if i < 256 then
                        BitVec.ofNat (edgeCount 12) 18916103803533000704
                      else
                        BitVec.ofNat (edgeCount 12) 19456535758817460224
                else
                  if i < 260 then
                    if i < 258 then
                      BitVec.ofNat (edgeCount 12) 19708737337950208000
                    else
                      if i < 259 then
                        BitVec.ofNat (edgeCount 12) 19780794931988135936
                      else
                        BitVec.ofNat (edgeCount 12) 20032996511120883712
                  else
                    if i < 261 then
                      BitVec.ofNat (edgeCount 12) 21942522753125974016
                    else
                      if i < 262 then
                        BitVec.ofNat (edgeCount 12) 22050609144182865920
                      else
                        BitVec.ofNat (edgeCount 12) 26518179974534397952
        else
          if i < 307 then
            if i < 285 then
              if i < 274 then
                if i < 268 then
                  if i < 265 then
                    if i < 264 then
                      BitVec.ofNat (edgeCount 12) 37146675095128768512
                    else
                      BitVec.ofNat (edgeCount 12) 37362847877242552320
                  else
                    if i < 266 then
                      BitVec.ofNat (edgeCount 12) 37903279832527011840
                    else
                      if i < 267 then
                        BitVec.ofNat (edgeCount 12) 38155481411659759616
                      else
                        BitVec.ofNat (edgeCount 12) 38227539005697687552
                else
                  if i < 271 then
                    if i < 269 then
                      BitVec.ofNat (edgeCount 12) 38479740584830435328
                    else
                      if i < 270 then
                        BitVec.ofNat (edgeCount 12) 40389266826835525632
                      else
                        BitVec.ofNat (edgeCount 12) 40497353217892417536
                  else
                    if i < 272 then
                      BitVec.ofNat (edgeCount 12) 44964924048243949568
                    else
                      if i < 273 then
                        BitVec.ofNat (edgeCount 12) 55449303980762464256
                      else
                        BitVec.ofNat (edgeCount 12) 55521361574800392192
              else
                if i < 279 then
                  if i < 276 then
                    if i < 275 then
                      BitVec.ofNat (edgeCount 12) 56530167891331383296
                    else
                      BitVec.ofNat (edgeCount 12) 558552113068638208
                  else
                    if i < 277 then
                      BitVec.ofNat (edgeCount 12) 1062955271334133760
                    else
                      if i < 278 then
                        BitVec.ofNat (edgeCount 12) 2179847978922016768
                      else
                        BitVec.ofNat (edgeCount 12) 18717065810626478080
                else
                  if i < 282 then
                    if i < 280 then
                      BitVec.ofNat (edgeCount 12) 55466438769969725440
                    else
                      if i < 281 then
                        BitVec.ofNat (edgeCount 12) 55790697943140401152
                      else
                        BitVec.ofNat (edgeCount 12) 558622481812815872
                  else
                    if i < 283 then
                      BitVec.ofNat (edgeCount 12) 990968046040383488
                    else
                      if i < 284 then
                        BitVec.ofNat (edgeCount 12) 1099054437097275392
                      else
                        BitVec.ofNat (edgeCount 12) 2071831956609302528
            else
              if i < 296 then
                if i < 290 then
                  if i < 287 then
                    if i < 286 then
                      BitVec.ofNat (edgeCount 12) 2107860753628266496
                    else
                      BitVec.ofNat (edgeCount 12) 4341646168804032512
                  else
                    if i < 288 then
                      BitVec.ofNat (edgeCount 12) 18717136179370655744
                    else
                      if i < 289 then
                        BitVec.ofNat (edgeCount 12) 18861251367446511616
                      else
                        BitVec.ofNat (edgeCount 12) 18933308961484439552
                else
                  if i < 293 then
                    if i < 291 then
                      BitVec.ofNat (edgeCount 12) 18969337758503403520
                    else
                      if i < 292 then
                        BitVec.ofNat (edgeCount 12) 19365654525712007168
                      else
                        BitVec.ofNat (edgeCount 12) 19473740916768899072
                  else
                    if i < 294 then
                      BitVec.ofNat (edgeCount 12) 55466509138713903104
                    else
                      if i < 295 then
                        BitVec.ofNat (edgeCount 12) 55574595529770795008
                      else
                        BitVec.ofNat (edgeCount 12) 55682681920827686912
              else
                if i < 301 then
                  if i < 298 then
                    if i < 297 then
                      BitVec.ofNat (edgeCount 12) 55718710717846650880
                    else
                      BitVec.ofNat (edgeCount 12) 56223113876112146432
                  else
                    if i < 299 then
                      BitVec.ofNat (edgeCount 12) 558868772417437696
                    else
                      if i < 300 then
                        BitVec.ofNat (edgeCount 12) 847099148569149440
                      else
                        BitVec.ofNat (edgeCount 12) 1855905465100140544
                else
                  if i < 304 then
                    if i < 302 then
                      BitVec.ofNat (edgeCount 12) 1927963059138068480
                    else
                      if i < 303 then
                        BitVec.ofNat (edgeCount 12) 4089690880275906560
                      else
                        BitVec.ofNat (edgeCount 12) 8665348101684330496
                  else
                    if i < 305 then
                      BitVec.ofNat (edgeCount 12) 18717382469975277568
                    else
                      if i < 306 then
                        BitVec.ofNat (edgeCount 12) 18933555252089061376
                      else
                        BitVec.ofNat (edgeCount 12) 19149728034202845184
          else
            if i < 329 then
              if i < 318 then
                if i < 312 then
                  if i < 309 then
                    if i < 308 then
                      BitVec.ofNat (edgeCount 12) 19221785628240773120
                    else
                      BitVec.ofNat (edgeCount 12) 19473987207373520896
                  else
                    if i < 310 then
                      BitVec.ofNat (edgeCount 12) 20230591944771764224
                    else
                      if i < 311 then
                        BitVec.ofNat (edgeCount 12) 20338678335828656128
                      else
                        BitVec.ofNat (edgeCount 12) 22500406156966494208
                else
                  if i < 315 then
                    if i < 313 then
                      BitVec.ofNat (edgeCount 12) 57088051295171903488
                    else
                      if i < 314 then
                        BitVec.ofNat (edgeCount 12) 252448350773706752
                      else
                        BitVec.ofNat (edgeCount 12) 2017859404702941184
                  else
                    if i < 316 then
                      BitVec.ofNat (edgeCount 12) 1873884954115440640
                    else
                      if i < 317 then
                        BitVec.ofNat (edgeCount 12) 4035612775253278720
                      else
                        BitVec.ofNat (edgeCount 12) 505283248604053504
              else
                if i < 323 then
                  if i < 320 then
                    if i < 319 then
                      BitVec.ofNat (edgeCount 12) 1514089565135044608
                    else
                      BitVec.ofNat (edgeCount 12) 3531702198197026816
                  else
                    if i < 321 then
                      BitVec.ofNat (edgeCount 12) 8071330622586486784
                    else
                      if i < 322 then
                        BitVec.ofNat (edgeCount 12) 16142871870369169408
                      else
                        BitVec.ofNat (edgeCount 12) 2269955087390474240
                else
                  if i < 326 then
                    if i < 324 then
                      BitVec.ofNat (edgeCount 12) 4431682908528312320
                    else
                      if i < 325 then
                        BitVec.ofNat (edgeCount 12) 8971311332917772288
                      else
                        BitVec.ofNat (edgeCount 12) 10340405619638403072
                  else
                    if i < 327 then
                      BitVec.ofNat (edgeCount 12) 11349211936169394176
                    else
                      if i < 328 then
                        BitVec.ofNat (edgeCount 12) 13582997351345160192
                      else
                        BitVec.ofNat (edgeCount 12) 28210688941044531200
            else
              if i < 340 then
                if i < 334 then
                  if i < 331 then
                    if i < 330 then
                      BitVec.ofNat (edgeCount 12) 28643034505272098816
                    else
                      BitVec.ofNat (edgeCount 12) 64815946712311922688
                  else
                    if i < 332 then
                      BitVec.ofNat (edgeCount 12) 1117068767155716096
                    else
                      if i < 333 then
                        BitVec.ofNat (edgeCount 12) 2125875083686707200
                      else
                        BitVec.ofNat (edgeCount 12) 2197932677724635136
                else
                  if i < 337 then
                    if i < 335 then
                      BitVec.ofNat (edgeCount 12) 2233961474743599104
                    else
                      if i < 336 then
                        BitVec.ofNat (edgeCount 12) 4359660498862473216
                      else
                        BitVec.ofNat (edgeCount 12) 4395689295881437184
                  else
                    if i < 338 then
                      BitVec.ofNat (edgeCount 12) 4467746889919365120
                    else
                      if i < 339 then
                        BitVec.ofNat (edgeCount 12) 8935317720270897152
                      else
                        BitVec.ofNat (edgeCount 12) 9763980051707068416
              else
                if i < 345 then
                  if i < 342 then
                    if i < 341 then
                      BitVec.ofNat (edgeCount 12) 10196325615934636032
                    else
                      BitVec.ofNat (edgeCount 12) 10268383209972563968
                  else
                    if i < 343 then
                      BitVec.ofNat (edgeCount 12) 10304412006991527936
                    else
                      if i < 344 then
                        BitVec.ofNat (edgeCount 12) 11277189526503555072
                      else
                        BitVec.ofNat (edgeCount 12) 11385275917560446976
                else
                  if i < 348 then
                    if i < 346 then
                      BitVec.ofNat (edgeCount 12) 18987352088561844224
                    else
                      if i < 347 then
                        BitVec.ofNat (edgeCount 12) 19419697652789411840
                      else
                        BitVec.ofNat (edgeCount 12) 19527784043846303744
                  else
                    if i < 349 then
                      BitVec.ofNat (edgeCount 12) 20536590360377294848
                    else
                      if i < 350 then
                        BitVec.ofNat (edgeCount 12) 27922493749264908288
                      else
                        BitVec.ofNat (edgeCount 12) 28066608937340764160
    else
      if i < 526 then
        if i < 438 then
          if i < 394 then
            if i < 372 then
              if i < 361 then
                if i < 356 then
                  if i < 353 then
                    if i < 352 then
                      BitVec.ofNat (edgeCount 12) 28174695328397656064
                    else
                      BitVec.ofNat (edgeCount 12) 37434096162271395840
                  else
                    if i < 354 then
                      BitVec.ofNat (edgeCount 12) 37866441726498963456
                    else
                      if i < 355 then
                        BitVec.ofNat (edgeCount 12) 37938499320536891392
                      else
                        BitVec.ofNat (edgeCount 12) 38947305637067882496
                else
                  if i < 358 then
                    if i < 357 then
                      BitVec.ofNat (edgeCount 12) 46369237822974459904
                    else
                      BitVec.ofNat (edgeCount 12) 46585410605088243712
                  else
                    if i < 359 then
                      BitVec.ofNat (edgeCount 12) 55592609859829235712
                    else
                      if i < 360 then
                        BitVec.ofNat (edgeCount 12) 55736725047905091584
                      else
                        BitVec.ofNat (edgeCount 12) 1117315057760337920
              else
                if i < 366 then
                  if i < 363 then
                    if i < 362 then
                      BitVec.ofNat (edgeCount 12) 1982006186215473152
                    else
                      BitVec.ofNat (edgeCount 12) 2198178968329256960
                  else
                    if i < 364 then
                      BitVec.ofNat (edgeCount 12) 4143734007353311232
                    else
                      if i < 365 then
                        BitVec.ofNat (edgeCount 12) 4215791601391239168
                      else
                        BitVec.ofNat (edgeCount 12) 4467993180523986944
                else
                  if i < 369 then
                    if i < 367 then
                      BitVec.ofNat (edgeCount 12) 8683362431742771200
                    else
                      if i < 368 then
                        BitVec.ofNat (edgeCount 12) 8791448822799663104
                      else
                        BitVec.ofNat (edgeCount 12) 9764226342311690240
                  else
                    if i < 370 then
                      BitVec.ofNat (edgeCount 12) 10052456718463401984
                    else
                      if i < 371 then
                        BitVec.ofNat (edgeCount 12) 10268629500577185792
                      else
                        BitVec.ofNat (edgeCount 12) 11061263034994393088
            else
              if i < 383 then
                if i < 377 then
                  if i < 374 then
                    if i < 373 then
                      BitVec.ofNat (edgeCount 12) 11133320629032321024
                    else
                      BitVec.ofNat (edgeCount 12) 13295048450170159104
                  else
                    if i < 375 then
                      BitVec.ofNat (edgeCount 12) 27922740039869530112
                    else
                      if i < 376 then
                        BitVec.ofNat (edgeCount 12) 28355085604097097728
                      else
                        BitVec.ofNat (edgeCount 12) 37434342452876017664
                else
                  if i < 380 then
                    if i < 378 then
                      BitVec.ofNat (edgeCount 12) 37722572829027729408
                    else
                      if i < 379 then
                        BitVec.ofNat (edgeCount 12) 37938745611141513216
                      else
                        BitVec.ofNat (edgeCount 12) 38731379145558720512
                  else
                    if i < 381 then
                      BitVec.ofNat (edgeCount 12) 38803436739596648448
                    else
                      if i < 382 then
                        BitVec.ofNat (edgeCount 12) 39055638318729396224
                      else
                        BitVec.ofNat (edgeCount 12) 40965164560734486528
              else
                if i < 388 then
                  if i < 385 then
                    if i < 384 then
                      BitVec.ofNat (edgeCount 12) 41073250951791378432
                    else
                      BitVec.ofNat (edgeCount 12) 45540821782142910464
                  else
                    if i < 386 then
                      BitVec.ofNat (edgeCount 12) 46369484113579081728
                    else
                      if i < 387 then
                        BitVec.ofNat (edgeCount 12) 46585656895692865536
                      else
                        BitVec.ofNat (edgeCount 12) 46801829677806649344
                else
                  if i < 391 then
                    if i < 389 then
                      BitVec.ofNat (edgeCount 12) 46873887271844577280
                    else
                      if i < 390 then
                        BitVec.ofNat (edgeCount 12) 47882693588375568384
                      else
                        BitVec.ofNat (edgeCount 12) 64672112999212777472
                  else
                    if i < 392 then
                      BitVec.ofNat (edgeCount 12) 1125935228922101760
                    else
                      if i < 393 then
                        BitVec.ofNat (edgeCount 12) 2206799139491020800
                      else
                        BitVec.ofNat (edgeCount 12) 2242827936509984768
          else
            if i < 416 then
              if i < 405 then
                if i < 399 then
                  if i < 396 then
                    if i < 395 then
                      BitVec.ofNat (edgeCount 12) 4476613351685750784
                    else
                      BitVec.ofNat (edgeCount 12) 9772846513473454080
                  else
                    if i < 397 then
                      BitVec.ofNat (edgeCount 12) 10277249671738949632
                    else
                      if i < 398 then
                        BitVec.ofNat (edgeCount 12) 18996218550328229888
                      else
                        BitVec.ofNat (edgeCount 12) 19536650505612689408
                else
                  if i < 402 then
                    if i < 400 then
                      BitVec.ofNat (edgeCount 12) 27931360211031293952
                    else
                      if i < 401 then
                        BitVec.ofNat (edgeCount 12) 46378104284740845568
                      else
                        BitVec.ofNat (edgeCount 12) 46594277066854629376
                  else
                    if i < 403 then
                      BitVec.ofNat (edgeCount 12) 64680733170374541312
                    else
                      if i < 404 then
                        BitVec.ofNat (edgeCount 12) 540678383596470272
                      else
                        BitVec.ofNat (edgeCount 12) 973023947824037888
              else
                if i < 410 then
                  if i < 407 then
                    if i < 406 then
                      BitVec.ofNat (edgeCount 12) 1045081541861965824
                    else
                      BitVec.ofNat (edgeCount 12) 2053887858392956928
                  else
                    if i < 408 then
                      BitVec.ofNat (edgeCount 12) 2161974249449848832
                    else
                      if i < 409 then
                        BitVec.ofNat (edgeCount 12) 4323702070587686912
                      else
                        BitVec.ofNat (edgeCount 12) 9475820044299534336
                else
                  if i < 413 then
                    if i < 411 then
                      BitVec.ofNat (edgeCount 12) 9619935232375390208
                    else
                      if i < 412 then
                        BitVec.ofNat (edgeCount 12) 9691992826413318144
                      else
                        BitVec.ofNat (edgeCount 12) 9728021623432282112
                  else
                    if i < 414 then
                      BitVec.ofNat (edgeCount 12) 10124338390640885760
                    else
                      if i < 415 then
                        BitVec.ofNat (edgeCount 12) 10160367187659849728
                      else
                        BitVec.ofNat (edgeCount 12) 10232424781697777664
            else
              if i < 427 then
                if i < 421 then
                  if i < 418 then
                    if i < 417 then
                      BitVec.ofNat (edgeCount 12) 11241231098228768768
                    else
                      BitVec.ofNat (edgeCount 12) 27778448929933230080
                  else
                    if i < 419 then
                      BitVec.ofNat (edgeCount 12) 27850506523971158016
                    else
                      if i < 420 then
                        BitVec.ofNat (edgeCount 12) 27994621712047013888
                      else
                        BitVec.ofNat (edgeCount 12) 28102708103103905792
                else
                  if i < 424 then
                    if i < 422 then
                      BitVec.ofNat (edgeCount 12) 28535053667331473408
                    else
                      if i < 423 then
                        BitVec.ofNat (edgeCount 12) 37145936154863861760
                      else
                        BitVec.ofNat (edgeCount 12) 37290051342939717632
                  else
                    if i < 425 then
                      BitVec.ofNat (edgeCount 12) 46225193003642781696
                    else
                      if i < 426 then
                        BitVec.ofNat (edgeCount 12) 46297250597680709632
                      else
                        BitVec.ofNat (edgeCount 12) 46333279394699673600
              else
                if i < 432 then
                  if i < 429 then
                    if i < 428 then
                      BitVec.ofNat (edgeCount 12) 46441365785756565504
                    else
                      BitVec.ofNat (edgeCount 12) 46477394582775529472
                  else
                    if i < 430 then
                      BitVec.ofNat (edgeCount 12) 64599879483314405376
                    else
                      if i < 431 then
                        BitVec.ofNat (edgeCount 12) 64707965874371297280
                      else
                        BitVec.ofNat (edgeCount 12) 64852081062447153152
                else
                  if i < 435 then
                    if i < 433 then
                      BitVec.ofNat (edgeCount 12) 540889489829003264
                    else
                      if i < 434 then
                        BitVec.ofNat (edgeCount 12) 829119865980715008
                      else
                        BitVec.ofNat (edgeCount 12) 1045292648094498816
                  else
                    if i < 436 then
                      BitVec.ofNat (edgeCount 12) 1081321445113462784
                    else
                      if i < 437 then
                        BitVec.ofNat (edgeCount 12) 1837926182511706112
                      else
                        BitVec.ofNat (edgeCount 12) 1909983776549634048
        else
          if i < 482 then
            if i < 460 then
              if i < 449 then
                if i < 443 then
                  if i < 440 then
                    if i < 439 then
                      BitVec.ofNat (edgeCount 12) 1946012573568598016
                    else
                      BitVec.ofNat (edgeCount 12) 2162185355682381824
                  else
                    if i < 441 then
                      BitVec.ofNat (edgeCount 12) 4071711597687472128
                    else
                      if i < 442 then
                        BitVec.ofNat (edgeCount 12) 4107740394706436096
                      else
                        BitVec.ofNat (edgeCount 12) 4179797988744364032
                else
                  if i < 446 then
                    if i < 444 then
                      BitVec.ofNat (edgeCount 12) 8647368819095896064
                    else
                      if i < 445 then
                        BitVec.ofNat (edgeCount 12) 9476031150532067328
                      else
                        BitVec.ofNat (edgeCount 12) 9692203932645851136
                  else
                    if i < 447 then
                      BitVec.ofNat (edgeCount 12) 9728232729664815104
                    else
                      if i < 448 then
                        BitVec.ofNat (edgeCount 12) 9908376714759634944
                      else
                        BitVec.ofNat (edgeCount 12) 9980434308797562880
              else
                if i < 454 then
                  if i < 451 then
                    if i < 450 then
                      BitVec.ofNat (edgeCount 12) 10016463105816526848
                    else
                      BitVec.ofNat (edgeCount 12) 10232635887930310656
                  else
                    if i < 452 then
                      BitVec.ofNat (edgeCount 12) 10989240625328553984
                    else
                      if i < 453 then
                        BitVec.ofNat (edgeCount 12) 11025269422347517952
                      else
                        BitVec.ofNat (edgeCount 12) 11097327016385445888
                else
                  if i < 457 then
                    if i < 455 then
                      BitVec.ofNat (edgeCount 12) 13259054837523283968
                    else
                      if i < 456 then
                        BitVec.ofNat (edgeCount 12) 18699403187386843136
                      else
                        BitVec.ofNat (edgeCount 12) 18951604766519590912
                  else
                    if i < 458 then
                      BitVec.ofNat (edgeCount 12) 19131748751614410752
                    else
                      if i < 459 then
                        BitVec.ofNat (edgeCount 12) 19239835142671302656
                      else
                        BitVec.ofNat (edgeCount 12) 20248641459202293760
            else
              if i < 471 then
                if i < 465 then
                  if i < 462 then
                    if i < 461 then
                      BitVec.ofNat (edgeCount 12) 27778660036165763072
                    else
                      BitVec.ofNat (edgeCount 12) 27886746427222654976
                  else
                    if i < 463 then
                      BitVec.ofNat (edgeCount 12) 28319091991450222592
                    else
                      if i < 464 then
                        BitVec.ofNat (edgeCount 12) 37146147261096394752
                      else
                        BitVec.ofNat (edgeCount 12) 37362320043210178560
                else
                  if i < 468 then
                    if i < 466 then
                      BitVec.ofNat (edgeCount 12) 37398348840229142528
                    else
                      if i < 467 then
                        BitVec.ofNat (edgeCount 12) 37578492825323962368
                      else
                        BitVec.ofNat (edgeCount 12) 37650550419361890304
                  else
                    if i < 469 then
                      BitVec.ofNat (edgeCount 12) 37686579216380854272
                    else
                      if i < 470 then
                        BitVec.ofNat (edgeCount 12) 38659356735892881408
                      else
                        BitVec.ofNat (edgeCount 12) 38695385532911845376
              else
                if i < 476 then
                  if i < 473 then
                    if i < 472 then
                      BitVec.ofNat (edgeCount 12) 46225404109875314688
                    else
                      BitVec.ofNat (edgeCount 12) 46297461703913242624
                  else
                    if i < 474 then
                      BitVec.ofNat (edgeCount 12) 46333490500932206592
                    else
                      if i < 475 then
                        BitVec.ofNat (edgeCount 12) 46549663283045990400
                      else
                        BitVec.ofNat (edgeCount 12) 46729807268140810240
                else
                  if i < 479 then
                    if i < 477 then
                      BitVec.ofNat (edgeCount 12) 46765836065159774208
                    else
                      if i < 478 then
                        BitVec.ofNat (edgeCount 12) 46837893659197702144
                      else
                        BitVec.ofNat (edgeCount 12) 47846699975728693248
                  else
                    if i < 480 then
                      BitVec.ofNat (edgeCount 12) 55448776146730090496
                    else
                      if i < 481 then
                        BitVec.ofNat (edgeCount 12) 55556862537786982400
                      else
                        BitVec.ofNat (edgeCount 12) 55989208102014550016
          else
            if i < 504 then
              if i < 493 then
                if i < 487 then
                  if i < 484 then
                    if i < 483 then
                      BitVec.ofNat (edgeCount 12) 64636119386565902336
                    else
                      BitVec.ofNat (edgeCount 12) 541417255410335744
                  else
                    if i < 485 then
                      BitVec.ofNat (edgeCount 12) 1045820413675831296
                    else
                      if i < 486 then
                        BitVec.ofNat (edgeCount 12) 1406108383865470976
                      else
                        BitVec.ofNat (edgeCount 12) 1622281165979254784
                else
                  if i < 490 then
                    if i < 488 then
                      BitVec.ofNat (edgeCount 12) 2162713121263714304
                    else
                      if i < 489 then
                        BitVec.ofNat (edgeCount 12) 3567836205003309056
                      else
                        BitVec.ofNat (edgeCount 12) 3639893799041236992
                  else
                    if i < 491 then
                      BitVec.ofNat (edgeCount 12) 3892095378173984768
                    else
                      if i < 492 then
                        BitVec.ofNat (edgeCount 12) 8107464629392769024
                      else
                        BitVec.ofNat (edgeCount 12) 8215551020449660928
              else
                if i < 498 then
                  if i < 495 then
                    if i < 494 then
                      BitVec.ofNat (edgeCount 12) 9476558916113399808
                    else
                      BitVec.ofNat (edgeCount 12) 9692731698227183616
                  else
                    if i < 496 then
                      BitVec.ofNat (edgeCount 12) 10485365232644390912
                    else
                      if i < 497 then
                        BitVec.ofNat (edgeCount 12) 10557422826682318848
                      else
                        BitVec.ofNat (edgeCount 12) 12719150647820156928
                else
                  if i < 501 then
                    if i < 499 then
                      BitVec.ofNat (edgeCount 12) 27779187801747095552
                    else
                      if i < 500 then
                        BitVec.ofNat (edgeCount 12) 37146675026677727232
                      else
                        BitVec.ofNat (edgeCount 12) 37362847808791511040
                  else
                    if i < 502 then
                      BitVec.ofNat (edgeCount 12) 37903279764075970560
                    else
                      if i < 503 then
                        BitVec.ofNat (edgeCount 12) 38155481343208718336
                      else
                        BitVec.ofNat (edgeCount 12) 38227538937246646272
            else
              if i < 515 then
                if i < 509 then
                  if i < 506 then
                    if i < 505 then
                      BitVec.ofNat (edgeCount 12) 38479740516379394048
                    else
                      BitVec.ofNat (edgeCount 12) 40389266758384484352
                  else
                    if i < 507 then
                      BitVec.ofNat (edgeCount 12) 40497353149441376256
                    else
                      if i < 508 then
                        BitVec.ofNat (edgeCount 12) 44964923979792908288
                      else
                        BitVec.ofNat (edgeCount 12) 46225931875456647168
                else
                  if i < 512 then
                    if i < 510 then
                      BitVec.ofNat (edgeCount 12) 46297989469494575104
                    else
                      if i < 511 then
                        BitVec.ofNat (edgeCount 12) 47306795786025566208
                      else
                        BitVec.ofNat (edgeCount 12) 549544845362855936
                  else
                    if i < 513 then
                      BitVec.ofNat (edgeCount 12) 1053948003628351488
                    else
                      if i < 514 then
                        BitVec.ofNat (edgeCount 12) 1089976800647315456
                      else
                        BitVec.ofNat (edgeCount 12) 2170840711216234496
              else
                if i < 520 then
                  if i < 517 then
                    if i < 516 then
                      BitVec.ofNat (edgeCount 12) 9484686506065920000
                    else
                      BitVec.ofNat (edgeCount 12) 9700859288179703808
                  else
                    if i < 518 then
                      BitVec.ofNat (edgeCount 12) 18708058542920695808
                    else
                      if i < 519 then
                        BitVec.ofNat (edgeCount 12) 18924231325034479616
                      else
                        BitVec.ofNat (edgeCount 12) 18960260122053443584
                else
                  if i < 523 then
                    if i < 521 then
                      BitVec.ofNat (edgeCount 12) 19464663280318939136
                    else
                      if i < 522 then
                        BitVec.ofNat (edgeCount 12) 27787315391699615744
                      else
                        BitVec.ofNat (edgeCount 12) 27859372985737543680
                  else
                    if i < 524 then
                      BitVec.ofNat (edgeCount 12) 46234059465409167360
                    else
                      if i < 525 then
                        BitVec.ofNat (edgeCount 12) 55457431502263943168
                      else
                        BitVec.ofNat (edgeCount 12) 64608745945080791040
      else
        if i < 614 then
          if i < 570 then
            if i < 548 then
              if i < 537 then
                if i < 531 then
                  if i < 528 then
                    if i < 527 then
                      BitVec.ofNat (edgeCount 12) 549615214107033600
                    else
                      BitVec.ofNat (edgeCount 12) 981960778334601216
                  else
                    if i < 529 then
                      BitVec.ofNat (edgeCount 12) 1054018372372529152
                    else
                      if i < 530 then
                        BitVec.ofNat (edgeCount 12) 1090047169391493120
                      else
                        BitVec.ofNat (edgeCount 12) 2062824688903520256
                else
                  if i < 534 then
                    if i < 532 then
                      BitVec.ofNat (edgeCount 12) 2098853485922484224
                    else
                      if i < 533 then
                        BitVec.ofNat (edgeCount 12) 2170911079960412160
                      else
                        BitVec.ofNat (edgeCount 12) 4332638901098250240
                  else
                    if i < 535 then
                      BitVec.ofNat (edgeCount 12) 9484756874810097664
                    else
                      if i < 536 then
                        BitVec.ofNat (edgeCount 12) 9628872062885953536
                      else
                        BitVec.ofNat (edgeCount 12) 9700929656923881472
              else
                if i < 542 then
                  if i < 539 then
                    if i < 538 then
                      BitVec.ofNat (edgeCount 12) 10133275221151449088
                    else
                      BitVec.ofNat (edgeCount 12) 18708128911664873472
                  else
                    if i < 540 then
                      BitVec.ofNat (edgeCount 12) 18852244099740729344
                    else
                      if i < 541 then
                        BitVec.ofNat (edgeCount 12) 18960330490797621248
                      else
                        BitVec.ofNat (edgeCount 12) 19392676055025188864
                else
                  if i < 545 then
                    if i < 543 then
                      BitVec.ofNat (edgeCount 12) 27787385760443793408
                    else
                      if i < 544 then
                        BitVec.ofNat (edgeCount 12) 46234129834153345024
                      else
                        BitVec.ofNat (edgeCount 12) 46306187428191272960
                  else
                    if i < 546 then
                      BitVec.ofNat (edgeCount 12) 46450302616267128832
                    else
                      if i < 547 then
                        BitVec.ofNat (edgeCount 12) 55457501871008120832
                      else
                        BitVec.ofNat (edgeCount 12) 55565588262065012736
            else
              if i < 559 then
                if i < 553 then
                  if i < 550 then
                    if i < 549 then
                      BitVec.ofNat (edgeCount 12) 55709703450140868608
                    else
                      BitVec.ofNat (edgeCount 12) 540643267943858176
                  else
                    if i < 551 then
                      BitVec.ofNat (edgeCount 12) 972988832171425792
                    else
                      if i < 552 then
                        BitVec.ofNat (edgeCount 12) 1045046426209353728
                      else
                        BitVec.ofNat (edgeCount 12) 1081075223228317696
                else
                  if i < 556 then
                    if i < 554 then
                      BitVec.ofNat (edgeCount 12) 2053852742740344832
                    else
                      if i < 555 then
                        BitVec.ofNat (edgeCount 12) 2089881539759308800
                      else
                        BitVec.ofNat (edgeCount 12) 2161939133797236736
                  else
                    if i < 557 then
                      BitVec.ofNat (edgeCount 12) 4323666954935074816
                    else
                      if i < 558 then
                        BitVec.ofNat (edgeCount 12) 9475784928646922240
                      else
                        BitVec.ofNat (edgeCount 12) 9619900116722778112
              else
                if i < 564 then
                  if i < 561 then
                    if i < 560 then
                      BitVec.ofNat (edgeCount 12) 9691957710760706048
                    else
                      BitVec.ofNat (edgeCount 12) 9727986507779670016
                  else
                    if i < 562 then
                      BitVec.ofNat (edgeCount 12) 10124303274988273664
                    else
                      if i < 563 then
                        BitVec.ofNat (edgeCount 12) 10160332072007237632
                      else
                        BitVec.ofNat (edgeCount 12) 10232389666045165568
                else
                  if i < 567 then
                    if i < 565 then
                      BitVec.ofNat (edgeCount 12) 18699156965501698048
                    else
                      if i < 566 then
                        BitVec.ofNat (edgeCount 12) 18843272153577553920
                      else
                        BitVec.ofNat (edgeCount 12) 18915329747615481856
                  else
                    if i < 568 then
                      BitVec.ofNat (edgeCount 12) 18951358544634445824
                    else
                      if i < 569 then
                        BitVec.ofNat (edgeCount 12) 19347675311843049472
                      else
                        BitVec.ofNat (edgeCount 12) 19383704108862013440
          else
            if i < 592 then
              if i < 581 then
                if i < 575 then
                  if i < 572 then
                    if i < 571 then
                      BitVec.ofNat (edgeCount 12) 27778413814280617984
                    else
                      BitVec.ofNat (edgeCount 12) 27850471408318545920
                  else
                    if i < 573 then
                      BitVec.ofNat (edgeCount 12) 27886500205337509888
                    else
                      if i < 574 then
                        BitVec.ofNat (edgeCount 12) 27994586596394401792
                      else
                        BitVec.ofNat (edgeCount 12) 37145901039211249664
                else
                  if i < 578 then
                    if i < 576 then
                      BitVec.ofNat (edgeCount 12) 37290016227287105536
                    else
                      if i < 577 then
                        BitVec.ofNat (edgeCount 12) 37362073821325033472
                      else
                        BitVec.ofNat (edgeCount 12) 37794419385552601088
                  else
                    if i < 579 then
                      BitVec.ofNat (edgeCount 12) 46225157887990169600
                    else
                      if i < 580 then
                        BitVec.ofNat (edgeCount 12) 46297215482028097536
                      else
                        BitVec.ofNat (edgeCount 12) 55448529924844945408
              else
                if i < 586 then
                  if i < 583 then
                    if i < 582 then
                      BitVec.ofNat (edgeCount 12) 540854374176391168
                    else
                      BitVec.ofNat (edgeCount 12) 829084750328102912
                  else
                    if i < 584 then
                      BitVec.ofNat (edgeCount 12) 1045257532441886720
                    else
                      if i < 585 then
                        BitVec.ofNat (edgeCount 12) 1081286329460850688
                      else
                        BitVec.ofNat (edgeCount 12) 1837891066859094016
                else
                  if i < 589 then
                    if i < 587 then
                      BitVec.ofNat (edgeCount 12) 1909948660897021952
                    else
                      if i < 588 then
                        BitVec.ofNat (edgeCount 12) 1945977457915985920
                      else
                        BitVec.ofNat (edgeCount 12) 2162150240029769728
                  else
                    if i < 590 then
                      BitVec.ofNat (edgeCount 12) 4071676482034860032
                    else
                      if i < 591 then
                        BitVec.ofNat (edgeCount 12) 4107705279053824000
                      else
                        BitVec.ofNat (edgeCount 12) 4179762873091751936
            else
              if i < 603 then
                if i < 597 then
                  if i < 594 then
                    if i < 593 then
                      BitVec.ofNat (edgeCount 12) 8647333703443283968
                    else
                      BitVec.ofNat (edgeCount 12) 9475996034879455232
                  else
                    if i < 595 then
                      BitVec.ofNat (edgeCount 12) 9692168816993239040
                    else
                      if i < 596 then
                        BitVec.ofNat (edgeCount 12) 9728197614012203008
                      else
                        BitVec.ofNat (edgeCount 12) 9908341599107022848
                else
                  if i < 600 then
                    if i < 598 then
                      BitVec.ofNat (edgeCount 12) 9980399193144950784
                    else
                      if i < 599 then
                        BitVec.ofNat (edgeCount 12) 10016427990163914752
                      else
                        BitVec.ofNat (edgeCount 12) 10989205509675941888
                  else
                    if i < 601 then
                      BitVec.ofNat (edgeCount 12) 11025234306694905856
                    else
                      if i < 602 then
                        BitVec.ofNat (edgeCount 12) 18699368071734231040
                      else
                        BitVec.ofNat (edgeCount 12) 18915540853848014848
              else
                if i < 608 then
                  if i < 605 then
                    if i < 604 then
                      BitVec.ofNat (edgeCount 12) 19131713635961798656
                    else
                      BitVec.ofNat (edgeCount 12) 19203771229999726592
                  else
                    if i < 606 then
                      BitVec.ofNat (edgeCount 12) 20212577546530717696
                    else
                      if i < 607 then
                        BitVec.ofNat (edgeCount 12) 27778624920513150976
                      else
                        BitVec.ofNat (edgeCount 12) 37146112145443782656
                else
                  if i < 611 then
                    if i < 609 then
                      BitVec.ofNat (edgeCount 12) 37362284927557566464
                    else
                      if i < 610 then
                        BitVec.ofNat (edgeCount 12) 37398313724576530432
                      else
                        BitVec.ofNat (edgeCount 12) 37578457709671350272
                  else
                    if i < 612 then
                      BitVec.ofNat (edgeCount 12) 37650515303709278208
                    else
                      if i < 613 then
                        BitVec.ofNat (edgeCount 12) 37686544100728242176
                      else
                        BitVec.ofNat (edgeCount 12) 37902716882842025984
        else
          if i < 658 then
            if i < 636 then
              if i < 625 then
                if i < 619 then
                  if i < 616 then
                    if i < 615 then
                      BitVec.ofNat (edgeCount 12) 38659321620240269312
                    else
                      BitVec.ofNat (edgeCount 12) 38695350417259233280
                  else
                    if i < 617 then
                      BitVec.ofNat (edgeCount 12) 38767408011297161216
                    else
                      if i < 618 then
                        BitVec.ofNat (edgeCount 12) 40929135832434999296
                      else
                        BitVec.ofNat (edgeCount 12) 46225368994222702592
                else
                  if i < 622 then
                    if i < 620 then
                      BitVec.ofNat (edgeCount 12) 46297426588260630528
                    else
                      if i < 621 then
                        BitVec.ofNat (edgeCount 12) 46333455385279594496
                      else
                        BitVec.ofNat (edgeCount 12) 46729772152488198144
                  else
                    if i < 623 then
                      BitVec.ofNat (edgeCount 12) 46765800949507162112
                    else
                      if i < 624 then
                        BitVec.ofNat (edgeCount 12) 55448741031077478400
                      else
                        BitVec.ofNat (edgeCount 12) 55520798625115406336
              else
                if i < 630 then
                  if i < 627 then
                    if i < 626 then
                      BitVec.ofNat (edgeCount 12) 55953144189342973952
                    else
                      BitVec.ofNat (edgeCount 12) 549509729710243840
                  else
                    if i < 628 then
                      BitVec.ofNat (edgeCount 12) 1053912887975739392
                    else
                      if i < 629 then
                        BitVec.ofNat (edgeCount 12) 2170805595563622400
                      else
                        BitVec.ofNat (edgeCount 12) 9484651390413307904
                else
                  if i < 633 then
                    if i < 631 then
                      BitVec.ofNat (edgeCount 12) 9700824172527091712
                    else
                      if i < 632 then
                        BitVec.ofNat (edgeCount 12) 18708023427268083712
                      else
                        BitVec.ofNat (edgeCount 12) 27787280276047003648
                  else
                    if i < 634 then
                      BitVec.ofNat (edgeCount 12) 252694366768857088
                    else
                      if i < 635 then
                        BitVec.ofNat (edgeCount 12) 9656210388718452736
                      else
                        BitVec.ofNat (edgeCount 12) 9944440764870164480
            else
              if i < 647 then
                if i < 641 then
                  if i < 638 then
                    if i < 637 then
                      BitVec.ofNat (edgeCount 12) 10953247081401155584
                    else
                      BitVec.ofNat (edgeCount 12) 19059726410668048384
                  else
                    if i < 639 then
                      BitVec.ofNat (edgeCount 12) 27706637695219400704
                    else
                      if i < 640 then
                        BitVec.ofNat (edgeCount 12) 27814724086276292608
                      else
                        BitVec.ofNat (edgeCount 12) 28247069650503860224
                else
                  if i < 644 then
                    if i < 642 then
                      BitVec.ofNat (edgeCount 12) 505388527110848512
                    else
                      if i < 643 then
                        BitVec.ofNat (edgeCount 12) 1009791685376344064
                      else
                        BitVec.ofNat (edgeCount 12) 1261993264509091840
                  else
                    if i < 645 then
                      BitVec.ofNat (edgeCount 12) 1370079655565983744
                    else
                      if i < 646 then
                        BitVec.ofNat (edgeCount 12) 1586252437679767552
                      else
                        BitVec.ofNat (edgeCount 12) 3531807476703821824
              else
                if i < 652 then
                  if i < 649 then
                    if i < 648 then
                      BitVec.ofNat (edgeCount 12) 3603865070741749760
                    else
                      BitVec.ofNat (edgeCount 12) 8071435901093281792
                  else
                    if i < 650 then
                      BitVec.ofNat (edgeCount 12) 9332443796757020672
                    else
                      if i < 651 then
                        BitVec.ofNat (edgeCount 12) 9440530187813912576
                      else
                        BitVec.ofNat (edgeCount 12) 10449336504344903680
                else
                  if i < 655 then
                    if i < 653 then
                      BitVec.ofNat (edgeCount 12) 18555815833611796480
                    else
                      if i < 654 then
                        BitVec.ofNat (edgeCount 12) 19636679744180715520
                      else
                        BitVec.ofNat (edgeCount 12) 27751286663400128512
                  else
                    if i < 656 then
                      BitVec.ofNat (edgeCount 12) 261420091046887424
                    else
                      if i < 657 then
                        BitVec.ofNat (edgeCount 12) 9340676939825807360
                      else
                        BitVec.ofNat (edgeCount 12) 18636106570718511104
          else
            if i < 680 then
              if i < 669 then
                if i < 663 then
                  if i < 660 then
                    if i < 659 then
                      BitVec.ofNat (edgeCount 12) 18780221758794366976
                    else
                      BitVec.ofNat (edgeCount 12) 540643474102288384
                  else
                    if i < 661 then
                      BitVec.ofNat (edgeCount 12) 972989038329856000
                    else
                      if i < 662 then
                        BitVec.ofNat (edgeCount 12) 1081075429386747904
                      else
                        BitVec.ofNat (edgeCount 12) 2053852948898775040
                else
                  if i < 666 then
                    if i < 664 then
                      BitVec.ofNat (edgeCount 12) 2089881745917739008
                    else
                      if i < 665 then
                        BitVec.ofNat (edgeCount 12) 4323667161093505024
                      else
                        BitVec.ofNat (edgeCount 12) 9475785134805352448
                  else
                    if i < 667 then
                      BitVec.ofNat (edgeCount 12) 9619900322881208320
                    else
                      if i < 668 then
                        BitVec.ofNat (edgeCount 12) 10124303481146703872
                      else
                        BitVec.ofNat (edgeCount 12) 18699157171660128256
              else
                if i < 674 then
                  if i < 671 then
                    if i < 670 then
                      BitVec.ofNat (edgeCount 12) 18843272359735984128
                    else
                      BitVec.ofNat (edgeCount 12) 18951358750792876032
                  else
                    if i < 672 then
                      BitVec.ofNat (edgeCount 12) 19383704315020443648
                    else
                      if i < 673 then
                        BitVec.ofNat (edgeCount 12) 27778414020439048192
                      else
                        BitVec.ofNat (edgeCount 12) 55556616522060267520
                else
                  if i < 677 then
                    if i < 675 then
                      BitVec.ofNat (edgeCount 12) 540784211590643712
                    else
                      if i < 676 then
                        BitVec.ofNat (edgeCount 12) 829014587742355456
                      else
                        BitVec.ofNat (edgeCount 12) 1045187369856139264
                  else
                    if i < 678 then
                      BitVec.ofNat (edgeCount 12) 1081216166875103232
                    else
                      if i < 679 then
                        BitVec.ofNat (edgeCount 12) 1837820904273346560
                      else
                        BitVec.ofNat (edgeCount 12) 1909878498311274496
            else
              if i < 691 then
                if i < 685 then
                  if i < 682 then
                    if i < 681 then
                      BitVec.ofNat (edgeCount 12) 1945907295330238464
                    else
                      BitVec.ofNat (edgeCount 12) 2162080077444022272
                  else
                    if i < 683 then
                      BitVec.ofNat (edgeCount 12) 4071606319449112576
                    else
                      if i < 684 then
                        BitVec.ofNat (edgeCount 12) 4107635116468076544
                      else
                        BitVec.ofNat (edgeCount 12) 4179692710506004480
                else
                  if i < 688 then
                    if i < 686 then
                      BitVec.ofNat (edgeCount 12) 8647263540857536512
                    else
                      if i < 687 then
                        BitVec.ofNat (edgeCount 12) 9475925872293707776
                      else
                        BitVec.ofNat (edgeCount 12) 9692098654407491584
                  else
                    if i < 689 then
                      BitVec.ofNat (edgeCount 12) 9908271436521275392
                    else
                      if i < 690 then
                        BitVec.ofNat (edgeCount 12) 9980329030559203328
                      else
                        BitVec.ofNat (edgeCount 12) 10989135347090194432
              else
                if i < 696 then
                  if i < 693 then
                    if i < 692 then
                      BitVec.ofNat (edgeCount 12) 18699297909148483584
                    else
                      BitVec.ofNat (edgeCount 12) 18843413097224339456
                  else
                    if i < 694 then
                      BitVec.ofNat (edgeCount 12) 18915470691262267392
                    else
                      if i < 695 then
                        BitVec.ofNat (edgeCount 12) 18951499488281231360
                      else
                        BitVec.ofNat (edgeCount 12) 19131643473376051200
                else
                  if i < 699 then
                    if i < 697 then
                      BitVec.ofNat (edgeCount 12) 19203701067413979136
                    else
                      if i < 698 then
                        BitVec.ofNat (edgeCount 12) 19239729864432943104
                      else
                        BitVec.ofNat (edgeCount 12) 19347816255489835008
                  else
                    if i < 700 then
                      BitVec.ofNat (edgeCount 12) 19383845052508798976
                    else
                      if i < 701 then
                        BitVec.ofNat (edgeCount 12) 19455902646546726912
                      else
                        BitVec.ofNat (edgeCount 12) 20212507383944970240
  else
    if i < 1053 then
      if i < 877 then
        if i < 789 then
          if i < 745 then
            if i < 723 then
              if i < 712 then
                if i < 707 then
                  if i < 704 then
                    if i < 703 then
                      BitVec.ofNat (edgeCount 12) 20248536180963934208
                    else
                      BitVec.ofNat (edgeCount 12) 20320593775001862144
                  else
                    if i < 705 then
                      BitVec.ofNat (edgeCount 12) 20464708963077718016
                    else
                      if i < 706 then
                        BitVec.ofNat (edgeCount 12) 22482321596139700224
                      else
                        BitVec.ofNat (edgeCount 12) 27778554757927403520
                else
                  if i < 709 then
                    if i < 708 then
                      BitVec.ofNat (edgeCount 12) 27850612351965331456
                    else
                      BitVec.ofNat (edgeCount 12) 27994727540041187328
                  else
                    if i < 710 then
                      BitVec.ofNat (edgeCount 12) 28282957916192899072
                    else
                      if i < 711 then
                        BitVec.ofNat (edgeCount 12) 55448670868491730944
                      else
                        BitVec.ofNat (edgeCount 12) 55520728462529658880
              else
                if i < 717 then
                  if i < 714 then
                    if i < 713 then
                      BitVec.ofNat (edgeCount 12) 55556757259548622848
                    else
                      BitVec.ofNat (edgeCount 12) 55772930041662406656
                  else
                    if i < 715 then
                      BitVec.ofNat (edgeCount 12) 55953074026757226496
                    else
                      if i < 716 then
                        BitVec.ofNat (edgeCount 12) 55989102823776190464
                      else
                        BitVec.ofNat (edgeCount 12) 56061160417814118400
                else
                  if i < 720 then
                    if i < 718 then
                      BitVec.ofNat (edgeCount 12) 57069966734345109504
                    else
                      if i < 719 then
                        BitVec.ofNat (edgeCount 12) 64599985311308578816
                      else
                        BitVec.ofNat (edgeCount 12) 541276792799887360
                  else
                    if i < 721 then
                      BitVec.ofNat (edgeCount 12) 1081708748084346880
                    else
                      if i < 722 then
                        BitVec.ofNat (edgeCount 12) 1405967921255022592
                      else
                        BitVec.ofNat (edgeCount 12) 1550083109330878464
            else
              if i < 734 then
                if i < 728 then
                  if i < 725 then
                    if i < 724 then
                      BitVec.ofNat (edgeCount 12) 1658169500387770368
                    else
                      BitVec.ofNat (edgeCount 12) 3567695742392860672
                  else
                    if i < 726 then
                      BitVec.ofNat (edgeCount 12) 3675782133449752576
                    else
                      if i < 727 then
                        BitVec.ofNat (edgeCount 12) 3819897321525608448
                      else
                        BitVec.ofNat (edgeCount 12) 8107324166782320640
                else
                  if i < 731 then
                    if i < 729 then
                      BitVec.ofNat (edgeCount 12) 8143352963801284608
                    else
                      if i < 730 then
                        BitVec.ofNat (edgeCount 12) 9476418453502951424
                      else
                        BitVec.ofNat (edgeCount 12) 9620533641578807296
                  else
                    if i < 732 then
                      BitVec.ofNat (edgeCount 12) 10485224770033942528
                    else
                      if i < 733 then
                        BitVec.ofNat (edgeCount 12) 12719010185209708544
                      else
                        BitVec.ofNat (edgeCount 12) 18699790490357727232
              else
                if i < 739 then
                  if i < 736 then
                    if i < 735 then
                      BitVec.ofNat (edgeCount 12) 18843905678433583104
                    else
                      BitVec.ofNat (edgeCount 12) 18951992069490475008
                  else
                    if i < 737 then
                      BitVec.ofNat (edgeCount 12) 19348308836699078656
                    else
                      if i < 738 then
                        BitVec.ofNat (edgeCount 12) 19384337633718042624
                      else
                        BitVec.ofNat (edgeCount 12) 19708596806888718336
                else
                  if i < 742 then
                    if i < 740 then
                      BitVec.ofNat (edgeCount 12) 19816683197945610240
                    else
                      if i < 741 then
                        BitVec.ofNat (edgeCount 12) 19924769589002502144
                      else
                        BitVec.ofNat (edgeCount 12) 19960798386021466112
                  else
                    if i < 743 then
                      BitVec.ofNat (edgeCount 12) 20465201544286961664
                    else
                      if i < 744 then
                        BitVec.ofNat (edgeCount 12) 21942382222064484352
                      else
                        BitVec.ofNat (edgeCount 12) 21978411019083448320
          else
            if i < 767 then
              if i < 756 then
                if i < 750 then
                  if i < 747 then
                    if i < 746 then
                      BitVec.ofNat (edgeCount 12) 22194583801197232128
                    else
                      BitVec.ofNat (edgeCount 12) 26518039443472908288
                  else
                    if i < 748 then
                      BitVec.ofNat (edgeCount 12) 27779047339136647168
                    else
                      if i < 749 then
                        BitVec.ofNat (edgeCount 12) 27995220121250430976
                      else
                        BitVec.ofNat (edgeCount 12) 28859911249705566208
                else
                  if i < 753 then
                    if i < 751 then
                      BitVec.ofNat (edgeCount 12) 55449163449700974592
                    else
                      if i < 752 then
                        BitVec.ofNat (edgeCount 12) 55557249840757866496
                      else
                        BitVec.ofNat (edgeCount 12) 55701365028833722368
                  else
                    if i < 754 then
                      BitVec.ofNat (edgeCount 12) 56530027360269893632
                    else
                      if i < 755 then
                        BitVec.ofNat (edgeCount 12) 56566056157288857600
                      else
                        BitVec.ofNat (edgeCount 12) 58799841572464623616
              else
                if i < 761 then
                  if i < 758 then
                    if i < 757 then
                      BitVec.ofNat (edgeCount 12) 64600477892517822464
                    else
                      BitVec.ofNat (edgeCount 12) 252448282322665472
                  else
                    if i < 759 then
                      BitVec.ofNat (edgeCount 12) 9439791522158477312
                    else
                      if i < 760 then
                        BitVec.ofNat (edgeCount 12) 18663163559013253120
                      else
                        BitVec.ofNat (edgeCount 12) 18771249950070145024
                else
                  if i < 764 then
                    if i < 762 then
                      BitVec.ofNat (edgeCount 12) 19311681905354604544
                    else
                      if i < 763 then
                        BitVec.ofNat (edgeCount 12) 27706391610773209088
                      else
                        BitVec.ofNat (edgeCount 12) 27958593189905956864
                  else
                    if i < 765 then
                      BitVec.ofNat (edgeCount 12) 252589019811020800
                    else
                      if i < 766 then
                        BitVec.ofNat (edgeCount 12) 9656105041760616448
                      else
                        BitVec.ofNat (edgeCount 12) 9944335417912328192
            else
              if i < 778 then
                if i < 772 then
                  if i < 769 then
                    if i < 768 then
                      BitVec.ofNat (edgeCount 12) 18555217905444716544
                    else
                      BitVec.ofNat (edgeCount 12) 18627275499482644480
                  else
                    if i < 770 then
                      BitVec.ofNat (edgeCount 12) 18771390687558500352
                    else
                      if i < 771 then
                        BitVec.ofNat (edgeCount 12) 18879477078615392256
                      else
                        BitVec.ofNat (edgeCount 12) 19059621063710212096
                else
                  if i < 775 then
                    if i < 773 then
                      BitVec.ofNat (edgeCount 12) 19167707454767104000
                    else
                      if i < 774 then
                        BitVec.ofNat (edgeCount 12) 19311822642842959872
                      else
                        BitVec.ofNat (edgeCount 12) 20176513771298095104
                  else
                    if i < 776 then
                      BitVec.ofNat (edgeCount 12) 27706532348261564416
                    else
                      if i < 777 then
                        BitVec.ofNat (edgeCount 12) 27814618739318456320
                      else
                        BitVec.ofNat (edgeCount 12) 27958733927394312192
              else
                if i < 783 then
                  if i < 780 then
                    if i < 779 then
                      BitVec.ofNat (edgeCount 12) 28246964303546023936
                    else
                      BitVec.ofNat (edgeCount 12) 252694572927287296
                  else
                    if i < 781 then
                      BitVec.ofNat (edgeCount 12) 504896152060035072
                    else
                      if i < 782 then
                        BitVec.ofNat (edgeCount 12) 793126528211746816
                      else
                        BitVec.ofNat (edgeCount 12) 9548124203819991040
                else
                  if i < 786 then
                    if i < 784 then
                      BitVec.ofNat (edgeCount 12) 9836354579971702784
                    else
                      if i < 785 then
                        BitVec.ofNat (edgeCount 12) 18663409849617874944
                      else
                        BitVec.ofNat (edgeCount 12) 18771496240674766848
                  else
                    if i < 787 then
                      BitVec.ofNat (edgeCount 12) 19059726616826478592
                    else
                      if i < 788 then
                        BitVec.ofNat (edgeCount 12) 19311928195959226368
                      else
                        BitVec.ofNat (edgeCount 12) 20176619324414361600
        else
          if i < 833 then
            if i < 811 then
              if i < 800 then
                if i < 794 then
                  if i < 791 then
                    if i < 790 then
                      BitVec.ofNat (edgeCount 12) 27706637901377830912
                    else
                      BitVec.ofNat (edgeCount 12) 505283180153012224
                  else
                    if i < 792 then
                      BitVec.ofNat (edgeCount 12) 1369974308608147456
                    else
                      if i < 793 then
                        BitVec.ofNat (edgeCount 12) 9440424840856076288
                      else
                        BitVec.ofNat (edgeCount 12) 9584540028931932160
                else
                  if i < 797 then
                    if i < 795 then
                      BitVec.ofNat (edgeCount 12) 10088943187197427712
                    else
                      if i < 796 then
                        BitVec.ofNat (edgeCount 12) 10449231157387067392
                      else
                        BitVec.ofNat (edgeCount 12) 10665403939500851200
                  else
                    if i < 798 then
                      BitVec.ofNat (edgeCount 12) 12683016572562833408
                    else
                      if i < 799 then
                        BitVec.ofNat (edgeCount 12) 18555710486653960192
                      else
                        BitVec.ofNat (edgeCount 12) 18663796877710852096
              else
                if i < 805 then
                  if i < 802 then
                    if i < 801 then
                      BitVec.ofNat (edgeCount 12) 18771883268767744000
                    else
                      BitVec.ofNat (edgeCount 12) 19636574397222879232
                  else
                    if i < 803 then
                      BitVec.ofNat (edgeCount 12) 19672603194241843200
                    else
                      if i < 804 then
                        BitVec.ofNat (edgeCount 12) 21906388609417609216
                      else
                        BitVec.ofNat (edgeCount 12) 27707024929470808064
                else
                  if i < 808 then
                    if i < 806 then
                      BitVec.ofNat (edgeCount 12) 27743053726489772032
                    else
                      if i < 807 then
                        BitVec.ofNat (edgeCount 12) 27959226508603555840
                      else
                        BitVec.ofNat (edgeCount 12) 28823917637058691072
                  else
                    if i < 809 then
                      BitVec.ofNat (edgeCount 12) 469289567506137088
                    else
                      if i < 810 then
                        BitVec.ofNat (edgeCount 12) 901635131733704704
                      else
                        BitVec.ofNat (edgeCount 12) 1009721522790596608
            else
              if i < 822 then
                if i < 816 then
                  if i < 813 then
                    if i < 812 then
                      BitVec.ofNat (edgeCount 12) 1333980695961272320
                    else
                      BitVec.ofNat (edgeCount 12) 1478095884037128192
                  else
                    if i < 814 then
                      BitVec.ofNat (edgeCount 12) 1586182275094020096
                    else
                      if i < 815 then
                        BitVec.ofNat (edgeCount 12) 3495708517099110400
                      else
                        BitVec.ofNat (edgeCount 12) 3603794908156002304
                else
                  if i < 819 then
                    if i < 817 then
                      BitVec.ofNat (edgeCount 12) 9404431228209201152
                    else
                      if i < 818 then
                        BitVec.ofNat (edgeCount 12) 9548546416285057024
                      else
                        BitVec.ofNat (edgeCount 12) 10413237544740192256
                  else
                    if i < 820 then
                      BitVec.ofNat (edgeCount 12) 18627803265063976960
                    else
                      if i < 821 then
                        BitVec.ofNat (edgeCount 12) 18771918453139832832
                      else
                        BitVec.ofNat (edgeCount 12) 18880004844196724736
              else
                if i < 827 then
                  if i < 824 then
                    if i < 823 then
                      BitVec.ofNat (edgeCount 12) 19636609581594968064
                    else
                      BitVec.ofNat (edgeCount 12) 19744695972651859968
                  else
                    if i < 825 then
                      BitVec.ofNat (edgeCount 12) 19888811160727715840
                    else
                      if i < 826 then
                        BitVec.ofNat (edgeCount 12) 21906423793789698048
                      else
                        BitVec.ofNat (edgeCount 12) 27707060113842896896
                else
                  if i < 830 then
                    if i < 828 then
                      BitVec.ofNat (edgeCount 12) 254172316555018240
                    else
                      if i < 829 then
                        BitVec.ofNat (edgeCount 12) 398287504630874112
                      else
                        BitVec.ofNat (edgeCount 12) 506373895687766016
                  else
                    if i < 831 then
                      BitVec.ofNat (edgeCount 12) 902690662896369664
                    else
                      if i < 832 then
                        BitVec.ofNat (edgeCount 12) 938719459915333632
                      else
                        BitVec.ofNat (edgeCount 12) 2019583370484252672
          else
            if i < 855 then
              if i < 844 then
                if i < 838 then
                  if i < 835 then
                    if i < 834 then
                      BitVec.ofNat (edgeCount 12) 2415900137692856320
                    else
                      BitVec.ofNat (edgeCount 12) 2523986528749748224
                  else
                    if i < 836 then
                      BitVec.ofNat (edgeCount 12) 2632072919806640128
                    else
                      if i < 837 then
                        BitVec.ofNat (edgeCount 12) 2668101716825604096
                      else
                        BitVec.ofNat (edgeCount 12) 3172504875091099648
                else
                  if i < 841 then
                    if i < 839 then
                      BitVec.ofNat (edgeCount 12) 6955528562082316288
                    else
                      if i < 840 then
                        BitVec.ofNat (edgeCount 12) 6991557359101280256
                      else
                        BitVec.ofNat (edgeCount 12) 7207730141215064064
                  else
                    if i < 842 then
                      BitVec.ofNat (edgeCount 12) 9333429165333938176
                    else
                      if i < 843 then
                        BitVec.ofNat (edgeCount 12) 9549601947447721984
                      else
                        BitVec.ofNat (edgeCount 12) 11567214580509704192
              else
                if i < 849 then
                  if i < 846 then
                    if i < 845 then
                      BitVec.ofNat (edgeCount 12) 18556801202188713984
                    else
                      BitVec.ofNat (edgeCount 12) 18664887593245605888
                  else
                    if i < 847 then
                      BitVec.ofNat (edgeCount 12) 18772973984302497792
                    else
                      if i < 848 then
                        BitVec.ofNat (edgeCount 12) 20790586617364480000
                      else
                        BitVec.ofNat (edgeCount 12) 20826615414383443968
                else
                  if i < 852 then
                    if i < 850 then
                      BitVec.ofNat (edgeCount 12) 25366243838772903936
                    else
                      if i < 851 then
                        BitVec.ofNat (edgeCount 12) 27708115645005561856
                      else
                        BitVec.ofNat (edgeCount 12) 261314744089051136
                  else
                    if i < 853 then
                      BitVec.ofNat (edgeCount 12) 18563943629722746880
                    else
                      if i < 854 then
                        BitVec.ofNat (edgeCount 12) 18636001223760674816
                      else
                        BitVec.ofNat (edgeCount 12) 18888202802893422592
            else
              if i < 866 then
                if i < 860 then
                  if i < 857 then
                    if i < 856 then
                      BitVec.ofNat (edgeCount 12) 19320548367120990208
                    else
                      BitVec.ofNat (edgeCount 12) 27715258072539594752
                  else
                    if i < 858 then
                      BitVec.ofNat (edgeCount 12) 18564154735955279872
                    else
                      if i < 859 then
                        BitVec.ofNat (edgeCount 12) 18672241127012171776
                      else
                        BitVec.ofNat (edgeCount 12) 18780327518069063680
                else
                  if i < 863 then
                    if i < 861 then
                      BitVec.ofNat (edgeCount 12) 19104586691239739392
                    else
                      if i < 862 then
                        BitVec.ofNat (edgeCount 12) 20185450601808658432
                      else
                        BitVec.ofNat (edgeCount 12) 27715469178772127744
                  else
                    if i < 864 then
                      BitVec.ofNat (edgeCount 12) 540660722690949120
                    else
                      if i < 865 then
                        BitVec.ofNat (edgeCount 12) 973006286918516736
                      else
                        BitVec.ofNat (edgeCount 12) 1081092677975408640
              else
                if i < 871 then
                  if i < 868 then
                    if i < 867 then
                      BitVec.ofNat (edgeCount 12) 2053870197487435776
                    else
                      BitVec.ofNat (edgeCount 12) 2089898994506399744
                  else
                    if i < 869 then
                      BitVec.ofNat (edgeCount 12) 4323684409682165760
                    else
                      if i < 870 then
                        BitVec.ofNat (edgeCount 12) 9475802383394013184
                      else
                        BitVec.ofNat (edgeCount 12) 9619917571469869056
                else
                  if i < 874 then
                    if i < 872 then
                      BitVec.ofNat (edgeCount 12) 10124320729735364608
                    else
                      if i < 873 then
                        BitVec.ofNat (edgeCount 12) 27778431269027708928
                      else
                        BitVec.ofNat (edgeCount 12) 27994604051141492736
                  else
                    if i < 875 then
                      BitVec.ofNat (edgeCount 12) 37145918493958340608
                    else
                      if i < 876 then
                        BitVec.ofNat (edgeCount 12) 37290033682034196480
                      else
                        BitVec.ofNat (edgeCount 12) 37398120073091088384
      else
        if i < 965 then
          if i < 921 then
            if i < 899 then
              if i < 888 then
                if i < 882 then
                  if i < 879 then
                    if i < 878 then
                      BitVec.ofNat (edgeCount 12) 37794436840299692032
                    else
                      BitVec.ofNat (edgeCount 12) 37830465637318656000
                  else
                    if i < 880 then
                      BitVec.ofNat (edgeCount 12) 38911329547887575040
                    else
                      if i < 881 then
                        BitVec.ofNat (edgeCount 12) 46225175342737260544
                      else
                        BitVec.ofNat (edgeCount 12) 46441348124851044352
                else
                  if i < 885 then
                    if i < 883 then
                      BitVec.ofNat (edgeCount 12) 64599861822408884224
                    else
                      if i < 884 then
                        BitVec.ofNat (edgeCount 12) 504913400648695808
                      else
                        BitVec.ofNat (edgeCount 12) 793143776800407552
                  else
                    if i < 886 then
                      BitVec.ofNat (edgeCount 12) 1801950093331398656
                    else
                      if i < 887 then
                        BitVec.ofNat (edgeCount 12) 4035735508507164672
                      else
                        BitVec.ofNat (edgeCount 12) 27706655149966491648
              else
                if i < 893 then
                  if i < 890 then
                    if i < 889 then
                      BitVec.ofNat (edgeCount 12) 252623998561550336
                    else
                      BitVec.ofNat (edgeCount 12) 468796780675334144
                  else
                    if i < 891 then
                      BitVec.ofNat (edgeCount 12) 684969562789117952
                    else
                      if i < 892 then
                        BitVec.ofNat (edgeCount 12) 1009228735959793664
                      else
                        BitVec.ofNat (edgeCount 12) 1873919864414928896
                else
                  if i < 896 then
                    if i < 894 then
                      BitVec.ofNat (edgeCount 12) 4035647685552766976
                    else
                      if i < 895 then
                        BitVec.ofNat (edgeCount 12) 9331880847340470272
                      else
                        BitVec.ofNat (edgeCount 12) 37001996957904797696
                  else
                    if i < 897 then
                      BitVec.ofNat (edgeCount 12) 37074054551942725632
                    else
                      if i < 898 then
                        BitVec.ofNat (edgeCount 12) 37326256131075473408
                      else
                        BitVec.ofNat (edgeCount 12) 37506400116170293248
            else
              if i < 910 then
                if i < 904 then
                  if i < 901 then
                    if i < 900 then
                      BitVec.ofNat (edgeCount 12) 37614486507227185152
                    else
                      BitVec.ofNat (edgeCount 12) 38623292823758176256
                  else
                    if i < 902 then
                      BitVec.ofNat (edgeCount 12) 46153311400721645568
                    else
                      if i < 903 then
                        BitVec.ofNat (edgeCount 12) 252413029767970816
                      else
                        BitVec.ofNat (edgeCount 12) 396528217843826688
                else
                  if i < 907 then
                    if i < 905 then
                      BitVec.ofNat (edgeCount 12) 2017824083697205248
                    else
                      if i < 906 then
                        BitVec.ofNat (edgeCount 12) 9331669878546890752
                      else
                        BitVec.ofNat (edgeCount 12) 9403727472584818688
                  else
                    if i < 908 then
                      BitVec.ofNat (edgeCount 12) 9655929051717566464
                    else
                      if i < 909 then
                        BitVec.ofNat (edgeCount 12) 252553767256326144
                      else
                        BitVec.ofNat (edgeCount 12) 468726549370109952
              else
                if i < 915 then
                  if i < 912 then
                    if i < 911 then
                      BitVec.ofNat (edgeCount 12) 684899331483893760
                    else
                      BitVec.ofNat (edgeCount 12) 1009158504654569472
                  else
                    if i < 913 then
                      BitVec.ofNat (edgeCount 12) 1873849633109704704
                    else
                      if i < 914 then
                        BitVec.ofNat (edgeCount 12) 4035577454247542784
                      else
                        BitVec.ofNat (edgeCount 12) 9331810616035246080
                else
                  if i < 918 then
                    if i < 916 then
                      BitVec.ofNat (edgeCount 12) 9403868210073174016
                    else
                      if i < 917 then
                        BitVec.ofNat (edgeCount 12) 9656069789205921792
                      else
                        BitVec.ofNat (edgeCount 12) 18555182652890021888
                  else
                    if i < 919 then
                      BitVec.ofNat (edgeCount 12) 18663269043946913792
                    else
                      if i < 920 then
                        BitVec.ofNat (edgeCount 12) 18771355435003805696
                      else
                        BitVec.ofNat (edgeCount 12) 18807384232022769664
          else
            if i < 943 then
              if i < 932 then
                if i < 926 then
                  if i < 923 then
                    if i < 922 then
                      BitVec.ofNat (edgeCount 12) 18879441826060697600
                    else
                      BitVec.ofNat (edgeCount 12) 19095614608174481408
                  else
                    if i < 924 then
                      BitVec.ofNat (edgeCount 12) 19311787390288265216
                    else
                      if i < 925 then
                        BitVec.ofNat (edgeCount 12) 27706497095706869760
                      else
                        BitVec.ofNat (edgeCount 12) 27742525892725833728
                else
                  if i < 929 then
                    if i < 927 then
                      BitVec.ofNat (edgeCount 12) 27814583486763761664
                    else
                      if i < 928 then
                        BitVec.ofNat (edgeCount 12) 27958698674839617536
                      else
                        BitVec.ofNat (edgeCount 12) 28246929050991329280
                  else
                    if i < 930 then
                      BitVec.ofNat (edgeCount 12) 55376613206271197184
                    else
                      if i < 931 then
                        BitVec.ofNat (edgeCount 12) 55484699597328089088
                      else
                        BitVec.ofNat (edgeCount 12) 55917045161555656704
              else
                if i < 937 then
                  if i < 934 then
                    if i < 933 then
                      BitVec.ofNat (edgeCount 12) 64563956446107009024
                    else
                      BitVec.ofNat (edgeCount 12) 253046348465569792
                  else
                    if i < 935 then
                      BitVec.ofNat (edgeCount 12) 505247927598317568
                    else
                      if i < 936 then
                        BitVec.ofNat (edgeCount 12) 937593491825885184
                      else
                        BitVec.ofNat (edgeCount 12) 1369939056053452800
                else
                  if i < 940 then
                    if i < 938 then
                      BitVec.ofNat (edgeCount 12) 1514054244129308672
                    else
                      if i < 939 then
                        BitVec.ofNat (edgeCount 12) 2018457402394804224
                      else
                        BitVec.ofNat (edgeCount 12) 3531666877191290880
                  else
                    if i < 941 then
                      BitVec.ofNat (edgeCount 12) 3747839659305074688
                    else
                      if i < 942 then
                        BitVec.ofNat (edgeCount 12) 8071295301580750848
                      else
                        BitVec.ofNat (edgeCount 12) 9404360791282417664
            else
              if i < 954 then
                if i < 948 then
                  if i < 945 then
                    if i < 944 then
                      BitVec.ofNat (edgeCount 12) 9440389588301381632
                    else
                      BitVec.ofNat (edgeCount 12) 9584504776377237504
                  else
                    if i < 946 then
                      BitVec.ofNat (edgeCount 12) 9656562370415165440
                    else
                      if i < 947 then
                        BitVec.ofNat (edgeCount 12) 10088907934642733056
                      else
                        BitVec.ofNat (edgeCount 12) 10521253498870300672
                else
                  if i < 951 then
                    if i < 949 then
                      BitVec.ofNat (edgeCount 12) 10665368686946156544
                    else
                      if i < 950 then
                        BitVec.ofNat (edgeCount 12) 27706989676916113408
                      else
                        BitVec.ofNat (edgeCount 12) 27743018473935077376
                  else
                    if i < 952 then
                      BitVec.ofNat (edgeCount 12) 27959191256048861184
                    else
                      if i < 953 then
                        BitVec.ofNat (edgeCount 12) 28823882384503996416
                      else
                        BitVec.ofNat (edgeCount 12) 37002419307808817152
              else
                if i < 959 then
                  if i < 956 then
                    if i < 955 then
                      BitVec.ofNat (edgeCount 12) 37110505698865709056
                    else
                      BitVec.ofNat (edgeCount 12) 37218592089922600960
                  else
                    if i < 957 then
                      BitVec.ofNat (edgeCount 12) 37254620886941564928
                    else
                      if i < 958 then
                        BitVec.ofNat (edgeCount 12) 37759024045207060480
                      else
                        BitVec.ofNat (edgeCount 12) 38083283218377736192
                else
                  if i < 962 then
                    if i < 960 then
                      BitVec.ofNat (edgeCount 12) 38119312015396700160
                    else
                      if i < 961 then
                        BitVec.ofNat (edgeCount 12) 38335484797510483968
                      else
                        BitVec.ofNat (edgeCount 12) 40353097430572466176
                  else
                    if i < 963 then
                      BitVec.ofNat (edgeCount 12) 46153733750625665024
                    else
                      if i < 964 then
                        BitVec.ofNat (edgeCount 12) 46189762547644628992
                      else
                        BitVec.ofNat (edgeCount 12) 46261820141682556928
        else
          if i < 1009 then
            if i < 987 then
              if i < 976 then
                if i < 970 then
                  if i < 967 then
                    if i < 966 then
                      BitVec.ofNat (edgeCount 12) 46405935329758412800
                    else
                      BitVec.ofNat (edgeCount 12) 47270626458213548032
                  else
                    if i < 968 then
                      BitVec.ofNat (edgeCount 12) 64564449027316252672
                    else
                      if i < 969 then
                        BitVec.ofNat (edgeCount 12) 253891254432038912
                      else
                        BitVec.ofNat (edgeCount 12) 758294412697534464
                else
                  if i < 973 then
                    if i < 971 then
                      BitVec.ofNat (edgeCount 12) 2415619075569876992
                    else
                      if i < 972 then
                        BitVec.ofNat (edgeCount 12) 2487676669607804928
                      else
                        BitVec.ofNat (edgeCount 12) 6955247499959336960
                  else
                    if i < 974 then
                      BitVec.ofNat (edgeCount 12) 9333148103210958848
                    else
                      if i < 975 then
                        BitVec.ofNat (edgeCount 12) 9405205697248886784
                      else
                        BitVec.ofNat (edgeCount 12) 9657407276381634560
              else
                if i < 981 then
                  if i < 978 then
                    if i < 977 then
                      BitVec.ofNat (edgeCount 12) 9945637652533346304
                    else
                      BitVec.ofNat (edgeCount 12) 11566933518386724864
                  else
                    if i < 979 then
                      BitVec.ofNat (edgeCount 12) 11675019909443616768
                    else
                      if i < 980 then
                        BitVec.ofNat (edgeCount 12) 16142590739795148800
                      else
                        BitVec.ofNat (edgeCount 12) 27707834582882582528
                else
                  if i < 984 then
                    if i < 982 then
                      BitVec.ofNat (edgeCount 12) 28248266538167042048
                    else
                      if i < 983 then
                        BitVec.ofNat (edgeCount 12) 29977648795077312512
                      else
                        BitVec.ofNat (edgeCount 12) 64565293933282721792
                  else
                    if i < 985 then
                      BitVec.ofNat (edgeCount 12) 1117174457981468672
                    else
                      if i < 986 then
                        BitVec.ofNat (edgeCount 12) 1981865586436603904
                      else
                        BitVec.ofNat (edgeCount 12) 4143593407574441984
            else
              if i < 998 then
                if i < 992 then
                  if i < 989 then
                    if i < 988 then
                      BitVec.ofNat (edgeCount 12) 5152399724105433088
                    else
                      BitVec.ofNat (edgeCount 12) 5440630100257144832
                  else
                    if i < 990 then
                      BitVec.ofNat (edgeCount 12) 6449436416788135936
                    else
                      if i < 991 then
                        BitVec.ofNat (edgeCount 12) 8683221831963901952
                      else
                        BitVec.ofNat (edgeCount 12) 14087541384808497152
                else
                  if i < 995 then
                    if i < 993 then
                      BitVec.ofNat (edgeCount 12) 14519886949036064768
                    else
                      if i < 994 then
                        BitVec.ofNat (edgeCount 12) 540748890050134016
                      else
                        BitVec.ofNat (edgeCount 12) 828979266201845760
                  else
                    if i < 996 then
                      BitVec.ofNat (edgeCount 12) 973094454277701632
                    else
                      if i < 997 then
                        BitVec.ofNat (edgeCount 12) 1081180845334593536
                      else
                        BitVec.ofNat (edgeCount 12) 1837785582732836864
              else
                if i < 1003 then
                  if i < 1000 then
                    if i < 999 then
                      BitVec.ofNat (edgeCount 12) 1945871973789728768
                    else
                      BitVec.ofNat (edgeCount 12) 2053958364846620672
                  else
                    if i < 1001 then
                      BitVec.ofNat (edgeCount 12) 2089987161865584640
                    else
                      if i < 1002 then
                        BitVec.ofNat (edgeCount 12) 4071570997908602880
                      else
                        BitVec.ofNat (edgeCount 12) 4107599794927566848
                else
                  if i < 1006 then
                    if i < 1004 then
                      BitVec.ofNat (edgeCount 12) 4323772577041350656
                    else
                      if i < 1005 then
                        BitVec.ofNat (edgeCount 12) 4864204532325810176
                      else
                        BitVec.ofNat (edgeCount 12) 5008319720401666048
                  else
                    if i < 1007 then
                      BitVec.ofNat (edgeCount 12) 5116406111458557952
                    else
                      if i < 1008 then
                        BitVec.ofNat (edgeCount 12) 5296550096553377792
                      else
                        BitVec.ofNat (edgeCount 12) 5512722878667161600
          else
            if i < 1031 then
              if i < 1020 then
                if i < 1014 then
                  if i < 1011 then
                    if i < 1010 then
                      BitVec.ofNat (edgeCount 12) 5548751675686125568
                    else
                      BitVec.ofNat (edgeCount 12) 6377414007122296832
                  else
                    if i < 1012 then
                      BitVec.ofNat (edgeCount 12) 6629615586255044608
                    else
                      if i < 1013 then
                        BitVec.ofNat (edgeCount 12) 9475890550753198080
                      else
                        BitVec.ofNat (edgeCount 12) 9620005738829053952
                else
                  if i < 1017 then
                    if i < 1015 then
                      BitVec.ofNat (edgeCount 12) 9728092129885945856
                    else
                      if i < 1016 then
                        BitVec.ofNat (edgeCount 12) 9908236114980765696
                      else
                        BitVec.ofNat (edgeCount 12) 10016322506037657600
                  else
                    if i < 1018 then
                      BitVec.ofNat (edgeCount 12) 10160437694113513472
                    else
                      if i < 1019 then
                        BitVec.ofNat (edgeCount 12) 11025128822568648704
                      else
                        BitVec.ofNat (edgeCount 12) 13943461381104730112
              else
                if i < 1025 then
                  if i < 1022 then
                    if i < 1021 then
                      BitVec.ofNat (edgeCount 12) 14195662960237477888
                    else
                      BitVec.ofNat (edgeCount 12) 27886605827443785728
                  else
                    if i < 1023 then
                      BitVec.ofNat (edgeCount 12) 37146006661317525504
                    else
                      if i < 1024 then
                        BitVec.ofNat (edgeCount 12) 37290121849393381376
                      else
                        BitVec.ofNat (edgeCount 12) 37578352225545093120
                else
                  if i < 1028 then
                    if i < 1026 then
                      BitVec.ofNat (edgeCount 12) 37794525007658876928
                    else
                      if i < 1027 then
                        BitVec.ofNat (edgeCount 12) 38659216136114012160
                      else
                        BitVec.ofNat (edgeCount 12) 41829750273782841344
                  else
                    if i < 1029 then
                      BitVec.ofNat (edgeCount 12) 46225263510096445440
                    else
                      if i < 1030 then
                        BitVec.ofNat (edgeCount 12) 541276655631466496
                      else
                        BitVec.ofNat (edgeCount 12) 973622219859034112
            else
              if i < 1042 then
                if i < 1036 then
                  if i < 1033 then
                    if i < 1032 then
                      BitVec.ofNat (edgeCount 12) 1405967784086601728
                    else
                      BitVec.ofNat (edgeCount 12) 1550082972162457600
                  else
                    if i < 1034 then
                      BitVec.ofNat (edgeCount 12) 2054486130427953152
                    else
                      if i < 1035 then
                        BitVec.ofNat (edgeCount 12) 3567695605224439808
                      else
                        BitVec.ofNat (edgeCount 12) 3783868387338223616
                else
                  if i < 1039 then
                    if i < 1037 then
                      BitVec.ofNat (edgeCount 12) 4324300342622683136
                    else
                      if i < 1038 then
                        BitVec.ofNat (edgeCount 12) 4864732297907142656
                      else
                        BitVec.ofNat (edgeCount 12) 5008847485982998528
                  else
                    if i < 1040 then
                      BitVec.ofNat (edgeCount 12) 5513250644248494080
                    else
                      if i < 1041 then
                        BitVec.ofNat (edgeCount 12) 5873538614438133760
                      else
                        BitVec.ofNat (edgeCount 12) 6089711396551917568
              else
                if i < 1047 then
                  if i < 1044 then
                    if i < 1043 then
                      BitVec.ofNat (edgeCount 12) 8107324029613899776
                    else
                      BitVec.ofNat (edgeCount 12) 13943989146686062592
                  else
                    if i < 1045 then
                      BitVec.ofNat (edgeCount 12) 37146534426898857984
                    else
                      if i < 1046 then
                        BitVec.ofNat (edgeCount 12) 37290649614974713856
                      else
                        BitVec.ofNat (edgeCount 12) 37795052773240209408
                else
                  if i < 1050 then
                    if i < 1048 then
                      BitVec.ofNat (edgeCount 12) 38155340743429849088
                    else
                      if i < 1049 then
                        BitVec.ofNat (edgeCount 12) 38371513525543632896
                      else
                        BitVec.ofNat (edgeCount 12) 38911945480828092416
                  else
                    if i < 1051 then
                      BitVec.ofNat (edgeCount 12) 40389126158605615104
                    else
                      if i < 1052 then
                        BitVec.ofNat (edgeCount 12) 40641327737738362880
                      else
                        BitVec.ofNat (edgeCount 12) 41614105257250390016
    else
      if i < 1229 then
        if i < 1141 then
          if i < 1097 then
            if i < 1075 then
              if i < 1064 then
                if i < 1058 then
                  if i < 1055 then
                    if i < 1054 then
                      BitVec.ofNat (edgeCount 12) 41830278039364173824
                    else
                      BitVec.ofNat (edgeCount 12) 42694969167819309056
                  else
                    if i < 1056 then
                      BitVec.ofNat (edgeCount 12) 544971014700793856
                    else
                      if i < 1057 then
                        BitVec.ofNat (edgeCount 12) 977316578928361472
                      else
                        BitVec.ofNat (edgeCount 12) 1085402969985253376
                else
                  if i < 1061 then
                    if i < 1059 then
                      BitVec.ofNat (edgeCount 12) 2058180489497280512
                    else
                      if i < 1060 then
                        BitVec.ofNat (edgeCount 12) 2094209286516244480
                      else
                        BitVec.ofNat (edgeCount 12) 4327994701692010496
                  else
                    if i < 1062 then
                      BitVec.ofNat (edgeCount 12) 4868426656976470016
                    else
                      if i < 1063 then
                        BitVec.ofNat (edgeCount 12) 5012541845052325888
                      else
                        BitVec.ofNat (edgeCount 12) 5516945003317821440
              else
                if i < 1069 then
                  if i < 1066 then
                    if i < 1065 then
                      BitVec.ofNat (edgeCount 12) 9480112675403857920
                    else
                      BitVec.ofNat (edgeCount 12) 9624227863479713792
                  else
                    if i < 1067 then
                      BitVec.ofNat (edgeCount 12) 9732314254536605696
                    else
                      if i < 1068 then
                        BitVec.ofNat (edgeCount 12) 10164659818764173312
                      else
                        BitVec.ofNat (edgeCount 12) 13947683505755389952
                else
                  if i < 1072 then
                    if i < 1070 then
                      BitVec.ofNat (edgeCount 12) 27890827952094445568
                    else
                      if i < 1071 then
                        BitVec.ofNat (edgeCount 12) 41617799616319717376
                      else
                        BitVec.ofNat (edgeCount 12) 41833972398433501184
                  else
                    if i < 1073 then
                      BitVec.ofNat (edgeCount 12) 252448145154244608
                    else
                      if i < 1074 then
                        BitVec.ofNat (edgeCount 12) 4828105366562668544
                      else
                        BitVec.ofNat (edgeCount 12) 32282048695013212160
            else
              if i < 1086 then
                if i < 1080 then
                  if i < 1077 then
                    if i < 1076 then
                      BitVec.ofNat (edgeCount 12) 252588882642599936
                    else
                      BitVec.ofNat (edgeCount 12) 684934446870167552
                  else
                    if i < 1078 then
                      BitVec.ofNat (edgeCount 12) 5044418886164807680
                    else
                      if i < 1079 then
                        BitVec.ofNat (edgeCount 12) 5332649262316519424
                      else
                        BitVec.ofNat (edgeCount 12) 13979560546867871744
                else
                  if i < 1083 then
                    if i < 1081 then
                      BitVec.ofNat (edgeCount 12) 14123675734943727616
                    else
                      if i < 1082 then
                        BitVec.ofNat (edgeCount 12) 14411906111095439360
                      else
                        BitVec.ofNat (edgeCount 12) 18879476941446971392
                  else
                    if i < 1084 then
                      BitVec.ofNat (edgeCount 12) 19167707317598683136
                    else
                      if i < 1085 then
                        BitVec.ofNat (edgeCount 12) 23202932583722647552
                      else
                        BitVec.ofNat (edgeCount 12) 505283042984591360
              else
                if i < 1091 then
                  if i < 1088 then
                    if i < 1087 then
                      BitVec.ofNat (edgeCount 12) 937628607212158976
                    else
                      BitVec.ofNat (edgeCount 12) 1369974171439726592
                  else
                    if i < 1089 then
                      BitVec.ofNat (edgeCount 12) 1514089359515582464
                    else
                      if i < 1090 then
                        BitVec.ofNat (edgeCount 12) 3531701992577564672
                      else
                        BitVec.ofNat (edgeCount 12) 4828738685260267520
                else
                  if i < 1094 then
                    if i < 1092 then
                      BitVec.ofNat (edgeCount 12) 4972853873336123392
                    else
                      if i < 1093 then
                        BitVec.ofNat (edgeCount 12) 5477257031601618944
                      else
                        BitVec.ofNat (edgeCount 12) 5837545001791258624
                  else
                    if i < 1095 then
                      BitVec.ofNat (edgeCount 12) 6053717783905042432
                    else
                      if i < 1096 then
                        BitVec.ofNat (edgeCount 12) 8071330416967024640
                      else
                        BitVec.ofNat (edgeCount 12) 9440424703687655424
          else
            if i < 1119 then
              if i < 1108 then
                if i < 1102 then
                  if i < 1099 then
                    if i < 1098 then
                      BitVec.ofNat (edgeCount 12) 9584539891763511296
                    else
                      BitVec.ofNat (edgeCount 12) 10449231020218646528
                  else
                    if i < 1100 then
                      BitVec.ofNat (edgeCount 12) 13907995534039187456
                    else
                      if i < 1101 then
                        BitVec.ofNat (edgeCount 12) 254172179386597376
                      else
                        BitVec.ofNat (edgeCount 12) 398287367462453248
                else
                  if i < 1105 then
                    if i < 1103 then
                      BitVec.ofNat (edgeCount 12) 902690525727948800
                    else
                      if i < 1104 then
                        BitVec.ofNat (edgeCount 12) 2019583233315831808
                      else
                        BitVec.ofNat (edgeCount 12) 2415900000524435456
                  else
                    if i < 1106 then
                      BitVec.ofNat (edgeCount 12) 2632072782638219264
                    else
                      if i < 1107 then
                        BitVec.ofNat (edgeCount 12) 3172504737922678784
                      else
                        BitVec.ofNat (edgeCount 12) 4721743009738129408
              else
                if i < 1113 then
                  if i < 1110 then
                    if i < 1109 then
                      BitVec.ofNat (edgeCount 12) 4937915791851913216
                    else
                      BitVec.ofNat (edgeCount 12) 6955528424913895424
                  else
                    if i < 1111 then
                      BitVec.ofNat (edgeCount 12) 256811007293259776
                    else
                      if i < 1112 then
                        BitVec.ofNat (edgeCount 12) 400926195369115648
                      else
                        BitVec.ofNat (edgeCount 12) 9336067856072179712
                else
                  if i < 1116 then
                    if i < 1114 then
                      BitVec.ofNat (edgeCount 12) 27818840726800695296
                    else
                      if i < 1115 then
                        BitVec.ofNat (edgeCount 12) 9444365353361604608
                      else
                        BitVec.ofNat (edgeCount 12) 9588480541437460480
                  else
                    if i < 1117 then
                      BitVec.ofNat (edgeCount 12) 9876710917589172224
                    else
                      if i < 1118 then
                        BitVec.ofNat (edgeCount 12) 252553766989987840
                      else
                        BitVec.ofNat (edgeCount 12) 468726549103771648
            else
              if i < 1130 then
                if i < 1124 then
                  if i < 1121 then
                    if i < 1120 then
                      BitVec.ofNat (edgeCount 12) 684899331217555456
                    else
                      BitVec.ofNat (edgeCount 12) 756956925255483392
                  else
                    if i < 1122 then
                      BitVec.ofNat (edgeCount 12) 1009158504388231168
                    else
                      if i < 1123 then
                        BitVec.ofNat (edgeCount 12) 1873849632843366400
                      else
                        BitVec.ofNat (edgeCount 12) 4035577453981204480
                else
                  if i < 1127 then
                    if i < 1125 then
                      BitVec.ofNat (edgeCount 12) 4720124597341519872
                    else
                      if i < 1126 then
                        BitVec.ofNat (edgeCount 12) 4792182191379447808
                      else
                        BitVec.ofNat (edgeCount 12) 4828210988398411776
                  else
                    if i < 1128 then
                      BitVec.ofNat (edgeCount 12) 5044383770512195584
                    else
                      if i < 1129 then
                        BitVec.ofNat (edgeCount 12) 5332614146663907328
                      else
                        BitVec.ofNat (edgeCount 12) 18555182652623683584
              else
                if i < 1135 then
                  if i < 1132 then
                    if i < 1131 then
                      BitVec.ofNat (edgeCount 12) 18627240246661611520
                    else
                      BitVec.ofNat (edgeCount 12) 18771355434737467392
                  else
                    if i < 1133 then
                      BitVec.ofNat (edgeCount 12) 19059585810889179136
                    else
                      if i < 1134 then
                        BitVec.ofNat (edgeCount 12) 252624135734165504
                      else
                        BitVec.ofNat (edgeCount 12) 396739323810021376
                else
                  if i < 1138 then
                    if i < 1136 then
                      BitVec.ofNat (edgeCount 12) 468796917847949312
                    else
                      if i < 1137 then
                        BitVec.ofNat (edgeCount 12) 504825714866913280
                      else
                        BitVec.ofNat (edgeCount 12) 684969699961733120
                  else
                    if i < 1139 then
                      BitVec.ofNat (edgeCount 12) 757027293999661056
                    else
                      if i < 1140 then
                        BitVec.ofNat (edgeCount 12) 901142482075516928
                      else
                        BitVec.ofNat (edgeCount 12) 937171279094480896
        else
          if i < 1185 then
            if i < 1163 then
              if i < 1152 then
                if i < 1146 then
                  if i < 1143 then
                    if i < 1142 then
                      BitVec.ofNat (edgeCount 12) 1801862407549616128
                    else
                      BitVec.ofNat (edgeCount 12) 2018035189663399936
                  else
                    if i < 1144 then
                      BitVec.ofNat (edgeCount 12) 4035647822725382144
                    else
                      if i < 1145 then
                        BitVec.ofNat (edgeCount 12) 4720194966085697536
                      else
                        BitVec.ofNat (edgeCount 12) 4792252560123625472
                else
                  if i < 1149 then
                    if i < 1147 then
                      BitVec.ofNat (edgeCount 12) 4828281357142589440
                    else
                      if i < 1148 then
                        BitVec.ofNat (edgeCount 12) 4936367748199481344
                      else
                        BitVec.ofNat (edgeCount 12) 4972396545218445312
                  else
                    if i < 1150 then
                      BitVec.ofNat (edgeCount 12) 5044454139256373248
                    else
                      if i < 1151 then
                        BitVec.ofNat (edgeCount 12) 5476799703483940864
                      else
                        BitVec.ofNat (edgeCount 12) 9331880984513085440
              else
                if i < 1157 then
                  if i < 1154 then
                    if i < 1153 then
                      BitVec.ofNat (edgeCount 12) 9439967375569977344
                    else
                      BitVec.ofNat (edgeCount 12) 9584082563645833216
                  else
                    if i < 1155 then
                      BitVec.ofNat (edgeCount 12) 9872312939797544960
                    else
                      if i < 1156 then
                        BitVec.ofNat (edgeCount 12) 18555253021367861248
                      else
                        BitVec.ofNat (edgeCount 12) 18627310615405789184
                else
                  if i < 1160 then
                    if i < 1158 then
                      BitVec.ofNat (edgeCount 12) 18663339412424753152
                    else
                      if i < 1159 then
                        BitVec.ofNat (edgeCount 12) 18771425803481645056
                      else
                        BitVec.ofNat (edgeCount 12) 18879512194538536960
                  else
                    if i < 1161 then
                      BitVec.ofNat (edgeCount 12) 37001997095077412864
                    else
                      if i < 1162 then
                        BitVec.ofNat (edgeCount 12) 37074054689115340800
                      else
                        BitVec.ofNat (edgeCount 12) 37218169877191196672
            else
              if i < 1174 then
                if i < 1168 then
                  if i < 1165 then
                    if i < 1164 then
                      BitVec.ofNat (edgeCount 12) 37506400253342908416
                    else
                      BitVec.ofNat (edgeCount 12) 253046348199231488
                  else
                    if i < 1166 then
                      BitVec.ofNat (edgeCount 12) 397161536275087360
                    else
                      if i < 1167 then
                        BitVec.ofNat (edgeCount 12) 469219130313015296
                      else
                        BitVec.ofNat (edgeCount 12) 505247927331979264
                else
                  if i < 1171 then
                    if i < 1169 then
                      BitVec.ofNat (edgeCount 12) 901564694540582912
                    else
                      if i < 1170 then
                        BitVec.ofNat (edgeCount 12) 937593491559546880
                      else
                        BitVec.ofNat (edgeCount 12) 1009651085597474816
                  else
                    if i < 1172 then
                      BitVec.ofNat (edgeCount 12) 1261852664730222592
                    else
                      if i < 1173 then
                        BitVec.ofNat (edgeCount 12) 1333910258768150528
                      else
                        BitVec.ofNat (edgeCount 12) 1369939055787114496
              else
                if i < 1179 then
                  if i < 1176 then
                    if i < 1175 then
                      BitVec.ofNat (edgeCount 12) 1514054243862970368
                    else
                      BitVec.ofNat (edgeCount 12) 1586111837900898304
                  else
                    if i < 1177 then
                      BitVec.ofNat (edgeCount 12) 2018457402128465920
                    else
                      if i < 1178 then
                        BitVec.ofNat (edgeCount 12) 3531666876924952576
                      else
                        BitVec.ofNat (edgeCount 12) 3603724470962880512
                else
                  if i < 1182 then
                    if i < 1180 then
                      BitVec.ofNat (edgeCount 12) 3747839659038736384
                    else
                      if i < 1181 then
                        BitVec.ofNat (edgeCount 12) 4720617178550763520
                      else
                        BitVec.ofNat (edgeCount 12) 4792674772588691456
                  else
                    if i < 1183 then
                      BitVec.ofNat (edgeCount 12) 4828703569607655424
                    else
                      if i < 1184 then
                        BitVec.ofNat (edgeCount 12) 5044876351721439232
                      else
                        BitVec.ofNat (edgeCount 12) 5909567480176574464
          else
            if i < 1207 then
              if i < 1196 then
                if i < 1190 then
                  if i < 1187 then
                    if i < 1186 then
                      BitVec.ofNat (edgeCount 12) 9332303196978151424
                    else
                      BitVec.ofNat (edgeCount 12) 9440389588035043328
                  else
                    if i < 1188 then
                      BitVec.ofNat (edgeCount 12) 9584504776110899200
                    else
                      if i < 1189 then
                        BitVec.ofNat (edgeCount 12) 10449195904566034432
                      else
                        BitVec.ofNat (edgeCount 12) 18555675233832927232
                else
                  if i < 1193 then
                    if i < 1191 then
                      BitVec.ofNat (edgeCount 12) 18627732827870855168
                    else
                      if i < 1192 then
                        BitVec.ofNat (edgeCount 12) 18771848015946711040
                      else
                        BitVec.ofNat (edgeCount 12) 19636539144401846272
                  else
                    if i < 1194 then
                      BitVec.ofNat (edgeCount 12) 37002419307542478848
                    else
                      if i < 1195 then
                        BitVec.ofNat (edgeCount 12) 37074476901580406784
                      else
                        BitVec.ofNat (edgeCount 12) 37110505698599370752
              else
                if i < 1201 then
                  if i < 1198 then
                    if i < 1197 then
                      BitVec.ofNat (edgeCount 12) 37218592089656262656
                    else
                      BitVec.ofNat (edgeCount 12) 37254620886675226624
                  else
                    if i < 1199 then
                      BitVec.ofNat (edgeCount 12) 37326678480713154560
                    else
                      if i < 1200 then
                        BitVec.ofNat (edgeCount 12) 37759024044940722176
                      else
                        BitVec.ofNat (edgeCount 12) 38083283218111397888
                else
                  if i < 1204 then
                    if i < 1202 then
                      BitVec.ofNat (edgeCount 12) 38119312015130361856
                    else
                      if i < 1203 then
                        BitVec.ofNat (edgeCount 12) 38191369609168289792
                      else
                        BitVec.ofNat (edgeCount 12) 38335484797244145664
                  else
                    if i < 1205 then
                      BitVec.ofNat (edgeCount 12) 40353097430306127872
                    else
                      if i < 1206 then
                        BitVec.ofNat (edgeCount 12) 41542047731931938816
                      else
                        BitVec.ofNat (edgeCount 12) 41650134122988830720
            else
              if i < 1218 then
                if i < 1212 then
                  if i < 1209 then
                    if i < 1208 then
                      BitVec.ofNat (edgeCount 12) 46189762547378290688
                    else
                      BitVec.ofNat (edgeCount 12) 55377105787214102528
                  else
                    if i < 1210 then
                      BitVec.ofNat (edgeCount 12) 256846260384825344
                    else
                      if i < 1211 then
                        BitVec.ofNat (edgeCount 12) 473019042498609152
                      else
                        BitVec.ofNat (edgeCount 12) 941393403745140736
                else
                  if i < 1215 then
                    if i < 1213 then
                      BitVec.ofNat (edgeCount 12) 2022257314314059776
                    else
                      if i < 1214 then
                        BitVec.ofNat (edgeCount 12) 4724417090736357376
                      else
                        BitVec.ofNat (edgeCount 12) 4796474684774285312
                  else
                    if i < 1216 then
                      BitVec.ofNat (edgeCount 12) 9336103109163745280
                    else
                      if i < 1217 then
                        BitVec.ofNat (edgeCount 12) 9588304688296493056
                      else
                        BitVec.ofNat (edgeCount 12) 18631532740056449024
              else
                if i < 1223 then
                  if i < 1220 then
                    if i < 1219 then
                      BitVec.ofNat (edgeCount 12) 252624616770502656
                    else
                      BitVec.ofNat (edgeCount 12) 468797398884286464
                  else
                    if i < 1221 then
                      BitVec.ofNat (edgeCount 12) 684970180998070272
                    else
                      if i < 1222 then
                        BitVec.ofNat (edgeCount 12) 1009229354168745984
                      else
                        BitVec.ofNat (edgeCount 12) 1765834091566989312
                else
                  if i < 1226 then
                    if i < 1224 then
                      BitVec.ofNat (edgeCount 12) 4035648303761719296
                    else
                      if i < 1225 then
                        BitVec.ofNat (edgeCount 12) 4720195447122034688
                      else
                        BitVec.ofNat (edgeCount 12) 4792253041159962624
                  else
                    if i < 1227 then
                      BitVec.ofNat (edgeCount 12) 5224598605387530240
                    else
                      if i < 1228 then
                        BitVec.ofNat (edgeCount 12) 18879512675574874112
                      else
                        BitVec.ofNat (edgeCount 12) 252906091747213312
      else
        if i < 1317 then
          if i < 1273 then
            if i < 1251 then
              if i < 1240 then
                if i < 1234 then
                  if i < 1231 then
                    if i < 1230 then
                      BitVec.ofNat (edgeCount 12) 397021279823069184
                    else
                      BitVec.ofNat (edgeCount 12) 469078873860997120
                  else
                    if i < 1232 then
                      BitVec.ofNat (edgeCount 12) 901424438088564736
                    else
                      if i < 1233 then
                        BitVec.ofNat (edgeCount 12) 1009510829145456640
                      else
                        BitVec.ofNat (edgeCount 12) 1261712408278204416
                else
                  if i < 1237 then
                    if i < 1235 then
                      BitVec.ofNat (edgeCount 12) 1477885190391988224
                    else
                      if i < 1236 then
                        BitVec.ofNat (edgeCount 12) 2018317145676447744
                      else
                        BitVec.ofNat (edgeCount 12) 3495497823453970432
                  else
                    if i < 1238 then
                      BitVec.ofNat (edgeCount 12) 3747699402586718208
                    else
                      if i < 1239 then
                        BitVec.ofNat (edgeCount 12) 4720476922098745344
                      else
                        BitVec.ofNat (edgeCount 12) 4792534516136673280
              else
                if i < 1245 then
                  if i < 1242 then
                    if i < 1241 then
                      BitVec.ofNat (edgeCount 12) 4936649704212529152
                    else
                      BitVec.ofNat (edgeCount 12) 5801340832667664384
                  else
                    if i < 1243 then
                      BitVec.ofNat (edgeCount 12) 18555534977380909056
                    else
                      if i < 1244 then
                        BitVec.ofNat (edgeCount 12) 18627592571418836992
                      else
                        BitVec.ofNat (edgeCount 12) 18771707759494692864
                else
                  if i < 1248 then
                    if i < 1246 then
                      BitVec.ofNat (edgeCount 12) 19059938135646404608
                    else
                      if i < 1247 then
                        BitVec.ofNat (edgeCount 12) 19168024526703296512
                      else
                        BitVec.ofNat (edgeCount 12) 19312139714779152384
                  else
                    if i < 1249 then
                      BitVec.ofNat (edgeCount 12) 19636398887949828096
                    else
                      if i < 1250 then
                        BitVec.ofNat (edgeCount 12) 20176830843234287616
                      else
                        BitVec.ofNat (edgeCount 12) 23095163401770369024
            else
              if i < 1262 then
                if i < 1256 then
                  if i < 1253 then
                    if i < 1252 then
                      BitVec.ofNat (edgeCount 12) 55376965530762084352
                    else
                      BitVec.ofNat (edgeCount 12) 55485051921818976256
                  else
                    if i < 1254 then
                      BitVec.ofNat (edgeCount 12) 55629167109894832128
                    else
                      if i < 1255 then
                        BitVec.ofNat (edgeCount 12) 56493858238349967360
                      else
                        BitVec.ofNat (edgeCount 12) 253891254165700608
                else
                  if i < 1259 then
                    if i < 1257 then
                      BitVec.ofNat (edgeCount 12) 470064036279484416
                    else
                      if i < 1258 then
                        BitVec.ofNat (edgeCount 12) 758294412431196160
                      else
                        BitVec.ofNat (edgeCount 12) 1010495991563943936
                  else
                    if i < 1260 then
                      BitVec.ofNat (edgeCount 12) 2415619075303538688
                    else
                      if i < 1261 then
                        BitVec.ofNat (edgeCount 12) 2487676669341466624
                      else
                        BitVec.ofNat (edgeCount 12) 2739878248474214400
              else
                if i < 1267 then
                  if i < 1264 then
                    if i < 1263 then
                      BitVec.ofNat (edgeCount 12) 3028108624625926144
                    else
                      BitVec.ofNat (edgeCount 12) 4721462084517232640
                  else
                    if i < 1265 then
                      BitVec.ofNat (edgeCount 12) 4793519678555160576
                    else
                      if i < 1266 then
                        BitVec.ofNat (edgeCount 12) 6955247499692998656
                      else
                        BitVec.ofNat (edgeCount 12) 18556520139799396352
                else
                  if i < 1270 then
                    if i < 1268 then
                      BitVec.ofNat (edgeCount 12) 18628577733837324288
                    else
                      if i < 1269 then
                        BitVec.ofNat (edgeCount 12) 18880779312970072064
                      else
                        BitVec.ofNat (edgeCount 12) 19060923298064891904
                  else
                    if i < 1271 then
                      BitVec.ofNat (edgeCount 12) 19169009689121783808
                    else
                      if i < 1272 then
                        BitVec.ofNat (edgeCount 12) 20177816005652774912
                      else
                        BitVec.ofNat (edgeCount 12) 20790305554975162368
          else
            if i < 1295 then
              if i < 1284 then
                if i < 1278 then
                  if i < 1275 then
                    if i < 1274 then
                      BitVec.ofNat (edgeCount 12) 20898391946032054272
                    else
                      BitVec.ofNat (edgeCount 12) 21330737510259621888
                  else
                    if i < 1276 then
                      BitVec.ofNat (edgeCount 12) 23096148564188856320
                    else
                      if i < 1277 then
                        BitVec.ofNat (edgeCount 12) 55377950693180571648
                      else
                        BitVec.ofNat (edgeCount 12) 55486037084237463552
                else
                  if i < 1281 then
                    if i < 1279 then
                      BitVec.ofNat (edgeCount 12) 57647764905375301632
                    else
                      if i < 1280 then
                        BitVec.ofNat (edgeCount 12) 252421550716747776
                      else
                        BitVec.ofNat (edgeCount 12) 396536738792603648
                  else
                    if i < 1282 then
                      BitVec.ofNat (edgeCount 12) 504623129849495552
                    else
                      if i < 1283 then
                        BitVec.ofNat (edgeCount 12) 1009026288114991104
                      else
                        BitVec.ofNat (edgeCount 12) 2017832604645982208
              else
                if i < 1289 then
                  if i < 1286 then
                    if i < 1285 then
                      BitVec.ofNat (edgeCount 12) 4719992381068279808
                    else
                      BitVec.ofNat (edgeCount 12) 4792049975106207744
                  else
                    if i < 1287 then
                      BitVec.ofNat (edgeCount 12) 9331678399495667712
                    else
                      if i < 1288 then
                        BitVec.ofNat (edgeCount 12) 9439764790552559616
                      else
                        BitVec.ofNat (edgeCount 12) 9655937572666343424
                else
                  if i < 1292 then
                    if i < 1290 then
                      BitVec.ofNat (edgeCount 12) 23094678860739903488
                    else
                      if i < 1291 then
                        BitVec.ofNat (edgeCount 12) 37001794510059995136
                      else
                        BitVec.ofNat (edgeCount 12) 37109880901116887040
                  else
                    if i < 1293 then
                      BitVec.ofNat (edgeCount 12) 37253996089192742912
                    else
                      if i < 1294 then
                        BitVec.ofNat (edgeCount 12) 504834236082028544
                      else
                        BitVec.ofNat (edgeCount 12) 793064612233740288
            else
              if i < 1306 then
                if i < 1300 then
                  if i < 1297 then
                    if i < 1296 then
                      BitVec.ofNat (edgeCount 12) 1009237394347524096
                    else
                      BitVec.ofNat (edgeCount 12) 1801870928764731392
                  else
                    if i < 1298 then
                      BitVec.ofNat (edgeCount 12) 1873928522802659328
                    else
                      if i < 1299 then
                        BitVec.ofNat (edgeCount 12) 4035656343940497408
                      else
                        BitVec.ofNat (edgeCount 12) 4720203487300812800
                else
                  if i < 1303 then
                    if i < 1301 then
                      BitVec.ofNat (edgeCount 12) 4792261081338740736
                    else
                      if i < 1302 then
                        BitVec.ofNat (edgeCount 12) 9331889505728200704
                      else
                        BitVec.ofNat (edgeCount 12) 9439975896785092608
                  else
                    if i < 1304 then
                      BitVec.ofNat (edgeCount 12) 9872321461012660224
                    else
                      if i < 1305 then
                        BitVec.ofNat (edgeCount 12) 23094889966972436480
                      else
                        BitVec.ofNat (edgeCount 12) 37002005616292528128
              else
                if i < 1311 then
                  if i < 1308 then
                    if i < 1307 then
                      BitVec.ofNat (edgeCount 12) 37074063210330456064
                    else
                      BitVec.ofNat (edgeCount 12) 37110092007349420032
                  else
                    if i < 1309 then
                      BitVec.ofNat (edgeCount 12) 37326264789463203840
                    else
                      if i < 1310 then
                        BitVec.ofNat (edgeCount 12) 37506408774558023680
                      else
                        BitVec.ofNat (edgeCount 12) 37542437571576987648
                else
                  if i < 1314 then
                    if i < 1312 then
                      BitVec.ofNat (edgeCount 12) 37614495165614915584
                    else
                      if i < 1313 then
                        BitVec.ofNat (edgeCount 12) 38623301482145906688
                      else
                        BitVec.ofNat (edgeCount 12) 41541634040681988096
                  else
                    if i < 1315 then
                      BitVec.ofNat (edgeCount 12) 46189348856128339968
                    else
                      if i < 1316 then
                        BitVec.ofNat (edgeCount 12) 261288012483133440
                      else
                        BitVec.ofNat (edgeCount 12) 1017892749881376768
        else
          if i < 1361 then
            if i < 1339 then
              if i < 1328 then
                if i < 1322 then
                  if i < 1319 then
                    if i < 1318 then
                      BitVec.ofNat (edgeCount 12) 4728858842834665472
                    else
                      BitVec.ofNat (edgeCount 12) 23103545322506289152
                  else
                    if i < 1320 then
                      BitVec.ofNat (edgeCount 12) 4900339020168429568
                    else
                      if i < 1321 then
                        BitVec.ofNat (edgeCount 12) 4756646044557639680
                      else
                        BitVec.ofNat (edgeCount 12) 434035239528955904
                else
                  if i < 1325 then
                    if i < 1323 then
                      BitVec.ofNat (edgeCount 12) 4685433287766704128
                    else
                      if i < 1324 then
                        BitVec.ofNat (edgeCount 12) 432776711032012800
                      else
                        BitVec.ofNat (edgeCount 12) 325104012030377984
                  else
                    if i < 1326 then
                      BitVec.ofNat (edgeCount 12) 865535967314837504
                    else
                      if i < 1327 then
                        BitVec.ofNat (edgeCount 12) 432944387360555008
                      else
                        BitVec.ofNat (edgeCount 12) 324963549419929600
              else
                if i < 1333 then
                  if i < 1330 then
                    if i < 1329 then
                      BitVec.ofNat (edgeCount 12) 865395504704389120
                    else
                      BitVec.ofNat (edgeCount 12) 181833523762561024
                  else
                    if i < 1331 then
                      BitVec.ofNat (edgeCount 12) 434035102895308800
                    else
                      if i < 1332 then
                        BitVec.ofNat (edgeCount 12) 111465741657571328
                      else
                        BitVec.ofNat (edgeCount 12) 219552132714463232
                else
                  if i < 1336 then
                    if i < 1334 then
                      BitVec.ofNat (edgeCount 12) 4651094166047031296
                    else
                      if i < 1335 then
                        BitVec.ofNat (edgeCount 12) 432697854895587328
                      else
                        BitVec.ofNat (edgeCount 12) 217017653991047168
                  else
                    if i < 1337 then
                      BitVec.ofNat (edgeCount 12) 540995456071663616
                    else
                      if i < 1338 then
                        BitVec.ofNat (edgeCount 12) 1405686584526798848
                      else
                        BitVec.ofNat (edgeCount 12) 2558608089133645824
            else
              if i < 1350 then
                if i < 1344 then
                  if i < 1341 then
                    if i < 1340 then
                      BitVec.ofNat (edgeCount 12) 3567414405664636928
                    else
                      BitVec.ofNat (edgeCount 12) 7026178919485177856
                  else
                    if i < 1342 then
                      BitVec.ofNat (edgeCount 12) 252800264292040704
                    else
                      if i < 1343 then
                        BitVec.ofNat (edgeCount 12) 505001843424788480
                      else
                        BitVec.ofNat (edgeCount 12) 685145828519608320
                else
                  if i < 1347 then
                    if i < 1345 then
                      BitVec.ofNat (edgeCount 12) 793232219576500224
                    else
                      if i < 1346 then
                        BitVec.ofNat (edgeCount 12) 1261606580823031808
                      else
                        BitVec.ofNat (edgeCount 12) 1369692971879923712
                  else
                    if i < 1348 then
                      BitVec.ofNat (edgeCount 12) 1766009739088527360
                    else
                      if i < 1349 then
                        BitVec.ofNat (edgeCount 12) 1802038536107491328
                      else
                        BitVec.ofNat (edgeCount 12) 2414528085429878784
              else
                if i < 1355 then
                  if i < 1352 then
                    if i < 1351 then
                      BitVec.ofNat (edgeCount 12) 2918931243695374336
                    else
                      BitVec.ofNat (edgeCount 12) 2954960040714338304
                  else
                    if i < 1353 then
                      BitVec.ofNat (edgeCount 12) 4035823951283257344
                    else
                      if i < 1354 then
                        BitVec.ofNat (edgeCount 12) 4720371094643572736
                      else
                        BitVec.ofNat (edgeCount 12) 4828457485700464640
                else
                  if i < 1358 then
                    if i < 1356 then
                      BitVec.ofNat (edgeCount 12) 5260803049928032256
                    else
                      if i < 1357 then
                        BitVec.ofNat (edgeCount 12) 5837263802231455744
                      else
                        BitVec.ofNat (edgeCount 12) 37002173223635288064
                  else
                    if i < 1359 then
                      BitVec.ofNat (edgeCount 12) 37506576381900783616
                    else
                      if i < 1360 then
                        BitVec.ofNat (edgeCount 12) 38083037134204207104
                      else
                        BitVec.ofNat (edgeCount 12) 253890979826794496
          else
            if i < 1383 then
              if i < 1372 then
                if i < 1366 then
                  if i < 1363 then
                    if i < 1362 then
                      BitVec.ofNat (edgeCount 12) 686236544054362112
                    else
                      BitVec.ofNat (edgeCount 12) 1767100454623281152
                  else
                    if i < 1364 then
                      BitVec.ofNat (edgeCount 12) 2415618800964632576
                    else
                      if i < 1365 then
                        BitVec.ofNat (edgeCount 12) 2920021959230128128
                      else
                        BitVec.ofNat (edgeCount 12) 37003263939170041856
                else
                  if i < 1369 then
                    if i < 1367 then
                      BitVec.ofNat (edgeCount 12) 37507667097435537408
                    else
                      if i < 1368 then
                        BitVec.ofNat (edgeCount 12) 38624559805023420416
                      else
                        BitVec.ofNat (edgeCount 12) 39237049354345807872
                  else
                    if i < 1370 then
                      BitVec.ofNat (edgeCount 12) 506690693285052416
                    else
                      if i < 1371 then
                        BitVec.ofNat (edgeCount 12) 794921069436764160
                      else
                        BitVec.ofNat (edgeCount 12) 1803727385967755264
              else
                if i < 1377 then
                  if i < 1374 then
                    if i < 1373 then
                      BitVec.ofNat (edgeCount 12) 2416216935290142720
                    else
                      BitVec.ofNat (edgeCount 12) 4722059944503836672
                  else
                    if i < 1375 then
                      BitVec.ofNat (edgeCount 12) 4830146335560728576
                    else
                      if i < 1376 then
                        BitVec.ofNat (edgeCount 12) 5262491899788296192
                      else
                        BitVec.ofNat (edgeCount 12) 39237647488671318016
                else
                  if i < 1380 then
                    if i < 1378 then
                      BitVec.ofNat (edgeCount 12) 432979502478426112
                    else
                      if i < 1379 then
                        BitVec.ofNat (edgeCount 12) 1297670630933561344
                      else
                        BitVec.ofNat (edgeCount 12) 2594707323616264192
                  else
                    if i < 1381 then
                      BitVec.ofNat (edgeCount 12) 9368121163181490176
                    else
                      if i < 1382 then
                        BitVec.ofNat (edgeCount 12) 217017826597175296
                      else
                        BitVec.ofNat (edgeCount 12) 649363390824742912
            else
              if i < 1394 then
                if i < 1388 then
                  if i < 1385 then
                    if i < 1384 then
                      BitVec.ofNat (edgeCount 12) 2883148806000508928
                    else
                      BitVec.ofNat (edgeCount 12) 217862251527307264
                  else
                    if i < 1386 then
                      BitVec.ofNat (edgeCount 12) 361977439603163136
                    else
                      if i < 1387 then
                        BitVec.ofNat (edgeCount 12) 650207815754874880
                      else
                        BitVec.ofNat (edgeCount 12) 1731071726323793920
                else
                  if i < 1391 then
                    if i < 1389 then
                      BitVec.ofNat (edgeCount 12) 2595762854778929152
                    else
                      if i < 1390 then
                        BitVec.ofNat (edgeCount 12) 4685433081878839296
                      else
                        BitVec.ofNat (edgeCount 12) 218706676457439232
                  else
                    if i < 1392 then
                      BitVec.ofNat (edgeCount 12) 108932466332434432
                    else
                      if i < 1393 then
                        BitVec.ofNat (edgeCount 12) 109495416285855744
                      else
                        BitVec.ofNat (edgeCount 12) 613898574551351296
              else
                if i < 1399 then
                  if i < 1396 then
                    if i < 1395 then
                      BitVec.ofNat (edgeCount 12) 1730791282139234304
                    else
                      BitVec.ofNat (edgeCount 12) 432701875792412672
                  else
                    if i < 1397 then
                      BitVec.ofNat (edgeCount 12) 4900272706143944704
                    else
                      if i < 1398 then
                        BitVec.ofNat (edgeCount 12) 9367843536495476736
                      else
                        BitVec.ofNat (edgeCount 12) 217021674887872512
                else
                  if i < 1402 then
                    if i < 1400 then
                      BitVec.ofNat (edgeCount 12) 361136862963728384
                    else
                      if i < 1401 then
                        BitVec.ofNat (edgeCount 12) 865540021229223936
                      else
                        BitVec.ofNat (edgeCount 12) 4684592505239404544
                  else
                    if i < 1403 then
                      BitVec.ofNat (edgeCount 12) 9372065661146136576
                    else
                      if i < 1404 then
                        BitVec.ofNat (edgeCount 12) 217334968060281856
                      else
                        BitVec.ofNat (edgeCount 12) 2379062789198119936

def level9 : Level 12 := ⟨1405, level9MaskAt⟩

end Erdos76.CertificateExhaustion.Certificates.PackedExhaustionN12
