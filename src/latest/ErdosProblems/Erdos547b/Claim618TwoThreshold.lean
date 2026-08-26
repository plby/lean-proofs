/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim618

/-!
# Claim 6.18 with separate physical and auxiliary threshold graphs

The matching certificate and final crossing live in R.
Only the eta-threshold auxiliary graph H has the eta-density lower bound.
The initial high-density graph R' is contained in H.
-/

open scoped BigOperators SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim618TwoThreshold

open Finset SimpleGraph Erdos547b.ZhaoStability Erdos547b.ZhaoLemma615

universe u v

theorem crossing_lt_of_local_twoThresholds
    {E : Type u} [Fintype E] [DecidableEq E]
    {K : Type v} [Fintype K] [DecidableEq K]
    (R H R' : SimpleGraph K) [DecidableRel R.Adj] [DecidableRel H.Adj] [DecidableRel R'.Adj]
    (hHR : H ≤ R) (hR'H : R' ≤ H)
    (L L₁ V₂ S₁ : Finset K)
    (M : Finset E) (endpoint : E → Fin 2 → K)
    (edgeOf : K → E) (density : K → K → ℝ)
    (eta rho rho₁ : ℝ) (k a b q miss t u z : ℕ)
    (C67 : Claim67Certificate R L miss)
    (heta : 0 < eta) (hk : 0 < k) (haNat : 0 < a)
    (ha : (a : ℝ) ≤ 8 * rho₁ * k)
    (hcutCard : L₁.card + V₂.card ≤ 2 * k)
    (hlocalArithmetic : 2 * (b + q + 1) + miss ≤ a)
    (hpartnerArithmetic : u + q ≤ t)
    (hdoubleCountArithmetic : z * a + V₂.card * t ≤ a * b)
    (hfinalArithmetic : 16 * rho * (k : ℝ) ^ 2 ≤ (z * u : ℕ))
    (h617 : ((R.interedges S₁ V₂).card : ℝ) <
      16 * rho * (k : ℝ) ^ 2)
    (hL₁ : L₁ ⊆ L ∩ C67.O)
    (hendpoint_inj : Function.Injective
      (fun ec : E × Fin 2 ↦ endpoint ec.1 ec.2))
    (hMedge : ∀ e ∈ M, C67.M.Adj (endpoint e 0) (endpoint e 1))
    (hlargeEnd : ∀ e ∈ M, endpoint e 0 ∈ L)
    (hV₂pair : ∀ e ∈ M, endpoint e 0 ∈ V₂ ↔ endpoint e 1 ∈ V₂)
    (hV₂covered : ∀ v ∈ V₂, v ∈ matchingSupport C67.M →
      v ∈ indexedMatchingSupport M endpoint)
    (hedgeOf : ∀ C ∈ L₁,
      edgeOf C ∈ M ∧ endpoint (edgeOf C) 0 = C ∧ endpoint (edgeOf C) 1 ∈ S₁)
    (hR'dense : ∀ ⦃A B⦄, R'.Adj A B → 2 * eta ≤ density A B)
    (hHdense : ∀ ⦃A B⦄, H.Adj A B → eta ≤ density A B)
    (hdenseH : ∀ ⦃A B⦄, eta ≤ density A B → H.Adj A B)
    (hnonadjZero : ∀ ⦃A B⦄, ¬ R.Adj A B → density A B = 0)
    (hunbalanced_initial : ∀ A ∈ L₁,
      (unbalancedEdges M (fun e c ↦ density A (endpoint e c)) eta).card ≤ q)
    (hunbalanced_neighbor : ∀ A ∈ L ∩ C67.O,
      (∃ B ∈ L ∩ C67.O, R.Adj A B) →
      (unbalancedEdges M (fun e c ↦ density A (endpoint e c)) eta).card ≤ q) :
    ((R'.interedges L₁ V₂).card : ℝ) < 16 * rho₁ * (k : ℝ) ^ 2 := by
  classical
  let : Std.Symm R.Adj := ⟨fun _ _ h ↦ h.symm⟩
  let : Std.Symm H.Adj := ⟨fun _ _ h ↦ h.symm⟩
  have hR'R : R' ≤ R := hR'H.trans hHR
  have hscale : ((2 * a * k : ℕ) : ℝ) ≤ 16 * rho₁ * (k : ℝ) ^ 2 := by
    push_cast
    calc
      2 * (a : ℝ) * (k : ℝ) ≤
          2 * (8 * rho₁ * (k : ℝ)) * (k : ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left ha (by norm_num)) (by positivity)
      _ = 16 * rho₁ * (k : ℝ) ^ 2 := by ring
  by_contra hclaim
  have hedgeNat : 2 * a * k ≤ (R'.interedges L₁ V₂).card := by
    have hedgeReal : (16 * rho₁ * (k : ℝ) ^ 2) ≤
        ((R'.interedges L₁ V₂).card : ℝ) := le_of_not_gt hclaim
    exact_mod_cast hscale.trans hedgeReal
  obtain ⟨L₀, hL₀L₁, hL₀card, hL₀degree⟩ :=
    exists_many_high_degree_of_many_interedges R' L₁ V₂ a k hk hcutCard hedgeNat
  have hL₀LO : L₀ ⊆ L ∩ C67.O := hL₀L₁.trans hL₁
  have hinj0 : Function.Injective (fun e : E ↦ endpoint e 0) := by
    intro e f hef
    have hp : (e, (0 : Fin 2)) = (f, (0 : Fin 2)) := hendpoint_inj hef
    exact congrArg Prod.fst hp
  have hinj1 : Function.Injective (fun e : E ↦ endpoint e 1) := by
    intro e f hef
    have hp : (e, (1 : Fin 2)) = (f, (1 : Fin 2)) := hendpoint_inj hef
    exact congrArg Prod.fst hp
  have hedgeOf_inj_on : Set.InjOn edgeOf (L₁ : Set K) := by
    intro A hA B hB hAB
    have hAe := (hedgeOf A hA).2.1
    have hBe := (hedgeOf B hB).2.1
    rw [hAB] at hAe
    exact hAe.symm.trans hBe
  have hpartner_inj_on : Set.InjOn
      (fun C ↦ endpoint (edgeOf C) 1) (L₁ : Set K) := by
    intro A hA B hB hAB
    exact hedgeOf_inj_on hA hB (hinj1 hAB)
  have hgoodAdj (A : K) (e : E)
      (he : e ∈ candidateEdges R' M endpoint A V₂ \
        unbalancedEdges M (fun p c ↦ density A (endpoint p c)) eta) :
      H.Adj A (endpoint e 0) ∧ H.Adj A (endpoint e 1) := by
    have heCand := (Finset.mem_sdiff.mp he).1
    have heNot := (Finset.mem_sdiff.mp he).2
    have heData := mem_candidateEdges.mp heCand
    have habs : |density A (endpoint e 0) - density A (endpoint e 1)| < eta := by
      have : ¬ eta ≤
          |density A (endpoint e 0) - density A (endpoint e 1)| := by
        intro hbal
        exact heNot (mem_unbalancedEdges.mpr ⟨heData.1, hbal⟩)
      exact lt_of_not_ge this
    rcases abs_lt.mp habs with ⟨hlo, hhi⟩
    rcases heData.2 with he0 | he1
    · have hd0 := hR'dense he0.2
      refine ⟨hR'H he0.2, hdenseH (by linarith)⟩
    · have hd1 := hR'dense he1.2
      refine ⟨hdenseH (by linarith), hR'H he1.2⟩
  let U : K → Finset E := fun A ↦
    unbalancedEdges M (fun e c ↦ density A (endpoint e c)) eta
  let Q : K → Finset E := fun A ↦ candidateEdges R' M endpoint A V₂
  let Good : K → Finset E := fun A ↦ Q A \ U A
  let NC : K → Finset K := fun A ↦
    ((Good A).image fun e ↦ endpoint e 0).filter fun D ↦ D ∈ C67.O
  have hUcardInitial (A : K) (hA : A ∈ L₁) : (U A).card ≤ q :=
    hunbalanced_initial A hA
  have hNC (A : K) (hA : A ∈ L₀) :
      b ≤ (NC A).card ∧ NC A ⊆ V₂ ∩ (L ∩ C67.O) ∩ H.neighborFinset A := by
    have hALO : A ∈ L ∩ C67.O := hL₀LO hA
    let W := V₂.filter fun v ↦ R'.Adj A v
    let Covered := W ∩ indexedMatchingSupport M endpoint
    have hWcard : W.card = Erdos547EC2.degreeInto R' A V₂ := by
      simp [W, Erdos547EC2.degreeInto]
    have hmissing : (W \ indexedMatchingSupport M endpoint).card ≤ miss := by
      apply (Finset.card_le_card ?_).trans
        (C67.neighbors_missed A (Finset.mem_inter.mp hALO).2)
      intro v hv
      have hv' := Finset.mem_sdiff.mp hv
      have hvW := Finset.mem_filter.mp hv'.1
      have hvV₂ : v ∈ V₂ := hvW.1
      have hvR' : R'.Adj A v := hvW.2
      have hvNotSupport : v ∉ matchingSupport C67.M := by
        intro hvSupport
        exact hv'.2 (hV₂covered v hvV₂ hvSupport)
      exact Finset.mem_sdiff.mpr ⟨by simpa using hR'R hvR', hvNotSupport⟩
    have hCoveredLower : a - miss ≤ Covered.card := by
      have hpart := Finset.card_sdiff_add_card_inter W
        (indexedMatchingSupport M endpoint)
      have hdegree := hL₀degree A hA
      rw [← hWcard] at hdegree
      change (W \ indexedMatchingSupport M endpoint).card + Covered.card = W.card at hpart
      omega
    have hCoveredSub : Covered ⊆
        (Q A).biUnion (fun e ↦ {endpoint e 0, endpoint e 1}) := by
      intro v hv
      have hvW := Finset.mem_inter.mp hv
      obtain ⟨e, heM, rfl | rfl⟩ := mem_indexedMatchingSupport.mp hvW.2
      · apply Finset.mem_biUnion.mpr
        refine ⟨e, ?_, by simp⟩
        exact mem_candidateEdges.mpr ⟨heM, Or.inl (Finset.mem_filter.mp hvW.1)⟩
      · apply Finset.mem_biUnion.mpr
        refine ⟨e, ?_, by simp⟩
        exact mem_candidateEdges.mpr ⟨heM, Or.inr (Finset.mem_filter.mp hvW.1)⟩
    have hQcount : a - miss ≤ 2 * (Q A).card := by
      calc
        a - miss ≤ Covered.card := hCoveredLower
        _ ≤ ((Q A).biUnion (fun e ↦ {endpoint e 0, endpoint e 1})).card :=
          Finset.card_le_card hCoveredSub
        _ ≤ (Q A).card * 2 := by
          apply Finset.card_biUnion_le_card_mul
          intro e he
          calc
            #{endpoint e 0, endpoint e 1} ≤ #{endpoint e 1} + 1 :=
              Finset.card_insert_le _ _
            _ = 2 := by simp
        _ = 2 * (Q A).card := by omega
    have hQGood : (Q A).card ≤ (Good A).card + (U A).card := by
      have hpart := Finset.card_sdiff_add_card_inter (Q A) (U A)
      change (Good A).card + (Q A ∩ U A).card = (Q A).card at hpart
      have hinter : (Q A ∩ U A).card ≤ (U A).card :=
        Finset.card_le_card Finset.inter_subset_right
      omega
    have hGood : b + 1 ≤ (Good A).card := by
      have hUc := hUcardInitial A (hL₀L₁ hA)
      omega
    let I := (Good A).image fun e ↦ endpoint e 0
    have hIcard : I.card = (Good A).card :=
      Finset.card_image_of_injective _ hinj0
    have houtside : (I \ C67.O).card ≤ 1 := by
      have hsub : (I \ C67.O : Finset K) ⊆
          Finset.univ.filter fun v ↦
            v ∈ matchingDoubleNeighborSet R C67.M A ∧ v ∉ C67.O := by
        intro v hv
        obtain ⟨hvI, hvO⟩ := Finset.mem_sdiff.mp hv
        obtain ⟨e, heGood, rfl⟩ := Finset.mem_image.mp hvI
        have heM : e ∈ M := (mem_candidateEdges.mp (Finset.mem_sdiff.mp heGood).1).1
        have hadj := hgoodAdj A e heGood
        have hdouble : endpoint e 0 ∈ matchingDoubleNeighborSet R C67.M A := by
          refine ⟨C67.M.edge_vert (hMedge e heM), endpoint e 1, hMedge e heM, hHR hadj.1, hHR hadj.2⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hdouble, hvO⟩
      have hcard := Finset.card_le_card hsub
      have hdouble := C67.doubleNeighbor_outside A (Finset.mem_inter.mp hALO).2
      have heq : (Finset.univ.filter fun v ↦
          v ∈ matchingDoubleNeighborSet R C67.M A ∧ v ∉ C67.O).card =
          (matchingDoubleNeighborSet R C67.M A \ (C67.O : Set K)).ncard := by
        rw [Set.ncard_eq_toFinset_card']
        congr 1
        ext v
        simp
      rw [heq] at hcard
      exact hcard.trans hdouble
    have hNCcard : b ≤ (NC A).card := by
      have hpartition := Finset.card_sdiff_add_card_inter I C67.O
      have hfilter : (NC A).card = (I ∩ C67.O).card := by
        congr 1
      rw [hIcard, ← hfilter] at hpartition
      omega
    refine ⟨hNCcard, ?_⟩
    intro D hD
    have hD' := Finset.mem_filter.mp hD
    obtain ⟨e, heGood, rfl⟩ := Finset.mem_image.mp hD'.1
    have heCand := (Finset.mem_sdiff.mp heGood).1
    have heM := (mem_candidateEdges.mp heCand).1
    have hside : endpoint e 0 ∈ V₂ := by
      rcases (mem_candidateEdges.mp heCand).2 with he0 | he1
      · exact he0.1
      · exact (hV₂pair e heM).mpr he1.1
    exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr
      ⟨hside, Finset.mem_inter.mpr ⟨hlargeEnd e heM, hD'.2⟩⟩,
        by simpa using (hgoodAdj A e heGood).1⟩
  let N : Finset K := L₀.biUnion NC
  have hNsub : N ⊆ V₂ ∩ (L ∩ C67.O) := by
    intro D hD
    obtain ⟨A, hA, hDA⟩ := Finset.mem_biUnion.mp hD
    exact Finset.mem_inter.mpr
      (Finset.mem_inter.mp (Finset.mem_inter.mp ((hNC A hA).2 hDA)).1)
  have hNcard : N.card ≤ V₂.card :=
    Finset.card_le_card (hNsub.trans Finset.inter_subset_left)
  have hL₀degreeN : ∀ A ∈ L₀, b ≤ Erdos547EC2.degreeInto H A N := by
    intro A hA
    calc
      b ≤ (NC A).card := (hNC A hA).1
      _ ≤ Erdos547EC2.degreeInto H A N := by
        unfold Erdos547EC2.degreeInto
        apply Finset.card_le_card
        intro D hD
        have hprops := (hNC A hA).2 hD
        exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨A, hA, hD⟩,
          by simpa using (Finset.mem_inter.mp hprops).2⟩
  have hHlower : a * b ≤ (H.interedges L₀ N).card := by
    rw [← hL₀card]
    exact Erdos547EC2.card_mul_le_card_interedges_of_subset_of_degreeInto
      H (Finset.Subset.rfl) hL₀degreeN
  let N₀ : Finset K := N.filter fun D ↦
    t ≤ Erdos547EC2.degreeInto H D L₀
  have hN₀subN : N₀ ⊆ N := Finset.filter_subset _ _
  have hzN₀ : z ≤ N₀.card := by
    by_contra hz
    have hzlt : N₀.card < z := Nat.lt_of_not_ge hz
    have hsum := Erdos547EC2.sum_degreeInto_eq_card_interedges H N L₀
    have hcomm : (H.interedges N L₀).card = (H.interedges L₀ N).card :=
      Rel.card_interedges_comm N L₀
    have hsplit :
        ∑ D ∈ N, Erdos547EC2.degreeInto H D L₀ =
          (∑ D ∈ N₀, Erdos547EC2.degreeInto H D L₀) +
            ∑ D ∈ N \ N₀, Erdos547EC2.degreeInto H D L₀ := by
      rw [← Finset.sum_inter_add_sum_sdiff N N₀]
      congr 2
      exact Finset.inter_eq_right.mpr hN₀subN
    have hhigh :
        ∑ D ∈ N₀, Erdos547EC2.degreeInto H D L₀ ≤ N₀.card * a := by
      rw [← hL₀card]
      exact Finset.sum_le_card_nsmul N₀
        (fun D ↦ Erdos547EC2.degreeInto H D L₀) L₀.card
        (fun D _ ↦ Erdos547EC2.degreeInto_le_card H D L₀)
    have hlow :
        ∑ D ∈ N \ N₀, Erdos547EC2.degreeInto H D L₀ ≤ N.card * t := by
      calc
        ∑ D ∈ N \ N₀, Erdos547EC2.degreeInto H D L₀ ≤
            (N \ N₀).card * t := by
          apply Finset.sum_le_card_nsmul
          intro D hD
          have hDN := (Finset.mem_sdiff.mp hD).1
          have hDnot := (Finset.mem_sdiff.mp hD).2
          have : ¬ t ≤ Erdos547EC2.degreeInto H D L₀ := by
            intro htD
            exact hDnot (Finset.mem_filter.mpr ⟨hDN, htD⟩)
          omega
        _ ≤ N.card * t :=
          Nat.mul_le_mul_right t (Finset.card_le_card Finset.sdiff_subset)
    have hedgeUpper : (H.interedges L₀ N).card ≤ N₀.card * a + N.card * t := by
      rw [← hcomm, ← hsum, hsplit]
      exact Nat.add_le_add hhigh hlow
    have hstrict : N₀.card * a + N.card * t < z * a + V₂.card * t := by
      exact Nat.add_lt_add_of_lt_of_le
        (Nat.mul_lt_mul_of_pos_right hzlt haNat)
        (Nat.mul_le_mul_right t hNcard)
    have : (H.interedges L₀ N).card < a * b :=
      hedgeUpper.trans_lt (hstrict.trans_le hdoubleCountArithmetic)
    omega
  have hN₀subV₂ : N₀ ⊆ V₂ :=
    hN₀subN.trans (hNsub.trans Finset.inter_subset_left)
  have hN₀LO : N₀ ⊆ L ∩ C67.O :=
    hN₀subN.trans (hNsub.trans Finset.inter_subset_right)
  have hN₀degree : ∀ D ∈ N₀, u ≤ Erdos547EC2.degreeInto R D S₁ := by
    intro D hD
    have hDLO := hN₀LO hD
    let AD := L₀.filter fun C ↦ H.Adj D C
    let Bad := AD.filter fun C ↦ ¬ R.Adj D (endpoint (edgeOf C) 1)
    let GoodD := AD \ Bad
    have hADcard : t ≤ AD.card := by
      have htD := (Finset.mem_filter.mp hD).2
      simpa [AD, Erdos547EC2.degreeInto] using htD
    have hBadL₁ : Bad ⊆ L₁ := by
      intro C hC
      exact hL₀L₁ (Finset.mem_filter.mp (Finset.mem_filter.mp hC).1).1
    have hBadImageCard : (Bad.image edgeOf).card = Bad.card := by
      apply Finset.card_image_iff.mpr
      exact hedgeOf_inj_on.mono (by simpa using hBadL₁)
    have hBadImageSub : Bad.image edgeOf ⊆ U D := by
      intro e he
      obtain ⟨C, hCBad, rfl⟩ := Finset.mem_image.mp he
      have hCAD := Finset.mem_filter.mp hCBad
      have hCA := Finset.mem_filter.mp hCAD.1
      have hCL₁ := hL₀L₁ hCA.1
      have hedata := hedgeOf C hCL₁
      have hpos : eta ≤ density D (endpoint (edgeOf C) 0) := by
        rw [hedata.2.1]
        exact hHdense hCA.2
      have hzero : density D (endpoint (edgeOf C) 1) = 0 :=
        hnonadjZero hCAD.2
      apply mem_unbalancedEdges.mpr
      refine ⟨hedata.1, ?_⟩
      rw [hzero, sub_zero, abs_of_nonneg (heta.le.trans hpos)]
      exact hpos
    have hBadcard : Bad.card ≤ q := by
      calc
        Bad.card = (Bad.image edgeOf).card := hBadImageCard.symm
        _ ≤ (U D).card := Finset.card_le_card hBadImageSub
        _ ≤ q := by
          obtain ⟨A, hA, hDA⟩ := Finset.mem_biUnion.mp (hN₀subN hD)
          have hAdj : H.Adj A D := (H.mem_neighborFinset A D).mp
            (Finset.mem_inter.mp ((hNC A hA).2 hDA)).2
          exact hunbalanced_neighbor D hDLO ⟨A, hL₀LO hA, (hHR hAdj).symm⟩
    have hGoodDcard : u ≤ GoodD.card := by
      have hpart := Finset.card_sdiff_add_card_inter AD Bad
      have hinter : (AD ∩ Bad).card ≤ Bad.card :=
        Finset.card_le_card Finset.inter_subset_right
      change GoodD.card + (AD ∩ Bad).card = AD.card at hpart
      omega
    let Partners := GoodD.image fun C ↦ endpoint (edgeOf C) 1
    have hPartnersCard : Partners.card = GoodD.card := by
      apply Finset.card_image_iff.mpr
      apply hpartner_inj_on.mono
      intro C hC
      exact hL₀L₁ (Finset.mem_filter.mp (Finset.mem_sdiff.mp hC).1).1
    calc
      u ≤ GoodD.card := hGoodDcard
      _ = Partners.card := hPartnersCard.symm
      _ ≤ Erdos547EC2.degreeInto R D S₁ := by
        unfold Erdos547EC2.degreeInto
        apply Finset.card_le_card
        intro Y hY
        obtain ⟨C, hCGood, rfl⟩ := Finset.mem_image.mp hY
        have hCAD := Finset.mem_filter.mp (Finset.mem_sdiff.mp hCGood).1
        have hCL₁ := hL₀L₁ hCAD.1
        exact Finset.mem_filter.mpr ⟨(hedgeOf C hCL₁).2.2,
          by_contra fun h ↦ (Finset.mem_sdiff.mp hCGood).2
            (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hCGood).1, h⟩)⟩
  have hfinalNat : z * u ≤ (R.interedges S₁ V₂).card := by
    calc
      z * u ≤ N₀.card * u := Nat.mul_le_mul_right u hzN₀
      _ ≤ (R.interedges N₀ S₁).card :=
        Erdos547EC2.card_mul_le_card_interedges_of_subset_of_degreeInto
          R (Finset.Subset.rfl) hN₀degree
      _ = (R.interedges S₁ N₀).card := Rel.card_interedges_comm N₀ S₁
      _ ≤ (R.interedges S₁ V₂).card := by
        apply Finset.card_le_card
        intro p hp
        have hp' := (SimpleGraph.mem_interedges_iff R).mp hp
        exact (SimpleGraph.mem_interedges_iff R).mpr
          ⟨hp'.1, hN₀subV₂ hp'.2.1, hp'.2.2⟩
  have hfinalReal : 16 * rho * (k : ℝ) ^ 2 ≤
      ((R.interedges S₁ V₂).card : ℝ) := by
    exact hfinalArithmetic.trans (by exact_mod_cast hfinalNat)
  linarith

theorem crossing_lt_of_twoThresholds
    {E : Type u} [Fintype E] [DecidableEq E]
    {K : Type v} [Fintype K] [DecidableEq K]
    (R H R' : SimpleGraph K) [DecidableRel R.Adj] [DecidableRel H.Adj] [DecidableRel R'.Adj]
    (hHR : H ≤ R) (hR'H : R' ≤ H)
    (L L₁ V₂ S₁ : Finset K)
    (M : Finset E) (endpoint : E → Fin 2 → K)
    (edgeOf : K → E) (density : K → K → ℝ)
    (eta rho rho₁ : ℝ) (k a b q miss t u z : ℕ)
    (C67 : Claim67Certificate R L miss)
    (heta : 0 < eta) (hk : 0 < k) (haNat : 0 < a)
    (ha : (a : ℝ) ≤ 8 * rho₁ * k)
    (hcutCard : L₁.card + V₂.card ≤ 2 * k)
    (hlocalArithmetic : 2 * (b + q + 1) + miss ≤ a)
    (hpartnerArithmetic : u + q ≤ t)
    (hdoubleCountArithmetic : z * a + V₂.card * t ≤ a * b)
    (hfinalArithmetic : 16 * rho * (k : ℝ) ^ 2 ≤ (z * u : ℕ))
    (h617 : ((R.interedges S₁ V₂).card : ℝ) <
      16 * rho * (k : ℝ) ^ 2)
    (hL₁ : L₁ ⊆ L ∩ C67.O)
    (hendpoint_inj : Function.Injective
      (fun ec : E × Fin 2 ↦ endpoint ec.1 ec.2))
    (hMedge : ∀ e ∈ M, C67.M.Adj (endpoint e 0) (endpoint e 1))
    (hlargeEnd : ∀ e ∈ M, endpoint e 0 ∈ L)
    (hV₂pair : ∀ e ∈ M, endpoint e 0 ∈ V₂ ↔ endpoint e 1 ∈ V₂)
    (hV₂covered : ∀ v ∈ V₂, v ∈ matchingSupport C67.M →
      v ∈ indexedMatchingSupport M endpoint)
    (hedgeOf : ∀ C ∈ L₁,
      edgeOf C ∈ M ∧ endpoint (edgeOf C) 0 = C ∧ endpoint (edgeOf C) 1 ∈ S₁)
    (hR'dense : ∀ ⦃A B⦄, R'.Adj A B → 2 * eta ≤ density A B)
    (hHdense : ∀ ⦃A B⦄, H.Adj A B → eta ≤ density A B)
    (hdenseH : ∀ ⦃A B⦄, eta ≤ density A B → H.Adj A B)
    (hnonadjZero : ∀ ⦃A B⦄, ¬ R.Adj A B → density A B = 0)
    (hunbalanced_card : ∀ A ∈ L ∩ C67.O,
      (unbalancedEdges M
        (fun e c ↦ density A (endpoint e c)) eta).card ≤ q) :
    ((R'.interedges L₁ V₂).card : ℝ) < 16 * rho₁ * (k : ℝ) ^ 2 := by
  exact crossing_lt_of_local_twoThresholds R H R' hHR hR'H L L₁ V₂ S₁ M endpoint
    edgeOf density eta rho rho₁ k a b q miss t u z C67 heta hk haNat ha hcutCard
    hlocalArithmetic hpartnerArithmetic hdoubleCountArithmetic hfinalArithmetic h617 hL₁
    hendpoint_inj hMedge hlargeEnd hV₂pair hV₂covered hedgeOf hR'dense hHdense hdenseH hnonadjZero
    (fun A hA => hunbalanced_card A (hL₁ hA)) (fun A hA _ => hunbalanced_card A hA)

end Erdos547b.ZhaoClaim618TwoThreshold

#print axioms Erdos547b.ZhaoClaim618TwoThreshold.crossing_lt_of_twoThresholds
#print axioms Erdos547b.ZhaoClaim618TwoThreshold.crossing_lt_of_local_twoThresholds
