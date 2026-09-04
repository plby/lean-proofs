/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma615
import ErdosProblems.Erdos547b.EC2

/-!
# Zhao's Claim 6.18

This is the finite reduced-graph argument on pages 37--38 of Zhao (2011).
The matching is represented by a finite edge set `M` and two endpoint maps.
The endpoint maps are tied to the genuine matching in a `Claim67Certificate`;
the only theorem which turns absence of the target tree into a restriction on
matching edges is the concrete, copy-valued Lemma 6.15.
-/

open scoped BigOperators SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoStability

open Finset SimpleGraph
open Erdos547b.ZhaoLemma615

universe u v w x

/-- The cluster vertices represented by an indexed submatching. -/
def indexedMatchingSupport {E : Type u} [DecidableEq E]
    {K : Type v} [DecidableEq K] (M : Finset E)
    (endpoint : E → Fin 2 → K) : Finset K :=
  M.biUnion fun e ↦ {endpoint e 0, endpoint e 1}

@[simp] theorem mem_indexedMatchingSupport {E : Type u} [DecidableEq E]
    {K : Type v} [DecidableEq K] {M : Finset E}
    {endpoint : E → Fin 2 → K} {z : K} :
    z ∈ indexedMatchingSupport M endpoint ↔
      ∃ e ∈ M, z = endpoint e 0 ∨ z = endpoint e 1 := by
  simp [indexedMatchingSupport]

/-- Matching edges which contain a prescribed `R'`-neighbor in `V₂`. -/
def candidateEdges {E : Type u} [DecidableEq E]
    {K : Type v} [DecidableEq K] (R' : SimpleGraph K)
    [DecidableRel R'.Adj] (M : Finset E) (endpoint : E → Fin 2 → K)
    (C : K) (V₂ : Finset K) : Finset E :=
  M.filter fun e ↦
    (endpoint e 0 ∈ V₂ ∧ R'.Adj C (endpoint e 0)) ∨
      (endpoint e 1 ∈ V₂ ∧ R'.Adj C (endpoint e 1))

@[simp] theorem mem_candidateEdges {E : Type u} [DecidableEq E]
    {K : Type v} [DecidableEq K] {R' : SimpleGraph K}
    [DecidableRel R'.Adj] {M : Finset E} {endpoint : E → Fin 2 → K}
    {C : K} {V₂ : Finset K} {e : E} :
    e ∈ candidateEdges R' M endpoint C V₂ ↔
      e ∈ M ∧ ((endpoint e 0 ∈ V₂ ∧ R'.Adj C (endpoint e 0)) ∨
        (endpoint e 1 ∈ V₂ ∧ R'.Adj C (endpoint e 1))) := by
  simp [candidateEdges]

/-- The elementary high-degree pruning at the start of Claim 6.18. -/
theorem exists_many_high_degree_of_many_interedges
    {K : Type*} [Fintype K] [DecidableEq K]
    (R : SimpleGraph K) [DecidableRel R.Adj]
    (L V₂ : Finset K) (a k : ℕ)
    (hk : 0 < k)
    (hcard : L.card + V₂.card ≤ 2 * k)
    (hedges : 2 * a * k ≤ (R.interedges L V₂).card) :
    ∃ L₀ ⊆ L, L₀.card = a ∧
      ∀ C ∈ L₀, a ≤ Erdos547EC2.degreeInto R C V₂ := by
  classical
  let : Std.Symm R.Adj := ⟨fun _ _ h ↦ h.symm⟩
  let H := L.filter fun C ↦ a ≤ Erdos547EC2.degreeInto R C V₂
  by_cases ha0 : a = 0
  · subst a
    exact ⟨∅, Finset.empty_subset _, rfl, by simp⟩
  have haH : a ≤ H.card := by
    by_contra h
    have hHlt : H.card < a := Nat.lt_of_not_ge h
    have haPos : 0 < a := Nat.pos_of_ne_zero ha0
    have hsum := Erdos547EC2.sum_degreeInto_eq_card_interedges R L V₂
    have hsplit :
        ∑ C ∈ L, Erdos547EC2.degreeInto R C V₂ =
          (∑ C ∈ H, Erdos547EC2.degreeInto R C V₂) +
            ∑ C ∈ L \ H, Erdos547EC2.degreeInto R C V₂ := by
      rw [← Finset.sum_inter_add_sum_sdiff L H]
      congr 2
      exact Finset.inter_eq_right.mpr (filter_subset _ _)
    have hhigh :
        ∑ C ∈ H, Erdos547EC2.degreeInto R C V₂ ≤ H.card * V₂.card := by
      exact Finset.sum_le_card_nsmul H
        (fun C ↦ Erdos547EC2.degreeInto R C V₂) V₂.card
        (fun C _ ↦ Erdos547EC2.degreeInto_le_card R C V₂)
    have hlow :
        ∑ C ∈ L \ H, Erdos547EC2.degreeInto R C V₂ ≤
          L.card * (a - 1) := by
      calc
        ∑ C ∈ L \ H, Erdos547EC2.degreeInto R C V₂ ≤
            (L \ H).card * (a - 1) := by
          apply Finset.sum_le_card_nsmul
          intro C hC
          have hnot : C ∉ H := (Finset.mem_sdiff.mp hC).2
          have hCL : C ∈ L := (Finset.mem_sdiff.mp hC).1
          have hlt : Erdos547EC2.degreeInto R C V₂ < a := by
            simpa [H, hCL] using hnot
          omega
        _ ≤ L.card * (a - 1) := by
          exact Nat.mul_le_mul_right (a - 1)
            (Finset.card_le_card Finset.sdiff_subset)
    rw [hsplit] at hsum
    have hstrict : (R.interedges L V₂).card < a * (L.card + V₂.card) := by
      rw [← hsum]
      calc
        (∑ C ∈ H, Erdos547EC2.degreeInto R C V₂) +
              ∑ C ∈ L \ H, Erdos547EC2.degreeInto R C V₂
            ≤ H.card * V₂.card + L.card * (a - 1) :=
              Nat.add_le_add hhigh hlow
        _ ≤ (a - 1) * V₂.card + L.card * (a - 1) := by
          exact Nat.add_le_add_right
            (Nat.mul_le_mul_right V₂.card (by omega : H.card ≤ a - 1)) _
        _ = (a - 1) * (L.card + V₂.card) := by ring
        _ < a * (L.card + V₂.card) := by
          have hpositive : 0 < L.card + V₂.card := by
            by_contra hzero
            have hLV : L.card + V₂.card = 0 := Nat.eq_zero_of_not_pos hzero
            have hL : L = ∅ := Finset.card_eq_zero.mp (by omega)
            have hV : V₂ = ∅ := Finset.card_eq_zero.mp (by omega)
            subst L
            subst V₂
            simp at hedges
            omega
          exact Nat.mul_lt_mul_of_pos_right (by omega : a - 1 < a) hpositive
    have : (R.interedges L V₂).card < 2 * a * k := by
      calc
        (R.interedges L V₂).card < a * (L.card + V₂.card) := hstrict
        _ ≤ a * (2 * k) := Nat.mul_le_mul_left a hcard
        _ = 2 * a * k := by ring
    omega
  obtain ⟨L₀, hL₀H, hL₀card⟩ := Finset.exists_subset_card_eq haH
  refine ⟨L₀, hL₀H.trans (filter_subset _ _), hL₀card, ?_⟩
  intro C hC
  have := hL₀H hC
  exact (by simpa [H] using this : C ∈ L ∧ a ≤ Erdos547EC2.degreeInto R C V₂).2

/-! The main source-shaped theorem follows after a few local counting helpers. -/

/-- **Zhao 2011, Claim 6.18.**  Here `a,b,t,u,z` are the integral
rounding parameters for `8ρ₁k, 3ρ₁k, 12ρ₁²k, 11ρ₁²k` and
`3(1-8η)ρ₁k/2`.  Their displayed hypotheses are precisely the finite
inequalities used in (6.24)--(6.25) and in the double count on page 38. -/
theorem zhaoClaim618
    {E : Type u} [Fintype E] [DecidableEq E]
    {K : Type v} [Fintype K] [DecidableEq K]
    {TreeVertex : Type w} [Fintype TreeVertex] [DecidableEq TreeVertex]
    {HostVertex : Type x} [Fintype HostVertex] [DecidableEq HostVertex]
    (T : SimpleGraph TreeVertex) [DecidableRel T.Adj]
    (globalRoot : TreeVertex) (small : ℕ)
    (P : Erdos547b.TreePartition.ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph HostVertex) [DecidableRel G.Adj]
    (R R' : SimpleGraph K) [DecidableRel R.Adj] [DecidableRel R'.Adj]
    (hR'R : R' ≤ R)
    (L L₁ V₂ S₁ : Finset K)
    (M : Finset E) (endpoint : E → Fin 2 → K)
    (edgeOf : K → E) (density : K → K → ℝ)
    (eta rho rho₁ : ℝ) (k a b q miss t u z : ℕ)
    (C67 : Claim67Certificate R L miss)
    (hrho₁ : rho₁ = Real.rpow rho (1 / 3 : ℝ))
    (heta : 0 < eta) (hk : 0 < k) (haNat : 0 < a) (hq : 0 < q)
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
    (hRdense : ∀ ⦃A B⦄, R.Adj A B → eta ≤ density A B)
    (hdenseR : ∀ ⦃A B⦄, eta ≤ density A B → R.Adj A B)
    (hnonadjZero : ∀ ⦃A B⦄, ¬ R.Adj A B → density A B = 0)
    (hunbalanced_card : ∀ A ∈ L ∩ C67.O,
      (unbalancedEdges M
        (fun e c ↦ density A (endpoint e c)) eta).card ≤ q) :
    ((R'.interedges L₁ V₂).card : ℝ) < 16 * rho₁ * (k : ℝ) ^ 2 := by
  classical
  let : Std.Symm R.Adj := ⟨fun _ _ h ↦ h.symm⟩
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
      R.Adj A (endpoint e 0) ∧ R.Adj A (endpoint e 1) := by
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
      refine ⟨hR'R he0.2, hdenseR (by linarith)⟩
    · have hd1 := hR'dense he1.2
      refine ⟨hdenseR (by linarith), hR'R he1.2⟩
  let U : K → Finset E := fun A ↦
    unbalancedEdges M (fun e c ↦ density A (endpoint e c)) eta
  let Q : K → Finset E := fun A ↦ candidateEdges R' M endpoint A V₂
  let Good : K → Finset E := fun A ↦ Q A \ U A
  let NC : K → Finset K := fun A ↦
    ((Good A).image fun e ↦ endpoint e 0).filter fun D ↦ D ∈ C67.O
  have hUcard (A : K) (hA : A ∈ L ∩ C67.O) : (U A).card ≤ q := by
    exact hunbalanced_card A hA
  have hNC (A : K) (hA : A ∈ L₀) :
      b ≤ (NC A).card ∧ NC A ⊆ V₂ ∩ (L ∩ C67.O) ∩ R.neighborFinset A := by
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
      have hUc := hUcard A hALO
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
          refine ⟨C67.M.edge_vert (hMedge e heM), endpoint e 1, hMedge e heM, hadj.1, hadj.2⟩
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
  have hL₀degreeN : ∀ A ∈ L₀, b ≤ Erdos547EC2.degreeInto R A N := by
    intro A hA
    calc
      b ≤ (NC A).card := (hNC A hA).1
      _ ≤ Erdos547EC2.degreeInto R A N := by
        unfold Erdos547EC2.degreeInto
        apply Finset.card_le_card
        intro D hD
        have hprops := (hNC A hA).2 hD
        exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨A, hA, hD⟩,
          by simpa using (Finset.mem_inter.mp hprops).2⟩
  have hHlower : a * b ≤ (R.interedges L₀ N).card := by
    rw [← hL₀card]
    exact Erdos547EC2.card_mul_le_card_interedges_of_subset_of_degreeInto
      R (Finset.Subset.rfl) hL₀degreeN
  let N₀ : Finset K := N.filter fun D ↦
    t ≤ Erdos547EC2.degreeInto R D L₀
  have hN₀subN : N₀ ⊆ N := Finset.filter_subset _ _
  have hzN₀ : z ≤ N₀.card := by
    by_contra hz
    have hzlt : N₀.card < z := Nat.lt_of_not_ge hz
    have hsum := Erdos547EC2.sum_degreeInto_eq_card_interedges R N L₀
    have hcomm : (R.interedges N L₀).card = (R.interedges L₀ N).card :=
      Rel.card_interedges_comm N L₀
    have hsplit :
        ∑ D ∈ N, Erdos547EC2.degreeInto R D L₀ =
          (∑ D ∈ N₀, Erdos547EC2.degreeInto R D L₀) +
            ∑ D ∈ N \ N₀, Erdos547EC2.degreeInto R D L₀ := by
      rw [← Finset.sum_inter_add_sum_sdiff N N₀]
      congr 2
      exact Finset.inter_eq_right.mpr hN₀subN
    have hhigh :
        ∑ D ∈ N₀, Erdos547EC2.degreeInto R D L₀ ≤ N₀.card * a := by
      rw [← hL₀card]
      exact Finset.sum_le_card_nsmul N₀
        (fun D ↦ Erdos547EC2.degreeInto R D L₀) L₀.card
        (fun D _ ↦ Erdos547EC2.degreeInto_le_card R D L₀)
    have hlow :
        ∑ D ∈ N \ N₀, Erdos547EC2.degreeInto R D L₀ ≤ N.card * t := by
      calc
        ∑ D ∈ N \ N₀, Erdos547EC2.degreeInto R D L₀ ≤
            (N \ N₀).card * t := by
          apply Finset.sum_le_card_nsmul
          intro D hD
          have hDN := (Finset.mem_sdiff.mp hD).1
          have hDnot := (Finset.mem_sdiff.mp hD).2
          have : ¬ t ≤ Erdos547EC2.degreeInto R D L₀ := by
            intro htD
            exact hDnot (Finset.mem_filter.mpr ⟨hDN, htD⟩)
          omega
        _ ≤ N.card * t :=
          Nat.mul_le_mul_right t (Finset.card_le_card Finset.sdiff_subset)
    have hedgeUpper : (R.interedges L₀ N).card ≤ N₀.card * a + N.card * t := by
      rw [← hcomm, ← hsum, hsplit]
      exact Nat.add_le_add hhigh hlow
    have hstrict : N₀.card * a + N.card * t < z * a + V₂.card * t := by
      exact Nat.add_lt_add_of_lt_of_le
        (Nat.mul_lt_mul_of_pos_right hzlt haNat)
        (Nat.mul_le_mul_right t hNcard)
    have : (R.interedges L₀ N).card < a * b :=
      hedgeUpper.trans_lt (hstrict.trans_le hdoubleCountArithmetic)
    omega
  have hN₀subV₂ : N₀ ⊆ V₂ :=
    hN₀subN.trans (hNsub.trans Finset.inter_subset_left)
  have hN₀LO : N₀ ⊆ L ∩ C67.O :=
    hN₀subN.trans (hNsub.trans Finset.inter_subset_right)
  have hN₀degree : ∀ D ∈ N₀, u ≤ Erdos547EC2.degreeInto R D S₁ := by
    intro D hD
    have hDLO := hN₀LO hD
    let AD := L₀.filter fun C ↦ R.Adj D C
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
        exact hRdense hCA.2
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
        _ ≤ q := hUcard D hDLO
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

end Erdos547b.ZhaoStability

#print axioms Erdos547b.ZhaoStability.exists_many_high_degree_of_many_interedges
#print axioms Erdos547b.ZhaoStability.zhaoClaim618
