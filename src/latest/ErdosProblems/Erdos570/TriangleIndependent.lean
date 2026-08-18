/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.TriangleArithmetic
import ErdosProblems.Erdos570.TriangleCoreExtension
import ErdosProblems.Erdos570.TriangleHost
import ErdosProblems.Erdos570.TrianglePermutation
import ErdosProblems.Erdos570.TriangleTarget

/-!
# The independent minimum-degree branch for triangles
-/

open scoped BigOperators SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

/-- The candidate-set argument of Goddard--Kleitman.  If the vertices of
minimum target degree are independent, a triangle-free red host of order at
least `2m+1` necessarily contains the target in blue. -/
theorem triangle_independent_minimum_contradiction
    {H : GraphCode} {N : ℕ} (C : SimpleGraph (Fin N))
    [DecidableRel C.Adj] [DecidableRel H.graph.Adj]
    (hH : NoIsolated H) (hN : 2 * H.edgeCount + 1 ≤ N)
    (v : Fin H.vertexCount)
    (hvmin : H.graph.degree v = H.graph.minDegree)
    (hδ : 3 ≤ H.graph.degree v)
    (hlarge : 22 ≤ H.edgeCount)
    (hSind : H.graph.IsIndepSet
      (minimumDegreeVertices H.graph v : Set (Fin H.vertexCount)))
    (hdelete : RamseyAt (cycleCode 3)
      (supportCode (deleteVertexCode H v)) N)
    (hnoCycle : ¬ (cycleCode 3).graph ⊑ C)
    (hnoH : ¬ H.graph ⊑ Cᶜ) : False := by
  classical
  let p := H.vertexCount
  let m := H.edgeCount
  let δ := H.graph.degree v
  let S := minimumDegreeVertices H.graph v
  have hδpos : 0 < δ := by omega
  have hvS : v ∈ S := by simp [S]
  have hfree : C.CliqueFree 3 :=
    cliqueFree_three_of_cycleCode_not_isContained C hnoCycle
  obtain ⟨T, hTclique, hTcard⟩ := Cᶜ.exists_isNClique_cliqueNum
  let Y : Finset (Fin N) := Finset.univ \ T
  have hTY : Disjoint T Y := by
    rw [Finset.disjoint_left]
    intro x hxT hxY
    exact (Finset.mem_sdiff.mp hxY).2 hxT
  have hTlt : T.card < p := by
    by_contra hnot
    have hpT : p ≤ T.card := Nat.le_of_not_gt hnot
    apply hnoH
    exact isContained_of_isClique_card_le H.graph Cᶜ T hTclique
      (by simpa [p] using hpT)
  let t := T.card
  let y := Y.card
  let f := p - t
  have hf : 1 ≤ f := by dsimp only [f, t]; omega
  have hpf : p = t + f := by dsimp only [f, t]; omega
  have hTYcard : t + y = N := by
    have hTleN : T.card ≤ N := by
      simpa using Finset.card_le_card (Finset.subset_univ T)
    dsimp only [t, y, Y]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ T)]
    simp only [Finset.card_univ, Fintype.card_fin]
    exact Nat.add_sub_of_le hTleN
  have hny : 2 * m + 1 ≤ t + y := by
    rw [hTYcard]
    simpa [m] using hN
  have hp2m : p ≤ 2 * m := by
    simpa [p, m] using NoIsolated.vertexCount_le_twice_edgeCount hH
  have hroom : H.vertexCount - 1 ≤ N := by
    dsimp only [p] at hp2m
    omega
  have hdeleteRaw : N - (H.vertexCount - 1) ≤ δ * T.card := by
    have hobs := deletion_obstruction_le_compl_cliqueNum
      C v (by simpa [δ] using hδpos) hroom hdelete hnoCycle hnoH
    rw [← hTcard] at hobs
    simpa [δ] using hobs
  have hdeleteNum : 2 * m + 2 ≤ p + δ * t := by
    dsimp only [p, m, δ, t] at hdeleteRaw ⊢
    omega
  have hdegrees : (δ + 1) * p ≤ 2 * m + S.card := by
    simpa [δ, p, m, S, GraphCode.edgeCount_eq_card_edgeFinset] using
      minimumDegreeVertices_degree_sum H.graph v hvmin
  have hindependent : δ * S.card ≤ m := by
    simpa [δ, m, S, GraphCode.edgeCount_eq_card_edgeFinset] using
      minimumDegreeVertices_independent_bound H.graph v hSind
  obtain ⟨htStrong, hδfS, hδfY, htLower, hyLower, hkey⟩ :=
    triangle_dense_numeric (δ := δ) (m := m) (p := p)
      (s := S.card) (t := t) (f := f) (y := y)
      hδ hf hpf hny hdeleteNum hdegrees hindependent
  have hfS : f ≤ S.card := by
    exact (show f ≤ δ * f by
      calc
        f = 1 * f := by ring
        _ ≤ δ * f := Nat.mul_le_mul_right f (by omega)).trans hδfS
  have hcoreCard : Fintype.card {w : Fin H.vertexCount // w ∉ S} ≤ T.card := by
    have hcomp : Fintype.card {w : Fin H.vertexCount // w ∉ S} =
        p - S.card := by
      calc
        _ = Fintype.card (Fin H.vertexCount) -
            Fintype.card {w : Fin H.vertexCount // w ∈ S} := by
              simpa using Fintype.card_subtype_compl
                (fun w : Fin H.vertexCount ↦ w ∈ S)
        _ = p - S.card := by simp [p]
    rw [hcomp]
    dsimp only [t] at hpf ⊢
    omega
  let core : {w : Fin H.vertexCount // w ∉ S} ↪ T :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (by
      simpa using hcoreCard))
  obtain ⟨cross, hcross⟩ := exists_uniform_blue_cross_family
    C hfree T Y hTY hTcard
  have hcrossCard (x : T) : (cross x).card = y - t := by
    simpa [y, t] using (hcross x).1
  have hcrossBlue (x : T) (z : Y) (hz : z ∈ cross x) :
      Cᶜ.Adj x.1 z.1 := (hcross x).2 z hz
  let neighborCore (x : S) :
      H.graph.neighborFinset x.1 ↪ T :=
    { toFun := fun w ↦ core ⟨w.1, by
          intro hwS
          have hadj := (H.graph.mem_neighborFinset x.1 w.1).mp w.2
          exact hSind x.2 hwS hadj.ne hadj⟩
      inj' := by
        intro a b hab
        apply Subtype.ext
        exact congrArg
          (fun z : {w : Fin H.vertexCount // w ∉ S} ↦ z.1)
          (core.injective hab) }
  let I : S → DeltaSubsets T δ := fun x ↦
    ⟨Finset.univ.map (neighborCore x), by
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [Finset.card_map]
      simpa [δ, S] using (mem_minimumDegreeVertices H.graph v x.1).mp x.2⟩
  let deg : Y → ℕ := fun z ↦
    (Finset.univ.filter fun x : T ↦ z ∈ cross x).card
  have hsumDeg : ∑ z : Y, deg z = t * (y - t) := by
    rw [← sum_cross_degrees cross]
    simp_rw [hcrossCard]
    simp [t]
  have htδ : δ ≤ t := by omega
  have ht7 : 7 ≤ t := by
    by_contra hnot
    have htUpper : t ≤ 6 := by omega
    have hfOne : f = 1 := by
      have hδ' : 3 ≤ δ := by simpa [δ] using hδ
      have hcoef : 4 ≤ 2 * δ - 2 := by omega
      by_contra hfne
      have hfTwo : 2 ≤ f := by omega
      have heigh : 8 ≤ (2 * δ - 2) * f := by
        calc
          8 = 4 * 2 := by norm_num
          _ ≤ (2 * δ - 2) * f := Nat.mul_le_mul hcoef hfTwo
      omega
    have hpUpper : p ≤ 7 := by omega
    have hdegreeUpper (z : Fin H.vertexCount) :
        H.graph.degree z ≤ p - 1 := by
      have hz := H.graph.degree_lt_card_verts z
      simpa [p] using (Nat.le_sub_one_of_lt hz)
    have hsumUpper : ∑ z : Fin H.vertexCount, H.graph.degree z ≤
        ∑ _z : Fin H.vertexCount, (p - 1) :=
      Finset.sum_le_sum fun z _ ↦ hdegreeUpper z
    have htwom : ∑ z : Fin H.vertexCount, H.graph.degree z = 2 * m := by
      simpa [m, GraphCode.edgeCount_eq_card_edgeFinset] using
        H.graph.sum_degrees_eq_twice_card_edges
    rw [htwom] at hsumUpper
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.nsmul_eq_mul] at hsumUpper
    have hmUpper : m ≤ 21 := by nlinarith
    omega
  have hty : t < y := by
    have htpos : 0 < t := hδpos.trans_le htδ
    have : t < (δ - 1) * t := by
      calc
        t = 1 * t := by ring
        _ < (δ - 1) * t :=
          Nat.mul_lt_mul_of_pos_right (by omega) htpos
    exact this.trans_le hyLower
  have havgFloor : δ - 1 ≤ t * (y - t) / y :=
    triangle_average_floor hδ (by omega) hyLower
  have hprod := triangle_product_lower_of_key
    (δ := δ) (m := m) (p := p) (t := t) (f := f) (y := y)
    hδ hf hpf hny ht7 htLower hyLower hkey
  have haverage : (y - t) * t.choose δ ≤
      δ * ∑ z : Y, (deg z).choose δ :=
    binomial_candidate_average deg δ t y (by simp [y])
      (by omega) htδ hty hsumDeg havgFloor hprod
  let g : DeltaSubsets T δ → ℕ := fun J ↦
    (commonCandidates cross J.1).card
  have hsumCandidates : ∑ J : DeltaSubsets T δ, g J =
      ∑ z : Y, (deg z).choose δ := by
    simpa only [g, deg, DeltaSubsets] using
      sum_card_commonCandidates_subtype cross δ
  have hZcard : Fintype.card (DeltaSubsets T δ) = t.choose δ := by
    rw [show Fintype.card (DeltaSubsets T δ) =
        ((Finset.univ : Finset T).powersetCard δ).card by
      exact Fintype.card_coe _]
    rw [Finset.card_powersetCard]
    simp [t]
  have havg' : (y - t) * Fintype.card (DeltaSubsets T δ) ≤
      δ * ∑ J : DeltaSubsets T δ, g J := by
    rw [hZcard, hsumCandidates]
    exact haverage
  have hZf : Fintype.card (DeltaSubsets T δ) * f ≤
      ∑ J : DeltaSubsets T δ, g J := by
    apply Nat.le_of_mul_le_mul_left (c := δ)
    · calc
        δ * (Fintype.card (DeltaSubsets T δ) * f) =
            (δ * f) * Fintype.card (DeltaSubsets T δ) := by ring
        _ ≤ (y - t) * Fintype.card (DeltaSubsets T δ) := by gcongr
        _ ≤ δ * ∑ J : DeltaSubsets T δ, g J := havg'
    · exact hδpos
  have hfG : f * (y - t) * Fintype.card (DeltaSubsets T δ) ≤
      S.card * ∑ J : DeltaSubsets T δ, g J := by
    calc
      f * (y - t) * Fintype.card (DeltaSubsets T δ) =
          f * ((y - t) * Fintype.card (DeltaSubsets T δ)) := by ring
      _ ≤ f * (δ * ∑ J : DeltaSubsets T δ, g J) := by gcongr
      _ = (δ * f) * ∑ J : DeltaSubsets T δ, g J := by ring
      _ ≤ S.card * ∑ J : DeltaSubsets T δ, g J := by gcongr
  have hpermAverage : Fintype.card (DeltaSubsets T δ) *
        max (S.card * f) (f * (y - t)) ≤
      Fintype.card S * ∑ J : DeltaSubsets T δ, g J := by
    rw [mul_max, max_le_iff]
    constructor
    · calc
        Fintype.card (DeltaSubsets T δ) * (S.card * f) =
            S.card * (Fintype.card (DeltaSubsets T δ) * f) := by ring
        _ ≤ S.card * ∑ J : DeltaSubsets T δ, g J := by gcongr
        _ = Fintype.card S * ∑ J : DeltaSubsets T δ, g J := by simp
    · calc
        Fintype.card (DeltaSubsets T δ) * (f * (y - t)) =
            f * (y - t) * Fintype.card (DeltaSubsets T δ) := by ring
        _ ≤ S.card * ∑ J : DeltaSubsets T δ, g J := hfG
        _ = Fintype.card S * ∑ J : DeltaSubsets T δ, g J := by simp
  have hSpos : 0 < S.card := lt_of_lt_of_le hf hfS
  letI : Nonempty S := Fintype.card_pos_iff.mp (by simpa using hSpos)
  obtain ⟨σ, hσ⟩ := exists_permutation_with_large_sum g I hpermAverage
  let cand : S → Finset Y := fun x ↦
    commonCandidates cross (permuteDeltaSubset σ (I x)).1
  have hcandBound : ∀ x : S, (cand x).card ≤ y - t := by
    intro x
    have hIcard : (permuteDeltaSubset σ (I x)).1.card = δ :=
      (Finset.mem_powersetCard.mp (permuteDeltaSubset σ (I x)).2).2
    have hnonempty : (permuteDeltaSubset σ (I x)).1.Nonempty :=
      Finset.card_pos.mp (by rw [hIcard]; omega)
    obtain ⟨z, hz⟩ := hnonempty
    exact (card_commonCandidates_le_of_mem cross _ hz).trans_eq
      (hcrossCard z)
  have hsumCandLower : max (S.card * f) (f * (y - t)) ≤
      ∑ x : S, (cand x).card := by
    simpa [cand, g] using hσ
  have hsf : Fintype.card S * f ≤ ∑ x : S, (cand x).card := by
    simpa using (le_max_left (S.card * f) (f * (y - t))).trans
      hsumCandLower
  have hfG' : f * (y - t) ≤ ∑ x : S, (cand x).card :=
    (le_max_right (S.card * f) (f * (y - t))).trans hsumCandLower
  obtain ⟨pick, choose, hpick, hchoose, hchooseMem⟩ :=
    exists_selected_distinct_representatives cand hf
      (by simpa using hfS) hcandBound hsf hfG'
  let pickW : Fin f ↪ Fin H.vertexCount :=
    { toFun := fun i ↦ (pick i).1
      inj' := fun i j hij ↦ hpick (Subtype.ext hij) }
  let P : Finset (Fin H.vertexCount) := Finset.univ.map pickW
  have hPcard : P.card = p - T.card := by
    dsimp only [P]
    rw [Finset.card_map]
    simp [p, f, t]
  have hPS : P ⊆ S := by
    intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨i, -, rfl⟩ := hx
    exact (pick i).2
  let idx : P → Fin f := fun x ↦
    Classical.choose (Finset.mem_map.mp x.2)
  have hidx (x : P) : pickW (idx x) = x.1 :=
    (Classical.choose_spec (Finset.mem_map.mp x.2)).2
  let outside : P ↪ Y :=
    { toFun := fun x ↦ choose (idx x)
      inj' := by
        intro x x' hxx'
        have hi : idx x = idx x' := hchoose hxx'
        apply Subtype.ext
        rw [← hidx x, ← hidx x', hi] }
  let coreσ : {w : Fin H.vertexCount // w ∉ S} ↪ T :=
    core.trans σ.toEmbedding
  have hattach : ∀ x : P, ∀ w : Fin H.vertexCount, ∀ hw : w ∉ S,
      H.graph.Adj x.1 w →
        Cᶜ.Adj (outside x).1 (coreσ ⟨w, hw⟩).1 := by
    intro x w hw hxw
    let i := idx x
    have hpickx : (pick i).1 = x.1 := by
      exact hidx x
    have hadj : H.graph.Adj (pick i).1 w := by simpa [hpickx] using hxw
    have hcoreMem : coreσ ⟨w, hw⟩ ∈
        (permuteDeltaSubset σ (I (pick i))).1 := by
      rw [permuteDeltaSubset_val, Finset.mem_map]
      refine ⟨core ⟨w, hw⟩, ?_, rfl⟩
      dsimp only [I]
      rw [Finset.mem_map]
      refine ⟨⟨w, (H.graph.mem_neighborFinset (pick i).1 w).mpr hadj⟩,
        by simp, rfl⟩
    have hcandMem := hchooseMem i
    have hcrossMem : choose i ∈ cross (coreσ ⟨w, hw⟩) :=
      (mem_commonCandidates.mp (by simpa [cand] using hcandMem))
        _ hcoreMem
    have hblue := hcrossBlue (coreσ ⟨w, hw⟩) (choose i) hcrossMem
    change Cᶜ.Adj (choose (idx x)).1 (coreσ ⟨w, hw⟩).1
    simpa [i] using hblue.symm
  apply hnoH
  have hPcard' : P.card = Fintype.card (Fin H.vertexCount) - T.card := by
    simpa [p] using hPcard
  exact isContained_of_independent_core_extension S hSind T Y hTY hTclique
    (by simpa [p] using hTlt.le) P hPS hPcard' coreσ outside hattach

end Erdos570
