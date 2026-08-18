/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.TriangleCoreExtension
import ErdosProblems.Erdos570.TriangleHost
import ErdosProblems.Erdos570.TrianglePermutation
import ErdosProblems.Erdos570.TriangleTarget
import ErdosProblems.Erdos570.TriangleTwoArithmetic

/-!
# The independent degree-two branch for triangles

This is the exceptional endpoint calculation in the Goddard--Kleitman
triangle proof.  Pairwise intersections of the uniform cross-candidate sets
have the common floor `y - 2t`; Cauchy--Schwarz and the two arithmetic
endpoint estimates supply the remaining descending staircase.
-/

open scoped BigOperators SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

theorem triangle_independent_degree_two_contradiction
    {H : GraphCode} {N : ℕ} (C : SimpleGraph (Fin N))
    [DecidableRel C.Adj] [DecidableRel H.graph.Adj]
    (hH : NoIsolated H) (hN : 2 * H.edgeCount + 1 ≤ N)
    (v : Fin H.vertexCount)
    (hvmin : H.graph.degree v = H.graph.minDegree)
    (hδ : H.graph.degree v = 2)
    (hlarge : 46 ≤ H.edgeCount)
    (hSind : H.graph.IsIndepSet
      (minimumDegreeVertices H.graph v : Set (Fin H.vertexCount)))
    (hdelete : RamseyAt (cycleCode 3)
      (supportCode (deleteVertexCode H v)) N)
    (hnoCycle : ¬ (cycleCode 3).graph ⊑ C)
    (hnoH : ¬ H.graph ⊑ Cᶜ) : False := by
  classical
  let p := H.vertexCount
  let m := H.edgeCount
  let S := minimumDegreeVertices H.graph v
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
  have hdeleteRaw : N - (H.vertexCount - 1) ≤ 2 * T.card := by
    have hobs := deletion_obstruction_le_compl_cliqueNum
      C v (by rw [hδ]; omega) hroom hdelete hnoCycle hnoH
    rw [← hTcard, hδ] at hobs
    exact hobs
  have hhostUpper : t + y + 1 ≤ p + 2 * t := by
    rw [hTYcard]
    dsimp only [p, t] at hdeleteRaw ⊢
    omega
  have hdegrees : 3 * p ≤ 2 * m + S.card := by
    have hd := minimumDegreeVertices_degree_sum H.graph v hvmin
    rw [hδ] at hd
    simpa [p, m, S, GraphCode.edgeCount_eq_card_edgeFinset] using hd
  have hindependent : 2 * S.card ≤ m := by
    have hi := minimumDegreeVertices_independent_bound H.graph v hSind
    rw [hδ] at hi
    simpa [m, S, GraphCode.edgeCount_eq_card_edgeFinset] using hi
  have hsp : S.card ≤ p := by
    simpa [p] using Finset.card_le_card (Finset.subset_univ S)
  have hp11 : 11 ≤ p := by
    have hmChoose : m ≤ p.choose 2 := by
      simpa [m, p, GraphCode.edgeCount_eq_card_edgeFinset] using
        H.graph.card_edgeFinset_le_card_choose_two
    by_contra hnot
    have hp10 : p ≤ 10 := by omega
    have hchoose : p.choose 2 ≤ Nat.choose 10 2 :=
      Nat.choose_le_choose 2 hp10
    norm_num at hchoose
    omega
  obtain ⟨hft, hty, hmean, hc1, hc2⟩ :=
    triangle_degree_two_extension_arithmetic
      (m := m) (p := p) (s := S.card) (t := t) (f := f) (y := y)
      hf hp11 hpf hny hhostUpper hdegrees hindependent hsp
  have hfS : f ≤ S.card := by omega
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
  let neighborCore (x : S) : H.graph.neighborFinset x.1 ↪ T :=
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
  let I : S → DeltaSubsets T 2 := fun x ↦
    ⟨Finset.univ.map (neighborCore x), by
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [Finset.card_map]
      simpa [S] using (mem_minimumDegreeVertices H.graph v x.1).mp x.2 |>.trans hδ⟩
  let deg : Y → ℕ := fun z ↦
    (Finset.univ.filter fun x : T ↦ z ∈ cross x).card
  have hsumDeg : ∑ z : Y, deg z = t * (y - t) := by
    rw [← sum_cross_degrees cross]
    simp_rw [hcrossCard]
    simp [t]
  let g : DeltaSubsets T 2 → ℕ := fun J ↦
    (commonCandidates cross J.1).card
  have hsumCandidates : ∑ J : DeltaSubsets T 2, g J =
      ∑ z : Y, (deg z).choose 2 := by
    simpa only [g, deg, DeltaSubsets] using
      sum_card_commonCandidates_subtype cross 2
  have hZcard : Fintype.card (DeltaSubsets T 2) = t.choose 2 := by
    rw [show Fintype.card (DeltaSubsets T 2) =
        ((Finset.univ : Finset T).powersetCard 2).card by
      exact Fintype.card_coe _]
    rw [Finset.card_powersetCard]
    simp [t]
  have htpos : 1 ≤ t := by omega
  have hypos : 1 ≤ y := by omega
  have hZf : Fintype.card (DeltaSubsets T 2) * f ≤
      ∑ J : DeltaSubsets T 2, g J := by
    rw [hZcard, hsumCandidates]
    simpa using degree_two_candidate_endpoint deg (by simp [y]) hsumDeg
      hmean htpos hypos (q := f) (r := 1) (by simpa using hc1)
  let σfloor := y - 2 * t
  let G := y - t
  have hfloor (J : DeltaSubsets T 2) : σfloor ≤ g J := by
    have hJcard : J.1.card = 2 := (Finset.mem_powersetCard.mp J.2).2
    have hlower := card_commonCandidates_pair_lower cross hJcard hcrossCard
    have hlower' : 2 * (y - t) - y ≤ g J := by
      simpa [g, y] using hlower
    dsimp only [σfloor]
    omega
  have hbound (J : DeltaSubsets T 2) : g J ≤ G := by
    have hJcard : J.1.card = 2 := (Finset.mem_powersetCard.mp J.2).2
    have hnonempty : J.1.Nonempty := Finset.card_pos.mp (by rw [hJcard]; omega)
    obtain ⟨z, hz⟩ := hnonempty
    exact (card_commonCandidates_le_of_mem cross _ hz).trans_eq
      (by simpa [G] using hcrossCard z)
  have hSpos : 0 < S.card := lt_of_lt_of_le hf hfS
  letI : Nonempty S := Fintype.card_pos_iff.mp (by simpa using hSpos)
  have hselected :
      ∃ τ : Equiv.Perm T, ∃ pick : Fin f → S, ∃ choose : Fin f → Y,
        Function.Injective pick ∧ Function.Injective choose ∧
        ∀ i : Fin f, choose i ∈
          commonCandidates cross (permuteDeltaSubset τ (I (pick i))).1 := by
    by_cases hσf : f ≤ σfloor
    · let pick : Fin f ↪ S := Classical.choice
          (Function.Embedding.nonempty_of_card_le (by simpa using hfS))
      let cand : Fin f → Finset Y := fun i ↦
        commonCandidates cross (I (pick i)).1
      have hstair : ∀ i : Fin f, f - i ≤ (cand i).card := by
        intro i
        exact (Nat.sub_le f i).trans (hσf.trans (by
          simpa [cand, g] using hfloor (I (pick i))))
      obtain ⟨choose, hchoose, hmem⟩ :=
        exists_distinct_representatives_of_staircase cand hstair
      refine ⟨Equiv.refl T, pick, choose, pick.injective, hchoose, ?_⟩
      intro i
      simpa [cand] using hmem i
    · have hσlt : σfloor < f := Nat.lt_of_not_ge hσf
      by_cases hfOne : f = 1
      · have hpermAverage : Fintype.card (DeltaSubsets T 2) * S.card ≤
            Fintype.card S * ∑ J : DeltaSubsets T 2, g J := by
          calc
            Fintype.card (DeltaSubsets T 2) * S.card =
                S.card * (Fintype.card (DeltaSubsets T 2) * f) := by
                  rw [hfOne]
                  ring
            _ ≤ S.card * ∑ J : DeltaSubsets T 2, g J := by gcongr
            _ = Fintype.card S * ∑ J : DeltaSubsets T 2, g J := by simp
        obtain ⟨τ, hτ⟩ := exists_permutation_with_large_sum g I hpermAverage
        let candS : S → Finset Y := fun x ↦
          commonCandidates cross (permuteDeltaSubset τ (I x)).1
        have hone : Fintype.card S * 1 ≤ ∑ x : S, (candS x).card := by
          simpa [candS, g] using hτ
        obtain ⟨x, hx⟩ := exists_le_of_card_mul_le_sum
          (fun x : S ↦ (candS x).card) hone
        let pick : Fin f → S := fun _ ↦ x
        have hpick : Function.Injective pick := by
          intro i j _h
          apply Fin.ext
          omega
        have hstair : ∀ i : Fin f, f - i ≤ (candS (pick i)).card := by
          intro i
          have hi0 : (i : ℕ) = 0 := by omega
          simpa [hfOne, hi0] using hx
        obtain ⟨choose, hchoose, hmem⟩ :=
          exists_distinct_representatives_of_staircase
            (fun i ↦ candS (pick i)) hstair
        exact ⟨τ, pick, choose, hpick, hchoose, fun i ↦ by
          simpa [candS] using hmem i⟩
      · have hf2 : 2 ≤ f := by omega
        let L := σfloor * S.card + (f - σfloor) * (G - σfloor)
        have hZL : Fintype.card (DeltaSubsets T 2) * L ≤
            S.card * ∑ J : DeltaSubsets T 2, g J := by
          rw [hZcard, hsumCandidates]
          have hend := hc2 (by simpa [σfloor]) hf2
          simpa [L, σfloor, G] using
            degree_two_candidate_endpoint deg (by simp [y]) hsumDeg hmean
              htpos hypos (q := L) (r := S.card) (by simpa [L, σfloor] using hend)
        have hpermAverage : Fintype.card (DeltaSubsets T 2) *
              max (S.card * f) L ≤
            Fintype.card S * ∑ J : DeltaSubsets T 2, g J := by
          rw [mul_max, max_le_iff]
          constructor
          · calc
              Fintype.card (DeltaSubsets T 2) * (S.card * f) =
                  S.card * (Fintype.card (DeltaSubsets T 2) * f) := by ring
              _ ≤ S.card * ∑ J : DeltaSubsets T 2, g J := by gcongr
              _ = Fintype.card S * ∑ J : DeltaSubsets T 2, g J := by simp
          · simpa using hZL
        obtain ⟨τ, hτ⟩ := exists_permutation_with_large_sum g I hpermAverage
        let cand : S → Finset Y := fun x ↦
          commonCandidates cross (permuteDeltaSubset τ (I x)).1
        have hcandFloor : ∀ x : S, σfloor ≤ (cand x).card := by
          intro x
          simpa [cand, g] using hfloor (permuteDeltaSubset τ (I x))
        have hcandBound : ∀ x : S, (cand x).card ≤ G := by
          intro x
          simpa [cand, g] using hbound (permuteDeltaSubset τ (I x))
        have hsf' : Fintype.card S * f ≤ ∑ x : S, (cand x).card := by
          have hs : S.card * f ≤ ∑ x : S, (cand x).card :=
            (le_max_left (S.card * f) L).trans (by simpa [cand, g] using hτ)
          simpa only [Fintype.card_coe] using hs
        have hshift : Fintype.card S * σfloor +
              (f - σfloor) * (G - σfloor) ≤
            ∑ x : S, (cand x).card := by
          have hraw := (le_max_right (S.card * f) L).trans hτ
          have hs : S.card * σfloor + (f - σfloor) * (G - σfloor) ≤
              ∑ x : S, (cand x).card := by
            simpa [L, cand, g, Nat.mul_comm] using hraw
          simpa only [Fintype.card_coe] using hs
        obtain ⟨pick, hpick, hstair⟩ := exists_floor_staircase_selection
          (fun x : S ↦ (cand x).card) hf (by simpa using hfS)
          hσlt.le hcandFloor hcandBound hsf' hshift
        obtain ⟨choose, hchoose, hmem⟩ :=
          exists_distinct_representatives_of_staircase
            (fun i ↦ cand (pick i)) hstair
        exact ⟨τ, pick, choose, hpick, hchoose, fun i ↦ by
          simpa [cand] using hmem i⟩
  obtain ⟨τ, pick, choose, hpick, hchoose, hchooseMem⟩ := hselected
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
  let coreτ : {w : Fin H.vertexCount // w ∉ S} ↪ T :=
    core.trans τ.toEmbedding
  have hattach : ∀ x : P, ∀ w : Fin H.vertexCount, ∀ hw : w ∉ S,
      H.graph.Adj x.1 w → Cᶜ.Adj (outside x).1 (coreτ ⟨w, hw⟩).1 := by
    intro x w hw hxw
    let i := idx x
    have hpickx : (pick i).1 = x.1 := by exact hidx x
    have hadj : H.graph.Adj (pick i).1 w := by simpa [hpickx] using hxw
    have hcoreMem : coreτ ⟨w, hw⟩ ∈
        (permuteDeltaSubset τ (I (pick i))).1 := by
      rw [permuteDeltaSubset_val, Finset.mem_map]
      refine ⟨core ⟨w, hw⟩, ?_, rfl⟩
      dsimp only [I]
      rw [Finset.mem_map]
      refine ⟨⟨w, (H.graph.mem_neighborFinset (pick i).1 w).mpr hadj⟩,
        by simp, rfl⟩
    have hcandMem := hchooseMem i
    have hcrossMem : choose i ∈ cross (coreτ ⟨w, hw⟩) :=
      (mem_commonCandidates.mp hcandMem) _ hcoreMem
    have hblue := hcrossBlue (coreτ ⟨w, hw⟩) (choose i) hcrossMem
    change Cᶜ.Adj (choose (idx x)).1 (coreτ ⟨w, hw⟩).1
    simpa [i] using hblue.symm
  apply hnoH
  have hPcard' : P.card = Fintype.card (Fin H.vertexCount) - T.card := by
    simpa [p] using hPcard
  exact isContained_of_independent_core_extension S hSind T Y hTY hTclique
    (by simpa [p] using hTlt.le) P hPS hPcard' coreτ outside hattach

end Erdos570
