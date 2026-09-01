import ErdosProblems.Erdos79.Core
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace Erdos79

open Finset
open scoped SimpleGraph

namespace SimpleGraph

variable {U V : Type} {T : _root_.SimpleGraph U} {G : _root_.SimpleGraph V}

/-- A finite tree embeds in every nonempty finite graph whose minimum degree is at least
one less than the number of vertices of the tree. -/
theorem isContained_of_isTree_of_card_sub_one_le_minDegree
    [Fintype U] [Fintype V] [Nonempty V]
    [DecidableRel G.Adj]
    (hT : T.IsTree) (hdeg : Fintype.card U - 1 ≤ G.minDegree) : T ⊑ G := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∀ (U : Type) [Fintype U] (T : _root_.SimpleGraph U),
      Fintype.card U = n → T.IsTree →
        Fintype.card U - 1 ≤ G.minDegree → T ⊑ G
  suffices hP : P (Fintype.card U) by
    exact hP U T rfl hT hdeg
  apply Nat.strong_induction_on (p := P) (Fintype.card U)
  intro n ih U _ T hn hT hdeg
  by_cases hU : Nontrivial U
  · let : Nontrivial U := hU
    obtain ⟨v, hv⟩ := hT.exists_vert_degree_one_of_nontrivial
    let U' := ({v}ᶜ : Set U)
    let T' : _root_.SimpleGraph U' := T.induce ({v}ᶜ : Set U)
    have hT' : T'.IsTree := ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hv,
      hT.isAcyclic.induce _⟩
    have hcardU' : Fintype.card U' = n - 1 := by
      change Fintype.card ↑({v}ᶜ : Set U) = n - 1
      rw [Fintype.card_compl_set]
      simp [hn]
    have hlt : Fintype.card U' < n := by
      rw [hcardU']
      have hnpos : 0 < n := by
        simpa [← hn] using Fintype.card_pos_iff.mpr (inferInstance : Nonempty U)
      omega
    have hdeg' : Fintype.card U' - 1 ≤ G.minDegree := by
      rw [hcardU']
      omega
    obtain ⟨e⟩ := ih (Fintype.card U') hlt U' T' rfl hT' hdeg'
    obtain ⟨p, hvp, hp_unique⟩ := (T.degree_eq_one_iff_existsUnique_adj).mp hv
    have hp_ne_v : p ≠ v := hvp.ne'
    let p' : U' := ⟨p, by
      change p ∈ ({v}ᶜ : Set U)
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact hp_ne_v⟩
    let used : Finset V := Finset.univ.image e
    have hused_card : used.card = Fintype.card U' := by
      simpa [used] using
        Finset.card_image_of_injective (Finset.univ : Finset U') e.injective
    have hused_le_neighbor : used.card ≤ (G.neighborFinset (e p')).card := by
      rw [hused_card, G.card_neighborFinset_eq_degree, hcardU']
      have hdeg_n : n - 1 ≤ G.minDegree := by
        rw [← hn]
        exact hdeg
      exact hdeg_n.trans (G.minDegree_le_degree (e p'))
    have hnot_subset : ¬ G.neighborFinset (e p') ⊆ used := by
      intro hsub
      have heq : G.neighborFinset (e p') = used :=
        Finset.eq_of_subset_of_card_le hsub hused_le_neighbor
      have hp_mem_used : e p' ∈ used := by simp [used]
      have hp_not_neighbor : e p' ∉ G.neighborFinset (e p') := G.notMem_neighborFinset_self _
      exact hp_not_neighbor (heq.symm ▸ hp_mem_used)
    obtain ⟨w, hw_neighbor, hw_unused⟩ := Finset.not_subset.mp hnot_subset
    have hw_adj : G.Adj (e p') w := (G.mem_neighborFinset _ _).mp hw_neighbor
    let f : U → V := fun x ↦ if hx : x = v then w else e ⟨x, by simpa [hx]⟩
    have hf_v : f v = w := by simp [f]
    have hf_ne (x : U) (hx : x ≠ v) : f x = e ⟨x, by simpa [hx]⟩ := by simp [f, hx]
    have hf_inj : Function.Injective f := by
      intro x y hxy
      by_cases hx : x = v
      · subst x
        by_cases hy : y = v
        · exact hy.symm
        exfalso
        have hwy : w = e ⟨y, by simpa [hy]⟩ := by
          simpa [hf_v, hf_ne y hy] using hxy
        apply hw_unused
        apply Finset.mem_image.mpr
        exact ⟨⟨y, by simp [U', hy]⟩, Finset.mem_univ _, hwy.symm⟩
      · by_cases hy : y = v
        · subst y
          exfalso
          have : e ⟨x, by simpa [hx]⟩ = w := by simpa [hf_v, hf_ne x hx] using hxy
          apply hw_unused
          apply Finset.mem_image.mpr
          exact ⟨⟨x, by simp [U', hx]⟩, Finset.mem_univ _, this⟩
        · have heq : e ⟨x, by simpa [hx]⟩ = e ⟨y, by simpa [hy]⟩ := by
            simpa [hf_ne x hx, hf_ne y hy] using hxy
          exact congrArg Subtype.val (e.injective heq)
    refine ⟨⟨⟨f, ?_⟩, hf_inj⟩⟩
    intro x y hxy
    by_cases hx : x = v
    · subst x
      have hy : y = p := hp_unique y hxy
      subst y
      simpa [hf_v, hf_ne p hp_ne_v, p'] using hw_adj.symm
    · by_cases hy : y = v
      · subst y
        have hx_p : x = p := hp_unique x hxy.symm
        subst x
        simpa [hf_v, hf_ne p hp_ne_v, p'] using hw_adj
      · have hT'xy : T'.Adj ⟨x, by simpa [hx]⟩ ⟨y, by simpa [hy]⟩ := hxy
        simpa [hf_ne x hx, hf_ne y hy] using e.toHom.map_adj hT'xy
  · let : Subsingleton U := not_nontrivial_iff_subsingleton.mp hU
    exact ⟨{
      toHom := {
        toFun := fun _ ↦ Classical.choice (inferInstance : Nonempty V)
        map_rel' := fun {a b} hab ↦
          (T.loopless.irrefl a (Subsingleton.elim b a ▸ hab)).elim }
      injective' := fun _ _ _ ↦ Subsingleton.elim _ _ }⟩

/-- Adjoining a vertex adjacent to an embedded clique produces a clique one vertex larger. -/
theorem top_succ_isContained_of_copy_of_adj
    {k : ℕ}
    (v : V) (q : (⊤ : _root_.SimpleGraph (Fin k)).Copy G)
    (hq : ∀ i, G.Adj v (q i)) :
    (⊤ : _root_.SimpleGraph (Fin (k + 1))) ⊑ G := by
  classical
  let f : Fin (k + 1) → V := Fin.cases v q
  have hf_inj : Function.Injective f := by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
        cases j using Fin.cases with
        | zero => rfl
        | succ j =>
            exfalso
            exact (hq j).ne hij
    | succ i =>
        cases j using Fin.cases with
        | zero =>
            exfalso
            exact (hq i).ne' hij
        | succ j =>
            exact congrArg Fin.succ (q.injective hij)
  refine ⟨⟨⟨f, ?_⟩, hf_inj⟩⟩
  intro i j hij
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero => simp at hij
      | succ j => exact hq j
  | succ i =>
      cases j using Fin.cases with
      | zero => exact (hq i).symm
      | succ j =>
          apply q.toHom.map_adj
          simpa using hij

end SimpleGraph

/-- Chvátal's tree-versus-clique bound
`R(T, K_s) ≤ (|T| - 1)(s - 1) + 1`. -/
theorem ramseyAt_tree_completeCode (F : GraphCode) (hF : F.graph.IsTree) (s : ℕ) :
    RamseyAt F (completeCode s) ((F.vertexCount - 1) * (s - 1) + 1) := by
  classical
  induction s using Nat.twoStepInduction with
  | zero =>
      simp only [Nat.zero_sub, Nat.mul_zero, Nat.zero_add]
      intro C
      right
      change (⊤ : _root_.SimpleGraph (Fin 0)) ⊑ Cᶜ
      exact _root_.SimpleGraph.IsContained.of_isEmpty
  | one =>
      simp only [Nat.sub_self, Nat.mul_zero, Nat.zero_add]
      intro C
      right
      change (⊤ : _root_.SimpleGraph (Fin 1)) ⊑ Cᶜ
      apply _root_.SimpleGraph.IsContained.of_le
      intro i j hij
      have hij' : i = j := Subsingleton.elim i j
      subst j
      exact ((⊤ : _root_.SimpleGraph (Fin 1)).loopless.irrefl i hij).elim
  | more k hk hk1 =>
      rw [show k + 2 - 1 = k + 1 by omega]
      let N := (F.vertexCount - 1) * (k + 1) + 1
      change RamseyAt F (completeCode (k + 2)) N
      intro C
      by_cases hred : F.graph ⊑ C
      · exact Or.inl hred
      right
      have hNpos : 0 < N := by simp [N]
      let : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hNpos
      have hmindeg : ¬ F.vertexCount - 1 ≤ C.minDegree := by
        intro h
        apply hred
        apply SimpleGraph.isContained_of_isTree_of_card_sub_one_le_minDegree hF
        simpa using h
      obtain ⟨v, hv⟩ := C.exists_minimal_degree_vertex
      have hvlt : C.degree v < F.vertexCount - 1 := by
        rw [← hv]
        exact Nat.lt_of_not_ge hmindeg
      let M := (F.vertexCount - 1) * k + 1
      have hblue_degree : M ≤ Cᶜ.degree v := by
        rw [C.degree_compl]
        simp only [Fintype.card_fin]
        dsimp [N, M]
        calc
          (F.vertexCount - 1) * k + 1 ≤
              (F.vertexCount - 1) * k + (F.vertexCount - 1) - C.degree v := by omega
          _ = (F.vertexCount - 1) * (k + 1) - C.degree v :=
            congrArg (fun z ↦ z - C.degree v) (Nat.mul_succ _ _).symm
      let S := Cᶜ.neighborSet v
      have hMcard : M ≤ Fintype.card S := by
        change M ≤ Fintype.card (Cᶜ.neighborSet v)
        rw [Cᶜ.card_neighborSet_eq_degree]
        exact hblue_degree
      let j : Fin M ↪ S :=
        (Function.Embedding.nonempty_of_card_le (by simpa using hMcard)).some
      let f : Fin M ↪ Fin N := j.trans (Function.Embedding.subtype _)
      have hrec : RamseyAt F (completeCode (k + 1)) M := by
        simpa [M] using hk1
      rcases hrec (C.comap f) with hsmallred | hsmallblue
      · exact (hred (hsmallred.trans (SimpleGraph.Embedding.comap f C).isContained)).elim
      · have hsmallblue' :
            (⊤ : _root_.SimpleGraph (Fin (k + 1))) ⊑ Cᶜ.comap f := by
          have hcompl : (C.comap f)ᶜ = Cᶜ.comap f := by
            ext x y
            simp [f.injective.eq_iff]
          rw [← hcompl]
          exact hsmallblue
        let q : (⊤ : _root_.SimpleGraph (Fin (k + 1))).Copy Cᶜ :=
          (SimpleGraph.Embedding.comap f Cᶜ).toCopy.comp hsmallblue'.some
        have hq (i : Fin (k + 1)) : Cᶜ.Adj v (q i) := by
          have hj := (j (hsmallblue'.some i)).property
          change Cᶜ.Adj v (j (hsmallblue'.some i)).val at hj
          change Cᶜ.Adj v (f (hsmallblue'.some i))
          exact hj
        exact SimpleGraph.top_succ_isContained_of_copy_of_adj v q hq

/-- Every finite forest is Ramsey size linear. -/
theorem ramseySizeLinear_of_isAcyclic (F : GraphCode) (hF : F.graph.IsAcyclic) :
    RamseySizeLinear F := by
  classical
  by_cases hF0 : F.vertexCount = 0
  · refine ⟨0, fun H hH C ↦ ?_⟩
    left
    have : IsEmpty (Fin F.vertexCount) := by rw [hF0]; infer_instance
    exact SimpleGraph.IsContained.of_isEmpty
  · have hFpos : 0 < F.vertexCount := Nat.pos_of_ne_zero hF0
    let : Nonempty (Fin F.vertexCount) := Fin.pos_iff_nonempty.mp hFpos
    have htop : (⊤ : _root_.SimpleGraph (Fin F.vertexCount)).Connected :=
      _root_.SimpleGraph.connected_top
    obtain ⟨T, hFT, _hTtop, hT⟩ := htop.exists_isTree_le_of_le_of_isAcyclic le_top hF
    let FT : GraphCode := ⟨F.vertexCount, T⟩
    refine ⟨2 * F.vertexCount + 1, fun H hH ↦ ?_⟩
    by_cases hm : H.edgeCount = 0
    · rw [hm, Nat.mul_zero]
      have hH0 : H.vertexCount = 0 := by
        have := hH.vertexCount_le_twice_edgeCount
        omega
      intro C
      right
      have : IsEmpty (Fin H.vertexCount) := by rw [hH0]; infer_instance
      exact SimpleGraph.IsContained.of_isEmpty
    · have hmpos : 0 < H.edgeCount := Nat.pos_of_ne_zero hm
      have hHK : IsContained H (completeCode H.vertexCount) := by
        change H.graph ⊑ (⊤ : _root_.SimpleGraph (Fin H.vertexCount))
        exact _root_.SimpleGraph.IsContained.of_le le_top
      have hramsey :
          RamseyAt FT H ((F.vertexCount - 1) * (H.vertexCount - 1) + 1) :=
        (ramseyAt_tree_completeCode FT hT H.vertexCount).mono_right hHK
      have hbound :
          (F.vertexCount - 1) * (H.vertexCount - 1) + 1 ≤
            (2 * F.vertexCount + 1) * H.edgeCount := by
        calc
          (F.vertexCount - 1) * (H.vertexCount - 1) + 1 ≤
              F.vertexCount * H.vertexCount + 1 :=
            Nat.add_le_add_right
              (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)) 1
          _ ≤ F.vertexCount * (2 * H.edgeCount) + 1 :=
            Nat.add_le_add_right
              (Nat.mul_le_mul_left F.vertexCount hH.vertexCount_le_twice_edgeCount) 1
          _ ≤ (2 * F.vertexCount + 1) * H.edgeCount := by
            simpa [Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
              Nat.add_le_add_left hmpos (2 * F.vertexCount * H.edgeCount)
      have hFFT : IsContained F FT := by
        change F.graph ⊑ T
        exact _root_.SimpleGraph.IsContained.of_le hFT
      exact (hramsey.mono_left hFFT).mono_vertices hbound

end Erdos79
