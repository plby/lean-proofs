/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.Recode
import ErdosProblems.Erdos570.TriangleIndependent

/-!
# Contracting an adjacent pair in the triangle argument
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

def contractVertex {V : Type*} [DecidableEq V] (u v : V) (x : V) : V :=
  if x = v then u else x

def contractionGraph {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (u v : V) :
    SimpleGraph {x : V // x ≠ v} :=
  (G.map (contractVertex u v)).induce {x | x ≠ v}

def contractionCode {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u v : V) : GraphCode :=
  recodeGraph (contractionGraph G u v)

theorem contractionGraph_adj_of_adj
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v a b : V}
    (ha : a ≠ v) (hb : b ≠ v) (hab : G.Adj a b) :
    (contractionGraph G u v).Adj ⟨a, ha⟩ ⟨b, hb⟩ := by
  change (G.map (contractVertex u v)).Adj a b
  have hmap := SimpleGraph.map_adj_apply'
    (f := contractVertex u v) hab (by
      simpa [contractVertex, ha, hb] using hab.ne)
  simpa [contractVertex, ha, hb] using hmap

theorem contractionGraph_adj_redirect
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v z : V}
    (huv : u ≠ v) (hzv : z ≠ v) (hzu : z ≠ u) (hvz : G.Adj v z) :
    (contractionGraph G u v).Adj ⟨u, huv⟩ ⟨z, hzv⟩ := by
  change (G.map (contractVertex u v)).Adj u z
  have hmap := SimpleGraph.map_adj_apply'
    (f := contractVertex u v) hvz (by
      simpa [contractVertex, hzv] using hzu.symm)
  simpa [contractVertex, huv, hzv] using hmap

/-- The contraction has one fewer vertex. -/
theorem contractionCode_vertexCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u v : V) :
    (contractionCode G u v).vertexCount = Fintype.card V - 1 := by
  rw [contractionCode, recodeGraph_vertexCount]
  let e : {x : V // x = v} ≃ Fin 1 :=
    { toFun := fun _ ↦ 0
      invFun := fun _ ↦ ⟨v, rfl⟩
      left_inv := by intro x; exact Subtype.ext x.2.symm
      right_inv := by intro x; exact Fin.ext (by simp) }
  calc
    Fintype.card {x : V // x ≠ v} =
        Fintype.card V - Fintype.card {x : V // x = v} := by
      simpa using Fintype.card_subtype_compl (fun x : V ↦ x = v)
    _ = Fintype.card V - 1 := by rw [Fintype.card_congr e]; simp

/-- Contracting an edge strictly decreases the number of edges. -/
theorem contractionCode_edgeCount_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V}
    (huv : G.Adj u v) :
    (contractionCode G u v).edgeCount < G.edgeFinset.card := by
  classical
  let c := contractVertex u v
  let M : Finset (Sym2 V) := G.edgeFinset.image (Sym2.map c)
  have hfullSub : (G.map c).edgeFinset ⊆ M := by
    intro e he
    induction e using Sym2.inductionOn with | _ a b =>
      have hab : (G.map c).Adj a b := by
        simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
      rw [SimpleGraph.map_adj'] at hab
      obtain ⟨hne, x, y, hxy, hxa, hyb⟩ := hab
      dsimp only [M]
      rw [Finset.mem_image]
      refine ⟨s(x, y), ?_, ?_⟩
      · simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hxy
      · simp only [Sym2.map_pair_eq]
        rw [hxa, hyb]
  let d : Sym2 V := s(u, u)
  have hdM : d ∈ M := by
    dsimp only [M]
    rw [Finset.mem_image]
    refine ⟨s(u, v), ?_, ?_⟩
    · simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using huv
    · simp [d, c, contractVertex, huv.ne]
  have hdnot : d ∉ (G.map c).edgeFinset := by
    intro hd
    have : (G.map c).Adj u u := by
      simpa [d, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hd
    exact this.ne rfl
  have hfullLt : (G.map c).edgeFinset.card < M.card := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨hfullSub, ?_⟩
    intro heq
    exact hdnot (heq ▸ hdM)
  have hMle : M.card ≤ G.edgeFinset.card := by
    dsimp only [M]
    exact Finset.card_image_le
  have hinduce : (contractionGraph G u v).edgeFinset.card ≤
      (G.map c).edgeFinset.card := by
    let inc : {x : V // x ≠ v} ↪ V := Function.Embedding.subtype _
    have hsub : (contractionGraph G u v).edgeFinset.map inc.sym2Map ⊆
        (G.map c).edgeFinset := by
      intro e he
      rw [Finset.mem_map] at he
      obtain ⟨e', he', rfl⟩ := he
      induction e' using Sym2.inductionOn with | _ a b =>
        have hab : (contractionGraph G u v).Adj a b := by
          simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he'
        simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
          contractionGraph, inc] using hab
    have hc := Finset.card_le_card hsub
    rw [Finset.card_map] at hc
    exact hc
  rw [contractionCode, recodeGraph_edgeCount]
  exact hinduce.trans_lt (hfullLt.trans_le hMle)

/-- If the contracted endpoint has another neighbour, contraction preserves
the absence of isolated vertices. -/
theorem contractionCode_noIsolated
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (huv : G.Adj u v)
    (hno : ∀ x : V, ¬ G.IsIsolated x) (huDegree : 2 ≤ G.degree u) :
    NoIsolated (contractionCode G u v) := by
  rw [contractionCode, recodeGraph_noIsolated_iff]
  intro x
  rw [← (contractionGraph G u v).exists_adj_iff_not_isIsolated]
  by_cases hxu : x.1 = u
  · have hvMem : v ∈ G.neighborFinset u := by
      rw [G.mem_neighborFinset]
      exact huv
    have htwo : 2 ≤ (G.neighborFinset u).card := by simpa using huDegree
    have hex : ∃ z ∈ G.neighborFinset u, z ≠ v := by
      by_contra hnot
      push_neg at hnot
      have hsub : G.neighborFinset u ⊆ {v} := by
        intro z hz
        simpa using hnot z hz
      have := Finset.card_le_card hsub
      simp at this
      omega
    obtain ⟨z, hz, hzv⟩ := hex
    refine ⟨⟨z, hzv⟩, ?_⟩
    have hxEq : x = ⟨u, huv.ne⟩ := Subtype.ext hxu
    rw [hxEq]
    exact contractionGraph_adj_of_adj huv.ne hzv
      ((G.mem_neighborFinset u z).mp hz)
  · obtain ⟨z, hxz⟩ := G.exists_adj_iff_not_isIsolated.mpr (hno x.1)
    by_cases hzv : z = v
    · subst z
      refine ⟨⟨u, huv.ne⟩, ?_⟩
      exact (contractionGraph_adj_redirect huv.ne x.2 hxu hxz.symm).symm
    · refine ⟨⟨z, hzv⟩, ?_⟩
      exact contractionGraph_adj_of_adj x.2 hzv hxz

/-- Extend an embedding of the graph with `u,v` removed after choosing
separate images for those two vertices. -/
theorem isContained_of_two_vertex_extension
    {W Z : Type*} [DecidableEq W]
    (G : SimpleGraph W) (B : SimpleGraph Z) {u v : W} (huv : u ≠ v)
    (core : {z : W // z ≠ u ∧ z ≠ v} ↪ Z) (U V : Z)
    (hUV : B.Adj U V)
    (hUcore : ∀ z, U ≠ core z) (hVcore : ∀ z, V ≠ core z)
    (hcoreAdj : ∀ a b : {z : W // z ≠ u ∧ z ≠ v},
      G.Adj a.1 b.1 → B.Adj (core a) (core b))
    (hUnbr : ∀ z : {z : W // z ≠ u ∧ z ≠ v},
      G.Adj u z.1 → B.Adj U (core z))
    (hVnbr : ∀ z : {z : W // z ≠ u ∧ z ≠ v},
      G.Adj v z.1 → B.Adj V (core z)) :
    G ⊑ B := by
  classical
  let emb : W → Z := fun z ↦
    if hzu : z = u then U
    else if hzv : z = v then V else core ⟨z, hzu, hzv⟩
  have hemb_u : emb u = U := by
    simp [emb]
  have hemb_v : emb v = V := by
    simp [emb, huv.symm]
  have hemb_core (z : {z : W // z ≠ u ∧ z ≠ v}) :
      emb z.1 = core z := by
    simp [emb, z.2.1, z.2.2]
  have hemb : Function.Injective emb := by
    intro a b hab
    by_cases hau : a = u
    · subst a
      by_cases hbu : b = u
      · exact hbu.symm
      by_cases hbv : b = v
      · subst b
        rw [hemb_u, hemb_v] at hab
        exact (hUV.ne hab).elim
      · rw [hemb_u, hemb_core ⟨b, hbu, hbv⟩] at hab
        exact (hUcore ⟨b, hbu, hbv⟩ hab).elim
    by_cases hav : a = v
    · subst a
      by_cases hbu : b = u
      · subst b
        rw [hemb_v, hemb_u] at hab
        exact (hUV.ne hab.symm).elim
      by_cases hbv : b = v
      · exact hbv.symm
      · rw [hemb_v, hemb_core ⟨b, hbu, hbv⟩] at hab
        exact (hVcore ⟨b, hbu, hbv⟩ hab).elim
    · by_cases hbu : b = u
      · subst b
        rw [hemb_core ⟨a, hau, hav⟩, hemb_u] at hab
        exact (hUcore ⟨a, hau, hav⟩ hab.symm).elim
      by_cases hbv : b = v
      · subst b
        rw [hemb_core ⟨a, hau, hav⟩, hemb_v] at hab
        exact (hVcore ⟨a, hau, hav⟩ hab.symm).elim
      · rw [hemb_core ⟨a, hau, hav⟩,
          hemb_core ⟨b, hbu, hbv⟩] at hab
        exact congrArg Subtype.val (core.injective hab)
  let hom : G →g B :=
    { toFun := emb
      map_rel' := by
        intro a b hab
        by_cases hau : a = u
        · subst a
          by_cases hbu : b = u
          · exact (hab.ne hbu.symm).elim
          by_cases hbv : b = v
          · subst b
            rw [hemb_u, hemb_v]
            exact hUV
          · rw [hemb_u, hemb_core ⟨b, hbu, hbv⟩]
            exact hUnbr ⟨b, hbu, hbv⟩ hab
        by_cases hav : a = v
        · subst a
          by_cases hbu : b = u
          · subst b
            rw [hemb_v, hemb_u]
            exact hUV.symm
          by_cases hbv : b = v
          · exact (hab.ne hbv.symm).elim
          · rw [hemb_v, hemb_core ⟨b, hbu, hbv⟩]
            exact hVnbr ⟨b, hbu, hbv⟩ hab
        · by_cases hbu : b = u
          · subst b
            rw [hemb_core ⟨a, hau, hav⟩, hemb_u]
            exact (hUnbr ⟨a, hau, hav⟩ hab.symm).symm
          by_cases hbv : b = v
          · subst b
            rw [hemb_core ⟨a, hau, hav⟩, hemb_v]
            exact (hVnbr ⟨a, hau, hav⟩ hab.symm).symm
          · rw [hemb_core ⟨a, hau, hav⟩,
              hemb_core ⟨b, hbu, hbv⟩]
            exact hcoreAdj ⟨a, hau, hav⟩ ⟨b, hbu, hbv⟩ hab }
  exact ⟨hom.toCopy hemb⟩

/-- The counting conclusion in the adjacent-minimum-vertices branch of the
Goddard--Kleitman argument.  A blue copy of the contraction, in a red
triangle-free coloring with no blue copy of the original graph, forces an
order strictly below `2m+1`. -/
theorem triangle_adjacent_contraction_contradiction
    {H : GraphCode} {N : ℕ} (C : SimpleGraph (Fin N))
    [DecidableRel C.Adj] [DecidableRel H.graph.Adj]
    (hH : NoIsolated H) (hN : 2 * H.edgeCount + 1 ≤ N)
    (u v : Fin H.vertexCount) (huv : H.graph.Adj u v)
    (humin : H.graph.degree u = H.graph.minDegree)
    (hvdeg : H.graph.degree v = H.graph.degree u)
    (hδ : 2 ≤ H.graph.degree u)
    (hcopy : (contractionGraph H.graph u v) ⊑ Cᶜ)
    (hnoCycle : ¬ (cycleCode 3).graph ⊑ C)
    (hnoH : ¬ H.graph ⊑ Cᶜ) : False := by
  classical
  let p := H.vertexCount
  let m := H.edgeCount
  let δ := H.graph.degree u
  let D := {z : Fin H.vertexCount // z ≠ v}
  obtain ⟨copy⟩ := hcopy
  let used : Finset (Fin N) := Finset.univ.image copy
  let X : Finset (Fin N) := Finset.univ \ used
  let w : Fin N := copy ⟨u, huv.ne⟩
  let core : {z : Fin H.vertexCount // z ≠ u ∧ z ≠ v} ↪ Fin N :=
    { toFun := fun z ↦ copy ⟨z.1, z.2.2⟩
      inj' := by
        intro a b hab
        apply Subtype.ext
        exact congrArg (fun z : D ↦ z.1) (copy.injective hab) }
  let W₁ := (H.graph.neighborFinset u).erase v
  let W₂ := (H.graph.neighborFinset v).erase u
  let image₁ : W₁ → Fin N := fun z ↦ copy ⟨z.1, by
    intro hzv
    exact (Finset.mem_erase.mp z.2).1 hzv⟩
  let image₂ : W₂ → Fin N := fun z ↦ copy ⟨z.1, by
    intro hzv
    have hadj := (H.graph.mem_neighborFinset v z.1).mp
      (Finset.mem_of_mem_erase z.2)
    exact hadj.ne hzv.symm⟩
  let A₁ : Finset (Fin N) := X.filter fun x ↦
    ∀ z : W₁, Cᶜ.Adj x (image₁ z)
  let A₂ : Finset (Fin N) := X.filter fun x ↦
    ∀ z : W₂, Cᶜ.Adj x (image₂ z)
  have hfree : C.CliqueFree 3 :=
    cliqueFree_three_of_cycleCode_not_isContained C hnoCycle
  have hfresh {x : Fin N} (hx : x ∈ X) (z : D) : x ≠ copy z := by
    intro heq
    have hxused : x ∈ used := by
      dsimp only [used]
      rw [Finset.mem_image]
      exact ⟨z, Finset.mem_univ _, heq.symm⟩
    exact (Finset.mem_sdiff.mp hx).2 hxused
  have hcoreAdj : ∀ a b : {z : Fin H.vertexCount // z ≠ u ∧ z ≠ v},
      H.graph.Adj a.1 b.1 → Cᶜ.Adj (core a) (core b) := by
    intro a b hab
    apply copy.toHom.map_adj
    exact contractionGraph_adj_of_adj a.2.2 b.2.2 hab
  have hwCoreU (z : {z : Fin H.vertexCount // z ≠ u ∧ z ≠ v})
      (hz : H.graph.Adj u z.1) : Cᶜ.Adj w (core z) := by
    apply copy.toHom.map_adj
    exact contractionGraph_adj_of_adj huv.ne z.2.2 hz
  have hwCoreV (z : {z : Fin H.vertexCount // z ≠ u ∧ z ≠ v})
      (hz : H.graph.Adj v z.1) : Cᶜ.Adj w (core z) := by
    apply copy.toHom.map_adj
    exact contractionGraph_adj_redirect huv.ne z.2.2 z.2.1 hz
  have hred_of_not_blue {a b : Fin N} (hne : a ≠ b)
      (hnot : ¬ Cᶜ.Adj a b) : C.Adj a b := by
    by_contra hred
    exact hnot ((SimpleGraph.compl_adj C a b).mpr ⟨hne, hred⟩)
  have hforbid : ∀ x ∈ A₁, ∀ y ∈ A₂, x ≠ y → False := by
    intro x hxA y hyA hxy
    have hxX : x ∈ X := (Finset.mem_filter.mp hxA).1
    have hyX : y ∈ X := (Finset.mem_filter.mp hyA).1
    have hxCompat := (Finset.mem_filter.mp hxA).2
    have hyCompat := (Finset.mem_filter.mp hyA).2
    have hxw : x ≠ w := hfresh hxX ⟨u, huv.ne⟩
    have hyw : y ≠ w := hfresh hyX ⟨u, huv.ne⟩
    have hnotXY : ¬ Cᶜ.Adj x y := by
      intro hblue
      apply hnoH
      apply isContained_of_two_vertex_extension H.graph Cᶜ huv.ne core x y hblue
      · intro z
        exact hfresh hxX ⟨z.1, z.2.2⟩
      · intro z
        exact hfresh hyX ⟨z.1, z.2.2⟩
      · exact hcoreAdj
      · intro z hz
        let z₁ : W₁ := ⟨z.1, Finset.mem_erase.mpr ⟨z.2.2,
          (H.graph.mem_neighborFinset u z.1).mpr hz⟩⟩
        exact hxCompat z₁
      · intro z hz
        let z₂ : W₂ := ⟨z.1, Finset.mem_erase.mpr ⟨z.2.1,
          (H.graph.mem_neighborFinset v z.1).mpr hz⟩⟩
        exact hyCompat z₂
    have hnotXW : ¬ Cᶜ.Adj x w := by
      intro hblue
      apply hnoH
      apply isContained_of_two_vertex_extension H.graph Cᶜ huv.ne core x w hblue
      · intro z
        exact hfresh hxX ⟨z.1, z.2.2⟩
      · intro z hEq
        exact z.2.1 (congrArg Subtype.val (copy.injective hEq.symm))
      · exact hcoreAdj
      · intro z hz
        let z₁ : W₁ := ⟨z.1, Finset.mem_erase.mpr ⟨z.2.2,
          (H.graph.mem_neighborFinset u z.1).mpr hz⟩⟩
        exact hxCompat z₁
      · exact hwCoreV
    have hnotWY : ¬ Cᶜ.Adj w y := by
      intro hblue
      apply hnoH
      apply isContained_of_two_vertex_extension H.graph Cᶜ huv.ne core w y hblue
      · intro z hEq
        exact z.2.1 (congrArg Subtype.val (copy.injective hEq)).symm
      · intro z
        exact hfresh hyX ⟨z.1, z.2.2⟩
      · exact hcoreAdj
      · exact hwCoreU
      · intro z hz
        let z₂ : W₂ := ⟨z.1, Finset.mem_erase.mpr ⟨z.2.1,
          (H.graph.mem_neighborFinset v z.1).mpr hz⟩⟩
        exact hyCompat z₂
    have hredXY : C.Adj x y := hred_of_not_blue hxy hnotXY
    have hredXW : C.Adj x w := hred_of_not_blue hxw hnotXW
    have hredWY : C.Adj w y := hred_of_not_blue hyw.symm hnotWY
    have hind := C.isIndepSet_neighborSet_of_triangleFree hfree x
    exact hind (by simpa using hredXW) (by simpa using hredXY)
      hredWY.ne hredWY
  have hsmall : A₁.card ≤ 1 ∨ A₂.card ≤ 1 := by
    by_cases hA₁ : A₁.card ≤ 1
    · exact Or.inl hA₁
    · right
      by_contra hA₂
      have hA₁pos : 0 < A₁.card := by omega
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hA₁pos
      have hA₂pos : 0 < A₂.card := by omega
      obtain ⟨y₀, hy₀⟩ := Finset.card_pos.mp hA₂pos
      by_cases hxy₀ : x ≠ y₀
      · exact hforbid x hx y₀ hy₀ hxy₀
      · have hA₂two : 2 ≤ A₂.card := by omega
        have hxy : x = y₀ := not_ne_iff.mp hxy₀
        have herase : 0 < (A₂.erase x).card := by
          rw [Finset.card_erase_of_mem (hxy ▸ hy₀)]
          omega
        obtain ⟨y, hy⟩ := Finset.card_pos.mp herase
        exact hforbid x hx y (Finset.mem_of_mem_erase hy)
          (Finset.ne_of_mem_erase hy).symm
  obtain ⟨T, hTclique, hTcard⟩ := Cᶜ.exists_isNClique_cliqueNum
  have hcliqueLt : Cᶜ.cliqueNum < p := by
    by_contra hnot
    apply hnoH
    exact isContained_of_isClique_card_le H.graph Cᶜ T hTclique (by
      rw [hTcard]
      simpa [p] using Nat.le_of_not_gt hnot)
  have hdegree (q : Fin N) : C.degree q ≤ p - 1 := by
    have hq := degree_le_compl_cliqueNum_of_cliqueFree_three C hfree q
    omega
  have hW₁card : W₁.card = δ - 1 := by
    dsimp only [W₁, δ]
    rw [Finset.card_erase_of_mem
      ((H.graph.mem_neighborFinset u v).mpr huv)]
    simp only [SimpleGraph.card_neighborFinset_eq_degree]
  have hW₂card : W₂.card = δ - 1 := by
    dsimp only [W₂, δ]
    rw [Finset.card_erase_of_mem]
    · exact congrArg (· - 1) hvdeg
    · exact (H.graph.mem_neighborFinset v u).mpr huv.symm
  have hside_bound (W : Finset (Fin H.vertexCount))
      (image : W → Fin N) (A : Finset (Fin N))
      (hAsub : A ⊆ X)
      (hnotA : ∀ x ∈ X, x ∉ A → ∃ z : W, ¬ Cᶜ.Adj x (image z))
      (himage : ∀ z : W, image z ∈ used)
      (hWcard : W.card = δ - 1) (hAcard : A.card ≤ 1) :
      X.card ≤ (δ - 1) * (p - 1) + 1 := by
    let covered : Finset (Fin N) :=
      (Finset.univ : Finset W).biUnion fun z ↦ C.neighborFinset (image z)
    have hcover : X \ A ⊆ covered := by
      intro x hx
      have hxX := (Finset.mem_sdiff.mp hx).1
      have hxA := (Finset.mem_sdiff.mp hx).2
      obtain ⟨z, hz⟩ := hnotA x hxX hxA
      have hne : x ≠ image z := by
        intro heq
        exact (Finset.mem_sdiff.mp hxX).2 (heq ▸ himage z)
      have hred : C.Adj x (image z) := hred_of_not_blue hne hz
      rw [Finset.mem_biUnion]
      exact ⟨z, Finset.mem_univ _,
        (C.mem_neighborFinset (image z) x).mpr hred.symm⟩
    calc
      X.card = (X \ A).card + A.card :=
        (Finset.card_sdiff_add_card_eq_card hAsub).symm
      _ ≤ covered.card + 1 := Nat.add_le_add (Finset.card_le_card hcover) hAcard
      _ ≤ (∑ z : W, (C.neighborFinset (image z)).card) + 1 := by
        gcongr
        exact Finset.card_biUnion_le
      _ = (∑ z : W, C.degree (image z)) + 1 := by
        simp only [SimpleGraph.card_neighborFinset_eq_degree]
      _ ≤ (∑ _z : W, (p - 1)) + 1 := by
        gcongr with z
        exact hdegree (image z)
      _ = (δ - 1) * (p - 1) + 1 := by
        simp [hWcard, mul_comm]
  have hA₁sub : A₁ ⊆ X := Finset.filter_subset _ _
  have hA₂sub : A₂ ⊆ X := Finset.filter_subset _ _
  have himage₁ (z : W₁) : image₁ z ∈ used := by
    dsimp only [image₁, used]
    rw [Finset.mem_image]
    exact ⟨⟨z.1, by
      intro hzv
      exact (Finset.mem_erase.mp z.2).1 hzv⟩, Finset.mem_univ _, rfl⟩
  have himage₂ (z : W₂) : image₂ z ∈ used := by
    dsimp only [image₂, used]
    rw [Finset.mem_image]
    exact ⟨⟨z.1, by
      intro hzv
      have hadj := (H.graph.mem_neighborFinset v z.1).mp
        (Finset.mem_of_mem_erase z.2)
      exact hadj.ne hzv.symm⟩,
      Finset.mem_univ _, rfl⟩
  have hnotA₁ : ∀ x ∈ X, x ∉ A₁ →
      ∃ z : W₁, ¬ Cᶜ.Adj x (image₁ z) := by
    intro x hxX hxA
    simp only [A₁, Finset.mem_filter, hxX, true_and] at hxA
    simpa only [not_forall] using hxA
  have hnotA₂ : ∀ x ∈ X, x ∉ A₂ →
      ∃ z : W₂, ¬ Cᶜ.Adj x (image₂ z) := by
    intro x hxX hxA
    simp only [A₂, Finset.mem_filter, hxX, true_and] at hxA
    simpa only [not_forall] using hxA
  have hXbound : X.card ≤ (δ - 1) * (p - 1) + 1 := by
    rcases hsmall with hsmall | hsmall
    · exact hside_bound W₁ image₁ A₁ hA₁sub hnotA₁ himage₁ hW₁card hsmall
    · exact hside_bound W₂ image₂ A₂ hA₂sub hnotA₂ himage₂ hW₂card hsmall
  have husedCard : used.card = p - 1 := by
    calc
      used.card = Fintype.card {z : Fin H.vertexCount // z ≠ v} := by
        dsimp only [used]
        rw [Finset.card_image_iff.mpr]
        · simp only [Finset.card_univ]
        · intro a _ b _ hab
          exact copy.injective hab
      _ = p - 1 := by
        simpa [p] using contractionCode_vertexCount H.graph u v
  have hp2m : p ≤ 2 * m := by
    simpa [p, m] using NoIsolated.vertexCount_le_twice_edgeCount hH
  have husedLe : p - 1 ≤ N := by omega
  have hXCard : X.card = N - (p - 1) := by
    dsimp only [X]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ used)]
    simp [husedCard]
  have hNbound : N ≤ (p - 1) + ((δ - 1) * (p - 1) + 1) := by
    rw [hXCard] at hXbound
    omega
  have hdegreeSum : δ * p ≤ 2 * m := by
    have hpoint : ∀ z : Fin H.vertexCount, δ ≤ H.graph.degree z := by
      intro z
      dsimp only [δ]
      rw [humin]
      exact H.graph.minDegree_le_degree z
    calc
      δ * p = ∑ _z : Fin H.vertexCount, δ := by simp [p, mul_comm]
      _ ≤ ∑ z : Fin H.vertexCount, H.graph.degree z :=
        Finset.sum_le_sum fun z _ ↦ hpoint z
      _ = 2 * m := by
        simpa [m, GraphCode.edgeCount_eq_card_edgeFinset] using
          H.graph.sum_degrees_eq_twice_card_edges
  have hNδ : N + (δ - 1) ≤ δ * p := by
    calc
      N + (δ - 1) ≤
          ((p - 1) + ((δ - 1) * (p - 1) + 1)) + (δ - 1) :=
        Nat.add_le_add_right hNbound _
      _ = ((δ - 1) + 1) * ((p - 1) + 1) := by ring
      _ = δ * p := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ δ),
          Nat.sub_add_cancel (by omega : 1 ≤ p)]
  omega

end Erdos570
