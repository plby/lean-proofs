/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Released under the Apache 2.0 license. This file has been modified. -/
/-
Erdős Problem 146. Informal proof: Astra (internal OpenAI model).
Formalization: Astra (internal OpenAI model), OpenAI team.
Source: https://www.erdosproblems.com/forum/thread/146#post-8253
https://github.com/openai/ten-proofs/blob/a13547c6be4563746881d0b3b4c9fd03f72f0484/CompactnessAndDegeneracy.lean
Original Lean/Mathlib version: 4.32.0. Ported to 4.33.0.
-/
import ErdosProblems.Erdos146.BinaryEntropy

set_option linter.mathlibStandardSet false

open Filter Finset SimpleGraph
open scoped Topology

namespace Erdos146

section ForbiddenGraph

noncomputable def neighborsWithin {V : Type*} (G : SimpleGraph V)
    (s : Finset V) (v : V) : Finset V := by
  classical
  exact s.filter (G.Adj v)

def IsDegenerate {V : Type*} (r : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ s : Finset V, s.Nonempty →
    ∃ v ∈ s, (neighborsWithin G s v).card ≤ r

abbrev IsTwoDegenerate {V : Type*} (G : SimpleGraph V) : Prop :=
  IsDegenerate 2 G

def DegeneracyConjectureStatement : Prop :=
  ∀ (r q : ℕ) (H : SimpleGraph (Fin q)),
    0 < r → H.IsBipartite → IsDegenerate r H →
      Asymptotics.IsBigO Filter.atTop
        (fun n : ℕ => (SimpleGraph.extremalNumber n H : ℝ))
        (fun n : ℕ => (n : ℝ) ^ (((2 : ℕ) : ℝ) - 1 / (r : ℝ)))

theorem isTwoDegenerate_of_iso {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (hG : IsTwoDegenerate G) :
    IsTwoDegenerate H := by
  classical
  intro s hs
  let t : Finset V := s.map e.symm.toEquiv.toEmbedding
  have ht : t.Nonempty := by
    obtain ⟨w, hw⟩ := hs
    refine ⟨e.symm w, ?_⟩
    exact Finset.mem_map.mpr ⟨w, hw, rfl⟩
  obtain ⟨v, hv, hcard⟩ := hG t ht
  refine ⟨e v, ?_, ?_⟩
  · change v ∈ s.map e.symm.toEquiv.toEmbedding at hv
    obtain ⟨w, hw, heq⟩ := Finset.mem_map.mp hv
    have hwv : w = e v := by
      apply e.symm.toEquiv.injective
      simpa using heq
    simpa [← hwv] using hw
  · have hneighbors :
        neighborsWithin H s (e v) =
          (neighborsWithin G t v).map e.toEquiv.toEmbedding := by
      ext w
      simp only [neighborsWithin, Finset.mem_filter, Finset.mem_map_equiv]
      have hmembership : e.symm w ∈ t ↔ w ∈ s := by
        change e.symm w ∈ s.map e.symm.toEquiv.toEmbedding ↔ w ∈ s
        constructor
        · intro hmember
          obtain ⟨u, hu, heq⟩ := Finset.mem_map.mp hmember
          have huw : u = w := e.symm.toEquiv.injective heq
          simpa [huw] using hu
        · intro hmember
          exact Finset.mem_map.mpr ⟨w, hmember, rfl⟩
      have hadjacency :
          G.Adj v (e.symm w) ↔ H.Adj (e v) w := by
        simpa using (e.map_rel_iff (a := v) (b := e.symm w)).symm
      exact (and_congr hmembership hadjacency).symm
    rw [hneighbors, Finset.card_map]
    exact hcard

theorem isBipartite_of_iso {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (hG : G.IsBipartite) : H.IsBipartite := by
  obtain ⟨coloring⟩ := hG
  exact ⟨coloring.comp e.symm.toHom⟩

structure ParentSystem (V : Type*) where

  level : V → ℕ

  parents : V → Finset V
  parent_level : ∀ ⦃v u : V⦄, u ∈ parents v → level u + 1 = level v
  parent_card : ∀ v : V, (parents v).card ≤ 2

namespace ParentSystem

def graph {V : Type*} (P : ParentSystem V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun v u => u ∈ P.parents v)

theorem graph_adj_iff {V : Type*} (P : ParentSystem V) (v u : V) :
    (P.graph).Adj v u ↔
      v ≠ u ∧ (u ∈ P.parents v ∨ v ∈ P.parents u) := by
  rfl

theorem graph_isBipartite {V : Type*} (P : ParentSystem V) :
    P.graph.IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk
    (fun v => (⟨P.level v % 2, by omega⟩ : Fin 2)) ?_⟩
  intro v u hadj
  apply Fin.ne_of_val_ne
  change P.level v % 2 ≠ P.level u % 2
  rcases (P.graph_adj_iff v u).mp hadj with ⟨_, huv | huv⟩
  · have hlevel := P.parent_level huv
    omega
  · have hlevel := P.parent_level huv
    omega

theorem graph_isTwoDegenerate {V : Type*} (P : ParentSystem V) :
    IsTwoDegenerate P.graph := by
  classical
  intro s hs
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image s P.level hs
  refine ⟨v, hv, ?_⟩
  have hsubset : neighborsWithin P.graph s v ⊆ P.parents v := by
    intro u hu
    have hus : u ∈ s ∧ P.graph.Adj v u := by
      simpa [neighborsWithin] using hu
    rcases (P.graph_adj_iff v u).mp hus.2 with ⟨_, hparent | hchild⟩
    · exact hparent
    · have hlevel := P.parent_level hchild
      have hle := hmax u hus.1
      omega
  exact (Finset.card_le_card hsubset).trans (P.parent_card v)

end ParentSystem

def PairLayer (baseSize : ℕ) : ℕ → Type
  | 0 => Fin baseSize
  | i + 1 => {parents : Finset (PairLayer baseSize i) // parents.card = 2}

noncomputable instance pairLayerFintype (baseSize i : ℕ) :
    Fintype (PairLayer baseSize i) := by
  classical
  induction i with
  | zero =>
      change Fintype (Fin baseSize)
      infer_instance
  | succ i ih =>
      letI := ih
      change Fintype
        {parents : Finset (PairLayer baseSize i) // parents.card = 2}
      infer_instance

theorem pairLayer_card_zero (baseSize : ℕ) :
    Fintype.card (PairLayer baseSize 0) = baseSize := by
  change Fintype.card (Fin baseSize) = baseSize
  simp

theorem pairLayer_card_succ (baseSize i : ℕ) :
    Fintype.card (PairLayer baseSize (i + 1)) =
      (Fintype.card (PairLayer baseSize i)).choose 2 := by
  classical
  let layerPairs : Finset (Finset (PairLayer baseSize i)) :=
    (Finset.univ : Finset (PairLayer baseSize i)).powersetCard 2
  let equivalence : PairLayer baseSize (i + 1) ≃ layerPairs :=
    { toFun := fun p =>
        ⟨p.val, by
          apply Finset.mem_powersetCard.mpr
          exact ⟨Finset.subset_univ _, p.property⟩⟩
      invFun := fun p => ⟨p.val, (Finset.mem_powersetCard.mp p.property).2⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  calc
    Fintype.card (PairLayer baseSize (i + 1)) = Fintype.card layerPairs :=
      Fintype.card_congr equivalence
    _ = layerPairs.card := Fintype.card_coe layerPairs
    _ = (Fintype.card (PairLayer baseSize i)).choose 2 := by
      simp [layerPairs]

theorem le_choose_two_of_four {size : ℕ} (hsize : 4 ≤ size) :
    size ≤ size.choose 2 := by
  have hreal : (4 : ℝ) ≤ (size : ℝ) := by
    exact_mod_cast hsize
  have hchoose :
      (size.choose 2 : ℝ) =
        (size : ℝ) * ((size : ℝ) - 1) / 2 :=
    Nat.cast_choose_two ℝ size
  have hbound : (size : ℝ) ≤ (size.choose 2 : ℝ) := by
    rw [hchoose]
    nlinarith [sq_nonneg ((size : ℝ) - 2)]
  exact_mod_cast hbound

theorem pairLayer_card_ge_base
    (baseSize i : ℕ) (hbase : 4 ≤ baseSize) :
    baseSize ≤ Fintype.card (PairLayer baseSize i) := by
  induction i with
  | zero =>
      rw [pairLayer_card_zero]
  | succ i ih =>
      rw [pairLayer_card_succ]
      exact ih.trans
        (le_choose_two_of_four (hbase.trans ih))

noncomputable def pairLayerFinEquiv (baseSize layer : ℕ) :
    PairLayer baseSize layer ≃
      Fin (Fintype.card (PairLayer baseSize layer)) :=
  Fintype.equivFin (PairLayer baseSize layer)

noncomputable def pairLayerPairEquiv (baseSize layer : ℕ) :
    PairLayer (Fintype.card (PairLayer baseSize layer)) 1 ≃
      PairLayer baseSize (layer + 1) := by
  classical
  change
    {parents : Finset
      (Fin (Fintype.card (PairLayer baseSize layer))) //
        parents.card = 2} ≃
      {parents : Finset (PairLayer baseSize layer) //
        parents.card = 2}
  exact
    (pairLayerFinEquiv baseSize layer).symm.finsetCongr.subtypeEquiv
      (fun parents => by
        simp [Equiv.finsetCongr_apply])

theorem pairLayerPair_nonempty
    {parentCount : ℕ}
    (hparents : 2 ≤ parentCount) :
    Nonempty (PairLayer parentCount 1) := by
  apply Fintype.card_pos_iff.mp
  rw [pairLayer_card_succ parentCount 0,
    pairLayer_card_zero]
  exact Nat.choose_pos hparents

abbrev PairVertex (baseSize depth : ℕ) :=
  Σ i : Fin (depth + 1), PairLayer baseSize i.val

def pairLayerEmbedding (baseSize depth i : ℕ) (hi : i < depth + 1) :
    PairLayer baseSize i ↪ PairVertex baseSize depth where
  toFun v := ⟨⟨i, hi⟩, v⟩
  inj' := by
    intro v w heq
    cases heq
    rfl

noncomputable def pairParents (baseSize depth : ℕ) :
    PairVertex baseSize depth → Finset (PairVertex baseSize depth)
  | ⟨⟨0, _⟩, _⟩ => ∅
  | ⟨⟨i + 1, hi⟩, v⟩ =>
      v.val.map (pairLayerEmbedding baseSize depth i (by omega))

noncomputable def pairParentSystem (baseSize depth : ℕ) :
    ParentSystem (PairVertex baseSize depth) where
  level v := v.1.val
  parents := pairParents baseSize depth
  parent_level := by
    classical
    rintro ⟨⟨i, hi⟩, v⟩ ⟨⟨j, hj⟩, u⟩ hparent
    cases i with
    | zero =>
        simp [pairParents] at hparent
    | succ i =>
        change {parents : Finset (PairLayer baseSize i) // parents.card = 2} at v
        simp only [pairParents, Finset.mem_map] at hparent
        obtain ⟨w, _, hw⟩ := hparent
        have hlevels := congrArg
          (fun z : PairVertex baseSize depth => z.1.val) hw
        change i = j at hlevels
        change j + 1 = i + 1
        omega
  parent_card := by
    classical
    rintro ⟨⟨i, hi⟩, v⟩
    cases i with
    | zero =>
        simp [pairParents]
    | succ i =>
        change {parents : Finset (PairLayer baseSize i) // parents.card = 2} at v
        simp [pairParents, v.property]

theorem pairGraph_parent_child_adj
    (baseSize depth layer : ℕ)
    (hlayer : layer + 1 < depth + 1)
    (child : PairLayer baseSize (layer + 1))
    (parent : PairLayer baseSize layer)
    (hparent : parent ∈ child.val) :
    (pairParentSystem baseSize depth).graph.Adj
      (pairLayerEmbedding baseSize depth (layer + 1) hlayer child)
      (pairLayerEmbedding baseSize depth layer (by omega) parent) := by
  apply (ParentSystem.graph_adj_iff _ _ _).mpr
  constructor
  · intro hequal
    have hlevels := congrArg
      (fun vertex : PairVertex baseSize depth => vertex.1.val)
      hequal
    change layer + 1 = layer at hlevels
    omega
  · left
    change
      pairLayerEmbedding baseSize depth layer (by omega) parent ∈
        pairParents baseSize depth
          (pairLayerEmbedding baseSize depth (layer + 1)
            hlayer child)
    change
      pairLayerEmbedding baseSize depth layer (by omega) parent ∈
        child.val.map
          (pairLayerEmbedding baseSize depth layer (by omega))
    exact Finset.mem_map.mpr ⟨parent, hparent, rfl⟩

theorem pairGraph_isBipartite (baseSize depth : ℕ) :
    (pairParentSystem baseSize depth).graph.IsBipartite :=
  ParentSystem.graph_isBipartite (pairParentSystem baseSize depth)

theorem pairGraph_isTwoDegenerate (baseSize depth : ℕ) :
    IsTwoDegenerate (pairParentSystem baseSize depth).graph :=
  ParentSystem.graph_isTwoDegenerate (pairParentSystem baseSize depth)

def pairBaseVertex (baseSize depth : ℕ) (a : Fin baseSize) :
    PairVertex baseSize depth :=
  pairLayerEmbedding baseSize depth 0 (by omega) a

theorem pairLayer_reaches_base (baseSize depth : ℕ) :
    ∀ (i : ℕ) (hi : i < depth + 1) (v : PairLayer baseSize i),
      ∃ a : Fin baseSize,
        (pairParentSystem baseSize depth).graph.Reachable
          (pairLayerEmbedding baseSize depth i hi v)
          (pairBaseVertex baseSize depth a) := by
  intro i
  induction i with
  | zero =>
      intro hi v
      exact ⟨v, SimpleGraph.Reachable.rfl⟩
  | succ i ih =>
      intro hi v
      change {parents : Finset (PairLayer baseSize i) // parents.card = 2} at v
      have hnonempty : v.val.Nonempty := by
        apply Finset.card_pos.mp
        omega
      obtain ⟨parent, hparent⟩ := hnonempty
      let lower := pairLayerEmbedding baseSize depth i (by omega) parent
      let upper := pairLayerEmbedding baseSize depth (i + 1) hi v
      have hedge :
          (pairParentSystem baseSize depth).graph.Adj upper lower := by
        apply (ParentSystem.graph_adj_iff _ upper lower).mpr
        constructor
        · intro heq
          have hlevels := congrArg
            (fun x : PairVertex baseSize depth => x.1.val) heq
          change i + 1 = i at hlevels
          omega
        · left
          change lower ∈ pairParents baseSize depth upper
          change lower ∈
            v.val.map (pairLayerEmbedding baseSize depth i (by omega))
          exact Finset.mem_map.mpr ⟨parent, hparent, rfl⟩
      obtain ⟨a, ha⟩ := ih (by omega) parent
      refine ⟨a, hedge.reachable.trans ?_⟩
      exact ha

theorem pairBaseVertices_reachable (baseSize depth : ℕ)
    (hdepth : 0 < depth) (a b : Fin baseSize) :
    (pairParentSystem baseSize depth).graph.Reachable
      (pairBaseVertex baseSize depth a)
      (pairBaseVertex baseSize depth b) := by
  classical
  let pairDecidableEq : DecidableEq (PairLayer baseSize 0) := Classical.decEq _
  by_cases hab : a = b
  · subst b
    exact SimpleGraph.Reachable.rfl
  · let pair : PairLayer baseSize 1 :=
      ⟨{a, b}, Finset.card_pair hab⟩
    let bridge := pairLayerEmbedding baseSize depth 1 (by omega) pair
    have hadj (x : Fin baseSize) (hx : x = a ∨ x = b) :
        (pairParentSystem baseSize depth).graph.Adj
          bridge (pairBaseVertex baseSize depth x) := by
      apply (ParentSystem.graph_adj_iff _ bridge _).mpr
      constructor
      · intro heq
        have hlevels := congrArg
          (fun z : PairVertex baseSize depth => z.1.val) heq
        change 1 = 0 at hlevels
        omega
      · left
        change pairBaseVertex baseSize depth x ∈
          pairParents baseSize depth bridge
        have hxmem : x ∈ ({a, b} : Finset (PairLayer baseSize 0)) := by
          rcases hx with hxa | hxb
          · rw [hxa]
            exact @Finset.mem_insert_self (PairLayer baseSize 0)
              pairDecidableEq a ({b} : Finset (PairLayer baseSize 0))
          · rw [hxb]
            exact @Finset.mem_insert_of_mem (PairLayer baseSize 0)
              pairDecidableEq ({b} : Finset (PairLayer baseSize 0)) b a
              (Finset.mem_singleton_self b)
        change
          pairLayerEmbedding baseSize depth 0 (by omega) x ∈
            ({a, b} : Finset (PairLayer baseSize 0)).map
              (pairLayerEmbedding baseSize depth 0 (by omega))
        exact Finset.mem_map.mpr ⟨x, hxmem, rfl⟩
    exact (hadj a (Or.inl rfl)).symm.reachable.trans
      (hadj b (Or.inr rfl)).reachable

theorem pairGraph_connected (baseSize depth : ℕ)
    (hbase : 0 < baseSize) (hdepth : 0 < depth) :
    (pairParentSystem baseSize depth).graph.Connected := by
  let root : Fin baseSize := ⟨0, hbase⟩
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨pairBaseVertex baseSize depth root, ?_⟩
  rintro ⟨⟨i, hi⟩, v⟩
  obtain ⟨a, ha⟩ := pairLayer_reaches_base baseSize depth i hi v
  exact (pairBaseVertices_reachable baseSize depth hdepth root a).trans ha.symm

noncomputable def pairGraphOverFin (baseSize depth : ℕ) :
    SimpleGraph (Fin (Fintype.card (PairVertex baseSize depth))) :=
  (pairParentSystem baseSize depth).graph.overFin rfl

noncomputable def pairGraphOverFinIso (baseSize depth : ℕ) :
    (pairParentSystem baseSize depth).graph ≃g
      pairGraphOverFin baseSize depth :=
  (pairParentSystem baseSize depth).graph.overFinIso rfl

theorem pairGraphOverFin_connected (baseSize depth : ℕ)
    (hbase : 0 < baseSize) (hdepth : 0 < depth) :
    (pairGraphOverFin baseSize depth).Connected :=
  (pairGraphOverFinIso baseSize depth).connected_iff.mp
    (pairGraph_connected baseSize depth hbase hdepth)

theorem pairGraphOverFin_isBipartite (baseSize depth : ℕ) :
    (pairGraphOverFin baseSize depth).IsBipartite :=
  isBipartite_of_iso (pairGraphOverFinIso baseSize depth)
    (pairGraph_isBipartite baseSize depth)

theorem pairGraphOverFin_isTwoDegenerate (baseSize depth : ℕ) :
    IsTwoDegenerate (pairGraphOverFin baseSize depth) :=
  isTwoDegenerate_of_iso (pairGraphOverFinIso baseSize depth)
    (pairGraph_isTwoDegenerate baseSize depth)

open Classical in
theorem degree_gt_two_of_three_neighbors
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (v x y z : V)
    (hx : G.Adj v x) (hy : G.Adj v y) (hz : G.Adj v z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    2 < G.degree v := by
  classical
  change 2 < (G.neighborFinset v).card
  apply Finset.two_lt_card_iff.mpr
  exact ⟨x, y, z,
    (G.mem_neighborFinset v x).mpr hx,
    (G.mem_neighborFinset v y).mpr hy,
    (G.mem_neighborFinset v z).mpr hz,
    hxy, hxz, hyz⟩

open Classical in
theorem pairGraph_exists_adj_degree_gt_two
    (baseSize depth : ℕ) (hbase : 4 ≤ baseSize) (hdepth : 2 ≤ depth) :
    ∃ u v : PairVertex baseSize depth,
      (pairParentSystem baseSize depth).graph.Adj u v ∧
      2 < (pairParentSystem baseSize depth).graph.degree u ∧
      2 < (pairParentSystem baseSize depth).graph.degree v := by
  classical
  let a : PairLayer baseSize 0 := ⟨0, by omega⟩
  let b : PairLayer baseSize 0 := ⟨1, by omega⟩
  let c : PairLayer baseSize 0 := ⟨2, by omega⟩
  let d : PairLayer baseSize 0 := ⟨3, by omega⟩
  let pairDecidableEq : DecidableEq (PairLayer baseSize 0) := Classical.decEq _
  have hab : a ≠ b := by
    intro heq
    have hval := congrArg Fin.val heq
    change 0 = 1 at hval
    omega
  have hac : a ≠ c := by
    intro heq
    have hval := congrArg Fin.val heq
    change 0 = 2 at hval
    omega
  have had : a ≠ d := by
    intro heq
    have hval := congrArg Fin.val heq
    change 0 = 3 at hval
    omega
  have hbc : b ≠ c := by
    intro heq
    have hval := congrArg Fin.val heq
    change 1 = 2 at hval
    omega
  have hbd : b ≠ d := by
    intro heq
    have hval := congrArg Fin.val heq
    change 1 = 3 at hval
    omega
  have hcd : c ≠ d := by
    intro heq
    have hval := congrArg Fin.val heq
    change 2 = 3 at hval
    omega
  let ab : PairLayer baseSize 1 :=
    ⟨{a, b}, Finset.card_pair hab⟩
  let ac : PairLayer baseSize 1 :=
    ⟨{a, c}, Finset.card_pair hac⟩
  let ad : PairLayer baseSize 1 :=
    ⟨{a, d}, Finset.card_pair had⟩
  have habac : ab ≠ ac := by
    intro heq
    have hmem : b ∈ ab.val := by
      change b ∈ ({a, b} : Finset (PairLayer baseSize 0))
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    rw [heq] at hmem
    change b ∈ ({a, c} : Finset (PairLayer baseSize 0)) at hmem
    rcases Finset.mem_insert.mp hmem with hba | hbc'
    · exact hab hba.symm
    · exact hbc (Finset.mem_singleton.mp hbc')
  have habad : ab ≠ ad := by
    intro heq
    have hmem : b ∈ ab.val := by
      change b ∈ ({a, b} : Finset (PairLayer baseSize 0))
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    rw [heq] at hmem
    change b ∈ ({a, d} : Finset (PairLayer baseSize 0)) at hmem
    rcases Finset.mem_insert.mp hmem with hba | hbd'
    · exact hab hba.symm
    · exact hbd (Finset.mem_singleton.mp hbd')
  have hacad : ac ≠ ad := by
    intro heq
    have hmem : c ∈ ac.val := by
      change c ∈ ({a, c} : Finset (PairLayer baseSize 0))
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self c)
    rw [heq] at hmem
    change c ∈ ({a, d} : Finset (PairLayer baseSize 0)) at hmem
    rcases Finset.mem_insert.mp hmem with hca | hcd'
    · exact hac hca.symm
    · exact hcd (Finset.mem_singleton.mp hcd')
  let abc : PairLayer baseSize 2 :=
    ⟨{ab, ac}, Finset.card_pair habac⟩
  let va : PairVertex baseSize depth :=
    pairLayerEmbedding baseSize depth 0 (by omega) a
  let vb : PairVertex baseSize depth :=
    pairLayerEmbedding baseSize depth 0 (by omega) b
  let vab : PairVertex baseSize depth :=
    pairLayerEmbedding baseSize depth 1 (by omega) ab
  let vac : PairVertex baseSize depth :=
    pairLayerEmbedding baseSize depth 1 (by omega) ac
  let vad : PairVertex baseSize depth :=
    pairLayerEmbedding baseSize depth 1 (by omega) ad
  let vabc : PairVertex baseSize depth :=
    pairLayerEmbedding baseSize depth 2 (by omega) abc
  let G : SimpleGraph (PairVertex baseSize depth) :=
    (pairParentSystem baseSize depth).graph
  have ha_mem_ab : a ∈ ab.val := by
    change a ∈ ({a, b} : Finset (PairLayer baseSize 0))
    exact Finset.mem_insert_self a {b}
  have hb_mem_ab : b ∈ ab.val := by
    change b ∈ ({a, b} : Finset (PairLayer baseSize 0))
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  have ha_mem_ac : a ∈ ac.val := by
    change a ∈ ({a, c} : Finset (PairLayer baseSize 0))
    exact Finset.mem_insert_self a {c}
  have ha_mem_ad : a ∈ ad.val := by
    change a ∈ ({a, d} : Finset (PairLayer baseSize 0))
    exact Finset.mem_insert_self a {d}
  have hab_a : G.Adj vab va := by
    simpa only [G, vab, va] using
      pairGraph_parent_child_adj baseSize depth 0
        (by omega) ab a ha_mem_ab
  have hab_b : G.Adj vab vb := by
    simpa only [G, vab, vb] using
      pairGraph_parent_child_adj baseSize depth 0
        (by omega) ab b hb_mem_ab
  have hac_a : G.Adj vac va := by
    simpa only [G, vac, va] using
      pairGraph_parent_child_adj baseSize depth 0
        (by omega) ac a ha_mem_ac
  have had_a : G.Adj vad va := by
    simpa only [G, vad, va] using
      pairGraph_parent_child_adj baseSize depth 0
        (by omega) ad a ha_mem_ad
  have habc_ab : G.Adj vabc vab := by
    simpa only [G, vabc, vab] using
      pairGraph_parent_child_adj baseSize depth 1
        (by omega) abc ab (by
          change ab ∈ ({ab, ac} : Finset (PairLayer baseSize 1))
          exact Finset.mem_insert_self ab {ac})
  have hab_vac : vab ≠ vac := by
    intro heq
    apply habac
    exact (pairLayerEmbedding baseSize depth 1 (by omega)).inj' heq
  have hab_vad : vab ≠ vad := by
    intro heq
    apply habad
    exact (pairLayerEmbedding baseSize depth 1 (by omega)).inj' heq
  have hac_vad : vac ≠ vad := by
    intro heq
    apply hacad
    exact (pairLayerEmbedding baseSize depth 1 (by omega)).inj' heq
  have ha_b : va ≠ vb := by
    intro heq
    have hfin := (pairLayerEmbedding baseSize depth 0 (by omega)).inj' heq
    have hval := congrArg Fin.val hfin
    simp [a, b] at hval
  have ha_abc : va ≠ vabc := by
    intro heq
    have hlevel := congrArg
      (fun vertex : PairVertex baseSize depth => vertex.1.val) heq
    change 0 = 2 at hlevel
    omega
  have hb_abc : vb ≠ vabc := by
    intro heq
    have hlevel := congrArg
      (fun vertex : PairVertex baseSize depth => vertex.1.val) heq
    change 0 = 2 at hlevel
    omega
  have ha_degree : 2 < G.degree va :=
    degree_gt_two_of_three_neighbors G va vab vac vad
      hab_a.symm hac_a.symm had_a.symm
      hab_vac hab_vad hac_vad
  have hab_degree : 2 < G.degree vab :=
    degree_gt_two_of_three_neighbors G vab va vb vabc
      hab_a hab_b habc_ab.symm ha_b ha_abc hb_abc
  exact ⟨va, vab, hab_a.symm, ha_degree, hab_degree⟩

open Classical in
theorem pairGraphOverFin_exists_adj_degree_gt_two
    (baseSize depth : ℕ) (hbase : 4 ≤ baseSize) (hdepth : 2 ≤ depth) :
    ∃ u v : Fin (Fintype.card (PairVertex baseSize depth)),
      (pairGraphOverFin baseSize depth).Adj u v ∧
      2 < (pairGraphOverFin baseSize depth).degree u ∧
      2 < (pairGraphOverFin baseSize depth).degree v := by
  classical
  obtain ⟨u, v, hadj, hu, hv⟩ :=
    pairGraph_exists_adj_degree_gt_two baseSize depth hbase hdepth
  let e := pairGraphOverFinIso baseSize depth
  refine ⟨e u, e v, (e.map_rel_iff).mpr hadj, ?_, ?_⟩
  · simpa only [e.degree_eq] using hu
  · simpa only [e.degree_eq] using hv

open Classical in
theorem bipartition_maximum_degree_gt_two_of_adj
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) {u v : V}
    (hadj : G.Adj u v)
    (hu : 2 < G.degree u) (hv : 2 < G.degree v) :
    ∀ coloring : G.Coloring (Fin 2), ∀ side : Fin 2,
      2 < (Finset.univ.filter
        (fun vertex : V => coloring vertex = side)).sup
        (fun vertex => G.degree vertex) := by
  classical
  intro coloring side
  have hwitness :
      ∃ vertex : V,
        coloring vertex = side ∧ 2 < G.degree vertex := by
    by_cases hcolor : coloring u = side
    · exact ⟨u, hcolor, hu⟩
    · refine ⟨v, ?_, hv⟩
      have hproper : coloring u ≠ coloring v := coloring.valid hadj
      apply Fin.ext
      have hu_lt := (coloring u).isLt
      have hv_lt := (coloring v).isLt
      have hside_lt := side.isLt
      omega
  obtain ⟨vertex, hcolor, hdegree⟩ := hwitness
  have hmember :
      vertex ∈ Finset.univ.filter
        (fun candidate : V => coloring candidate = side) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ vertex, hcolor⟩
  exact lt_of_lt_of_le hdegree
    (Finset.le_sup (f := fun candidate => G.degree candidate) hmember)

open Classical in
theorem pairGraphOverFin_bipartition_maximum_degree_gt_two
    (baseSize depth : ℕ) (hbase : 4 ≤ baseSize) (hdepth : 2 ≤ depth) :
    ∀ coloring : (pairGraphOverFin baseSize depth).Coloring (Fin 2),
      ∀ side : Fin 2,
        2 < (Finset.univ.filter
          (fun vertex : Fin (Fintype.card (PairVertex baseSize depth)) =>
            coloring vertex = side)).sup
          (fun vertex => (pairGraphOverFin baseSize depth).degree vertex) := by
  classical
  obtain ⟨u, v, hadj, hu, hv⟩ :=
    pairGraphOverFin_exists_adj_degree_gt_two baseSize depth hbase hdepth
  exact bipartition_maximum_degree_gt_two_of_adj
    (pairGraphOverFin baseSize depth) hadj hu hv

end ForbiddenGraph

end Erdos146
