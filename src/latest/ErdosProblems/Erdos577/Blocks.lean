import ErdosProblems.Erdos577.Counting

/-! Four-element cycle blocks and their disjoint finite partitions. -/

namespace Erdos577

open Finset Function
open scoped BigOperators

variable {V : Type*} [DecidableEq V]
variable {G H : SimpleGraph V}

/-- A specified finite set is exactly the vertex set of a four-cycle. -/
def QuadOn (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∃ q : Quadrilateral G, q.support = s

namespace QuadOn

lemma card {s : Finset V} (h : QuadOn G s) : s.card = 4 := by
  obtain ⟨q, rfl⟩ := h
  exact q.card_support

lemma mono {s : Finset V} (h : QuadOn G s) (hGH : G ≤ H) : QuadOn H s := by
  obtain ⟨q, hq⟩ := h
  refine ⟨(SimpleGraph.Copy.ofLE G H hGH).comp q, ?_⟩
  simpa [Quadrilateral.support] using hq

lemma induced_copy {s : Finset V} (h : QuadOn G s) :
    Nonempty (Quadrilateral (G.induce (s : Set V))) := by
  obtain ⟨q, hq⟩ := h
  have hm (i : Fin 4) : q i ∈ s := by
    rw [← hq]
    exact (Quadrilateral.mem_support q _).mpr ⟨i, rfl⟩
  refine ⟨{
    toHom := {
      toFun := fun i ↦ ⟨q i, hm i⟩
      map_rel' := fun h ↦ q.toHom.map_rel' h }
    injective' := ?_ }⟩
  intro i j hij
  exact q.injective (congrArg Subtype.val hij)

lemma of_induced_copy {s : Finset V} (hs : s.card = 4)
    (h : Nonempty (Quadrilateral (G.induce (s : Set V)))) : QuadOn G s := by
  obtain ⟨q⟩ := h
  let q' : Quadrilateral G := (SimpleGraph.Copy.induce G (s : Set V)).comp q
  have hsub : q'.support ⊆ s := by
    intro v hv
    obtain ⟨i, rfl⟩ := (Quadrilateral.mem_support q' v).mp hv
    exact (q i).property
  refine ⟨q', eq_of_subset_of_card_le hsub ?_⟩
  simp [hs]

variable [DecidableRel G.Adj]

lemma two_le_degreeIn {s : Finset V} (h : QuadOn G s) {v : V} (hv : v ∈ s) :
    2 ≤ degreeIn G v s := by
  obtain ⟨q⟩ := h.induced_copy
  have hsurj : Surjective (q : Fin 4 → (s : Set V)) := by
    exact ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨q.injective, by simp [h.card]⟩).2
  obtain ⟨i, hi⟩ := hsurj ⟨v, hv⟩
  have hd := q.degree_le i
  have he : (q i : V) = v := congrArg Subtype.val hi
  simpa only [SimpleGraph.cycleGraph_degree_three_le, degree_induce_eq_degreeIn, he] using hd

lemma of_degreeIn {s : Finset V} (hs : s.card = 4)
    (h : ∀ v ∈ s, 2 ≤ degreeIn G v s) : QuadOn G s := by
  apply of_induced_copy hs
  apply quadrilateral_of_card_four (G.induce (s : Set V))
  · change Fintype.card s = 4
    rw [Fintype.card_coe, hs]
  · intro v
    rw [degree_induce_eq_degreeIn]
    exact h v v.property

lemma iff_degreeIn (s : Finset V) :
    QuadOn G s ↔ s.card = 4 ∧ ∀ v ∈ s, 2 ≤ degreeIn G v s := by
  exact ⟨fun h ↦ ⟨h.card, fun _ hv ↦ h.two_le_degreeIn hv⟩,
    fun h ↦ of_degreeIn h.1 h.2⟩

lemma four_le_edgeCount {s : Finset V} (h : QuadOn G s) : 4 ≤ edgeCount G s := by
  have hc : 8 ≤ contacts G s s := by
    calc
      8 = ∑ _ ∈ s, (2 : ℕ) := by simp [h.card]
      _ ≤ ∑ v ∈ s, degreeIn G v s := sum_le_sum fun _ hv ↦ h.two_le_degreeIn hv
      _ = contacts G s s := rfl
  rw [contacts_self_eq_twice_edgeCount] at hc
  omega

lemma edgeCount_le_six {s : Finset V} (h : QuadOn G s) : edgeCount G s ≤ 6 :=
  Erdos577.edgeCount_le_six G h.card

lemma of_triangle {t : Finset V} (ht : G.IsNClique 3 t) {x : V} (hx : x ∉ t)
    (hd : 2 ≤ degreeIn G x t) : QuadOn G (insert x t) := by
  apply of_degreeIn
  · simp [hx, ht.card_eq]
  · intro v hv
    rcases mem_insert.mp hv with he | hv
    · subst v
      rw [degreeIn_insert G x x hx]
      simpa using hd
    · calc
        2 = degreeIn G v t := by rw [degreeIn_clique G ht.isClique hv, ht.card_eq]
        _ ≤ degreeIn G v (insert x t) := degreeIn_mono G v (subset_insert x t)

end QuadOn

/-- An actual partition of a finite vertex set into four-cycle blocks. -/
structure BlockPartition (G : SimpleGraph V) (s : Finset V) where
  blocks : Finset (Finset V)
  disjoint : (blocks : Set (Finset V)).PairwiseDisjoint id
  cover : blocks.biUnion id = s
  quad : ∀ b ∈ blocks, QuadOn G b

namespace BlockPartition

variable {s : Finset V}

lemma card (p : BlockPartition G s) : s.card = 4 * p.blocks.card := by
  calc
    s.card = (p.blocks.biUnion id).card := congrArg Finset.card p.cover.symm
    _ = ∑ b ∈ p.blocks, b.card := card_biUnion p.disjoint
    _ = ∑ _ ∈ p.blocks, 4 :=
      sum_congr rfl fun b hb ↦ (p.quad b hb).card
    _ = 4 * p.blocks.card := by simp [Nat.mul_comm]

lemma block_subset (p : BlockPartition G s) {b : Finset V} (hb : b ∈ p.blocks) : b ⊆ s := by
  intro v hv
  rw [← p.cover]
  exact mem_biUnion.mpr ⟨b, hb, hv⟩

/-- The empty set has the empty partition. -/
def empty (G : SimpleGraph V) : BlockPartition G ∅ where
  blocks := ∅
  disjoint := by simp
  cover := by simp
  quad := by simp

/-- A single actual cycle is a one-block partition. -/
def single {s : Finset V} (h : QuadOn G s) : BlockPartition G s where
  blocks := {s}
  disjoint := by simp
  cover := by simp
  quad := by simpa

/-- Combine partitions on disjoint vertex sets. -/
def union {s t : Finset V} (p : BlockPartition G s) (q : BlockPartition G t)
    (h : Disjoint s t) : BlockPartition G (s ∪ t) where
  blocks := p.blocks ∪ q.blocks
  disjoint := by
    intro b hb c hc hbc
    rcases mem_union.mp hb with hb | hb <;> rcases mem_union.mp hc with hc | hc
    · exact p.disjoint hb hc hbc
    · exact h.mono (p.block_subset hb) (q.block_subset hc)
    · exact (h.mono (p.block_subset hc) (q.block_subset hb)).symm
    · exact q.disjoint hb hc hbc
  cover := by rw [union_biUnion, p.cover, q.cover]
  quad := by
    intro b hb
    rcases mem_union.mp hb with hb | hb
    · exact p.quad b hb
    · exact q.quad b hb

/-- Enumerate the finite block family without changing its vertices. -/
noncomputable def indexEquiv (p : BlockPartition G s) : Fin p.blocks.card ≃ p.blocks :=
  (Fintype.equivFinOfCardEq (Fintype.card_coe p.blocks)).symm

/-- Choose an orientation and a starting point for a block's existing cycle. -/
noncomputable def blockCycle (p : BlockPartition G s) (b : p.blocks) : Quadrilateral G :=
  (p.quad b b.property).choose

@[simp] lemma blockCycle_support (p : BlockPartition G s) (b : p.blocks) :
    (p.blockCycle b).support = b := (p.quad b b.property).choose_spec

/-- A finite partition yields the exact product-indexed packing. -/
noncomputable def toPacking (p : BlockPartition G s) : Packing G p.blocks.card where
  vertices := {
    toFun := fun v ↦ (p.blockCycle (p.indexEquiv v.1)) v.2
    inj' := by
      rintro ⟨i, a⟩ ⟨j, b⟩ he
      have hij : i = j := by
        by_contra hij
        have hne : (p.indexEquiv i).val ≠ (p.indexEquiv j).val := by
          intro hval
          exact hij (p.indexEquiv.injective (Subtype.ext hval))
        have hd := p.disjoint (p.indexEquiv i).property (p.indexEquiv j).property hne
        apply (Finset.disjoint_left.mp hd) (a := (p.blockCycle (p.indexEquiv i)) a)
        · rw [← p.blockCycle_support (p.indexEquiv i)]
          exact (Quadrilateral.mem_support _ _).mpr ⟨a, rfl⟩
        · rw [← p.blockCycle_support (p.indexEquiv j)]
          exact (Quadrilateral.mem_support _ _).mpr ⟨b, he.symm⟩
      subst j
      exact Prod.ext rfl ((p.blockCycle (p.indexEquiv i)).injective he) }
  adjacent i j := (p.blockCycle (p.indexEquiv i)).adjacent j

lemma toPacking_support (p : BlockPartition G s) : p.toPacking.support = s := by
  apply eq_of_subset_of_card_le
  · intro v hv
    obtain ⟨⟨i, j⟩, _, rfl⟩ := mem_image.mp hv
    apply p.block_subset (p.indexEquiv i).property
    rw [← p.blockCycle_support (p.indexEquiv i)]
    exact (Quadrilateral.mem_support _ _).mpr ⟨j, rfl⟩
  · rw [Packing.card_support, p.card]

lemma hasPacking_of_card (p : BlockPartition G s) (k : ℕ) (hs : s.card = 4 * k) :
    HasPacking G k := by
  have hp := p.card
  have hk : p.blocks.card = k := by omega
  have h : HasPacking G p.blocks.card := ⟨p.toPacking⟩
  simpa only [hk] using h

end BlockPartition

end Erdos577
