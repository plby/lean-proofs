import ErdosProblems.Erdos556.Definitions

/-!
# Finite edge-set matchings

The representation exposes the edge count and uncovered vertices for finite
augmentation arguments. Every member is an actual edge with two endpoints.
-/

namespace Erdos556

open SimpleGraph Finset

def EdgeMatching {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (M : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧
    ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e.toFinset f.toFinset

def matchingSupport {V : Type*} [DecidableEq V] (M : Finset (Sym2 V)) : Finset V :=
  M.biUnion Sym2.toFinset

theorem matchingSupport_mem {V : Type*} [DecidableEq V] {M : Finset (Sym2 V)} {v : V} :
    v ∈ matchingSupport M ↔ ∃ e ∈ M, v ∈ e := by
  simp only [matchingSupport, Finset.mem_biUnion, Sym2.mem_toFinset]

theorem EdgeMatching.empty {V : Type*} [DecidableEq V] (G : SimpleGraph V) :
    EdgeMatching G ∅ := by simp [EdgeMatching]

theorem EdgeMatching.mono {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {M T : Finset (Sym2 V)} (hM : EdgeMatching G M) (hTM : T ⊆ M) : EdgeMatching G T :=
  ⟨fun e he => hM.1 e (hTM he), fun e he f hf hne => hM.2 e (hTM he) f (hTM hf) hne⟩

theorem matchingSupport_mono {V : Type*} [DecidableEq V]
    {M T : Finset (Sym2 V)} (hTM : T ⊆ M) : matchingSupport T ⊆ matchingSupport M := by
  intro v hv
  obtain ⟨e, he, hve⟩ := matchingSupport_mem.mp hv
  exact matchingSupport_mem.mpr ⟨e, hTM he, hve⟩

theorem EdgeMatching.card_support {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {M : Finset (Sym2 V)} (hM : EdgeMatching G M) :
    (matchingSupport M).card = 2 * M.card := by
  rw [matchingSupport, Finset.card_biUnion (by
    intro e he f hf hne
    exact hM.2 e he f hf hne)]
  have hecard : ∀ e ∈ M, e.toFinset.card = 2 := by
    intro e he
    exact Sym2.card_toFinset_of_not_isDiag e (G.not_isDiag_of_mem_edgeSet (hM.1 e he))
  rw [Finset.sum_congr rfl hecard]
  simp [mul_comm]

theorem EdgeMatching.adjoin_edge {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {M : Finset (Sym2 V)} (hM : EdgeMatching G M) {u v : V} (huv : G.Adj u v)
    (hu : u ∉ matchingSupport M) (hv : v ∉ matchingSupport M) :
    EdgeMatching G (insert s(u, v) M) := by
  have hd (e : Sym2 V) (he : e ∈ M) : Disjoint s(u, v).toFinset e.toFinset := by
    apply Finset.disjoint_left.mpr
    intro x hx hxe
    have hxs : x ∈ matchingSupport M :=
      matchingSupport_mem.mpr ⟨e, he, Sym2.mem_toFinset.mp hxe⟩
    simp only [Sym2.toFinset_mk_eq, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hu hxs
    · exact hv hxs
  constructor
  · intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact huv
    · exact hM.1 e he
  · intro e he f hf hne
    rcases Finset.mem_insert.mp he with rfl | he
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · exact (hne rfl).elim
      · exact hd f hf
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · exact (hd e he).symm
      · exact hM.2 e he f hf hne

theorem exists_maximum_edgeMatching {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    ∃ M : Finset (Sym2 V), EdgeMatching G M ∧
      ∀ T, EdgeMatching G T → T.card ≤ M.card := by
  classical
  let all := G.edgeFinset.powerset.filter (EdgeMatching G)
  have hall : all.Nonempty := ⟨∅, by simp [all, EdgeMatching.empty]⟩
  obtain ⟨M, hM, hmax⟩ := all.exists_max_image Finset.card hall
  refine ⟨M, (Finset.mem_filter.mp hM).2, ?_⟩
  intro T hT
  apply hmax T
  simp only [all, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun e he => mem_edgeFinset.mpr (hT.1 e he), hT⟩

theorem maximum_edgeMatching_uncovered_independent {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) {M : Finset (Sym2 V)} (hM : EdgeMatching G M)
    (hmax : ∀ T, EdgeMatching G T → T.card ≤ M.card)
    {u v : V} (hu : u ∉ matchingSupport M) (hv : v ∉ matchingSupport M) : ¬ G.Adj u v := by
  intro huv
  have he : s(u, v) ∉ M := by
    intro he
    exact hu (matchingSupport_mem.mpr ⟨s(u, v), he, Sym2.mem_mk_left _ _⟩)
  have hh := hmax _ (hM.adjoin_edge huv hu hv)
  rw [Finset.card_insert_of_notMem he] at hh
  omega

theorem edge_not_mem_of_left_uncovered {V : Type*} [DecidableEq V]
    {M : Finset (Sym2 V)} {u v : V} (hu : u ∉ matchingSupport M) : s(u, v) ∉ M := by
  intro he
  exact hu (matchingSupport_mem.mpr ⟨s(u, v), he, Sym2.mem_mk_left _ _⟩)

theorem matchingSupport_insert {V : Type*} [DecidableEq V]
    (M : Finset (Sym2 V)) (e : Sym2 V) :
    matchingSupport (insert e M) = e.toFinset ∪ matchingSupport M := by
  simp [matchingSupport]

theorem EdgeMatching.uncovered_erase_left {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {M : Finset (Sym2 V)} (hM : EdgeMatching G M)
    {u v : V} (he : s(u, v) ∈ M) : u ∉ matchingSupport (M.erase s(u, v)) := by
  intro hu
  obtain ⟨e, he', hue⟩ := matchingSupport_mem.mp hu
  have hh := Finset.mem_erase.mp he'
  exact Finset.disjoint_left.mp (hM.2 _ he _ hh.2 (Ne.symm hh.1))
    (Sym2.mem_toFinset.mpr (Sym2.mem_mk_left _ _)) (Sym2.mem_toFinset.mpr hue)

theorem EdgeMatching.augment_three {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {M : Finset (Sym2 V)} (hM : EdgeMatching G M)
    {u v x y : V} (he : s(u, v) ∈ M)
    (hux : G.Adj u x) (hvy : G.Adj v y)
    (hx : x ∉ matchingSupport M) (hy : y ∉ matchingSupport M) (hxy : x ≠ y) :
    ∃ T, EdgeMatching G T ∧ T.card = M.card + 1 := by
  have huv : G.Adj u v := hM.1 _ he
  have huM : u ∈ matchingSupport M :=
    matchingSupport_mem.mpr ⟨_, he, Sym2.mem_mk_left _ _⟩
  have hvM : v ∈ matchingSupport M :=
    matchingSupport_mem.mpr ⟨_, he, Sym2.mem_mk_right _ _⟩
  let M₀ := M.erase s(u, v)
  have hM₀ : EdgeMatching G M₀ := hM.mono (Finset.erase_subset _ _)
  have hu₀ : u ∉ matchingSupport M₀ := hM.uncovered_erase_left he
  have hv₀ : v ∉ matchingSupport M₀ := by
    have hh := hM.uncovered_erase_left (u := v) (v := u) (by simpa [Sym2.eq_swap] using he)
    simpa [M₀, Sym2.eq_swap] using hh
  have hx₀ : x ∉ matchingSupport M₀ := fun hh => hx (matchingSupport_mono (Finset.erase_subset _ _) hh)
  have hy₀ : y ∉ matchingSupport M₀ := fun hh => hy (matchingSupport_mono (Finset.erase_subset _ _) hh)
  let M₁ := insert s(u, x) M₀
  have hM₁ : EdgeMatching G M₁ := hM₀.adjoin_edge hux hu₀ hx₀
  have hv₁ : v ∉ matchingSupport M₁ := by
    dsimp only [M₁]
    rw [matchingSupport_insert, Sym2.toFinset_mk_eq]
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨⟨huv.ne.symm, fun h => hx (h ▸ hvM)⟩, hv₀⟩
  have hy₁ : y ∉ matchingSupport M₁ := by
    dsimp only [M₁]
    rw [matchingSupport_insert, Sym2.toFinset_mk_eq]
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨⟨fun h => hy (h.symm ▸ huM), hxy.symm⟩, hy₀⟩
  refine ⟨insert s(v, y) M₁, hM₁.adjoin_edge hvy hv₁ hy₁, ?_⟩
  rw [Finset.card_insert_of_notMem (edge_not_mem_of_left_uncovered hv₁)]
  dsimp only [M₁]
  rw [Finset.card_insert_of_notMem (edge_not_mem_of_left_uncovered hu₀)]
  dsimp [M₀]
  rw [Finset.card_erase_of_mem he]
  have hpos := Finset.card_pos.mpr (show M.Nonempty from ⟨_, he⟩)
  omega

open scoped Classical in
theorem maximum_edgeMatching_endpoint {V : Type*} [Fintype V]
    (G : SimpleGraph V) {M : Finset (Sym2 V)} (hM : EdgeMatching G M)
    (hmax : ∀ T, EdgeMatching G T → T.card ≤ M.card)
    {u v : V} (he : s(u, v) ∈ M) :
    ((Finset.univ \ matchingSupport M).filter (G.Adj u)).card ≤ 1 ∨
      ((Finset.univ \ matchingSupport M).filter (G.Adj v)).card ≤ 1 := by
  classical
  by_contra hh
  push Not at hh
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (show 0 <
    ((Finset.univ \ matchingSupport M).filter (G.Adj v)).card by omega)
  obtain ⟨x, hx, hxy⟩ := Finset.exists_mem_ne hh.1 y
  obtain ⟨hxS, hux⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyS, hvy⟩ := Finset.mem_filter.mp hy
  obtain ⟨T, hT, hcard⟩ := hM.augment_three he hux hvy
    (Finset.mem_sdiff.mp hxS).2 (Finset.mem_sdiff.mp hyS).2 hxy
  have hbound := hmax T hT
  omega

theorem matchingSupport_inter {V : Type*} [DecidableEq V]
    (M : Finset (Sym2 V)) (A : Finset V) :
    matchingSupport M ∩ A = M.biUnion (fun e => e.toFinset ∩ A) := by
  ext x
  simp only [matchingSupport, Finset.mem_inter, Finset.mem_biUnion]
  aesop

theorem EdgeMatching.card_support_inter {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {M : Finset (Sym2 V)} (hM : EdgeMatching G M)
    (A : Finset V) (hA : ∀ e ∈ M, (e.toFinset ∩ A).card = 1) :
    (matchingSupport M ∩ A).card = M.card := by
  rw [matchingSupport_inter, Finset.card_biUnion (by
    intro e he f hf hne
    exact (hM.2 e he f hf hne).mono Finset.inter_subset_left Finset.inter_subset_left)]
  rw [Finset.sum_congr rfl hA]
  simp

end Erdos556
