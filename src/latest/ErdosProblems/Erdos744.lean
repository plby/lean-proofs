import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.ENat.Lattice
import Mathlib.Tactic

/-!
# Erdős Problem 744

Rödl and Tuza proved that, for each `k ≥ 4`, the least number of edges which
must be deleted from a sufficiently large `k`-critical graph to make it
bipartite is exactly `Nat.choose (k - 1) 2`.

The mathematical proof, including the explicit constructions used here, is
given in `tex/744.tex`.
-/

open Filter SimpleGraph
open scoped ENat

namespace Erdos744

universe u

/-- A graph is `k`-critical when it has chromatic number exactly `k` and every
proper subgraph, allowing both vertex and edge deletion, has smaller chromatic
number. -/
def IsCritical {V : Type u} (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.chromaticNumber = (k : ℕ∞) ∧
    ∀ H : G.Subgraph, H < ⊤ → H.coe.chromaticNumber < (k : ℕ∞)

/-- `G` can be made bipartite by deleting exactly `m` actual edges. -/
def CanBipartizeBy {V : Type u} [Fintype V]
    (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ E : Set (Sym2 V),
    E ⊆ G.edgeSet ∧ E.ncard = m ∧ (G.deleteEdges E).IsBipartite

/-- The fewest edges whose deletion makes `G` bipartite. -/
noncomputable def deletionNumber {V : Type u} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  sInf {m : ℕ | CanBipartizeBy G m}

lemma canBipartizeBy_allEdges {V : Type u} [Fintype V]
    (G : SimpleGraph V) : CanBipartizeBy G G.edgeSet.ncard := by
  refine ⟨G.edgeSet, Set.Subset.rfl, rfl, ?_⟩
  rw [deleteEdges_edgeSet, sdiff_self]
  exact ⟨SimpleGraph.Coloring.mk (fun _ ↦ 0) (by simp)⟩

lemma deletionCandidates_nonempty {V : Type u} [Fintype V]
    (G : SimpleGraph V) : {m : ℕ | CanBipartizeBy G m}.Nonempty :=
  ⟨G.edgeSet.ncard, canBipartizeBy_allEdges G⟩

theorem deletionNumber_spec {V : Type u} [Fintype V]
    (G : SimpleGraph V) : CanBipartizeBy G (deletionNumber G) :=
  Nat.sInf_mem (deletionCandidates_nonempty G)

theorem deletionNumber_le_of_canBipartizeBy {V : Type u} [Fintype V]
    {G : SimpleGraph V} {m : ℕ} (h : CanBipartizeBy G m) :
    deletionNumber G ≤ m :=
  Nat.sInf_le h

theorem le_deletionNumber_of_forall {V : Type u} [Fintype V]
    {G : SimpleGraph V} {b : ℕ}
    (h : ∀ m, CanBipartizeBy G m → b ≤ m) :
    b ≤ deletionNumber G :=
  h _ (deletionNumber_spec G)

/-- The possible bipartization numbers of `k`-critical graphs on `n`
vertices. -/
def criticalDeletionNumbers (k n : ℕ) : Set ℕ :=
  {m : ℕ | ∃ G : SimpleGraph (Fin n),
    IsCritical G k ∧ deletionNumber G = m}

/-- The extremal function in Problem 744.  The natural infimum is zero when
there is no critical graph of the requested exact order; the main theorem
constructs a witness throughout its range. -/
noncomputable def f (k n : ℕ) : ℕ :=
  sInf (criticalDeletionNumbers k n)

lemma criticalDeletionNumbers_nonempty {k n : ℕ}
    (hex : ∃ G : SimpleGraph (Fin n), IsCritical G k) :
    (criticalDeletionNumbers k n).Nonempty := by
  obtain ⟨G, hG⟩ := hex
  exact ⟨deletionNumber G, G, hG, rfl⟩

theorem f_spec {k n : ℕ}
    (hex : ∃ G : SimpleGraph (Fin n), IsCritical G k) :
    ∃ G : SimpleGraph (Fin n), IsCritical G k ∧ deletionNumber G = f k n := by
  exact Nat.sInf_mem (criticalDeletionNumbers_nonempty hex)

theorem f_le_deletionNumber {k n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : IsCritical G k) : f k n ≤ deletionNumber G :=
  Nat.sInf_le ⟨G, hG, rfl⟩

theorem f_le_of_critical_canBipartizeBy {k n m : ℕ}
    {G : SimpleGraph (Fin n)} (hG : IsCritical G k)
    (hdel : CanBipartizeBy G m) : f k n ≤ m :=
  (f_le_deletionNumber hG).trans
    (deletionNumber_le_of_canBipartizeBy hdel)

theorem le_f_of_forall_critical {k n b : ℕ}
    (hex : ∃ G : SimpleGraph (Fin n), IsCritical G k)
    (hlower : ∀ G : SimpleGraph (Fin n),
      IsCritical G k → b ≤ deletionNumber G) :
    b ≤ f k n := by
  obtain ⟨G, hG, hmin⟩ := f_spec hex
  rw [← hmin]
  exact hlower G hG

theorem f_eq_of_lower_of_critical_witness {k n b : ℕ}
    (hlower : ∀ G : SimpleGraph (Fin n),
      IsCritical G k → b ≤ deletionNumber G)
    {G : SimpleGraph (Fin n)} (hG : IsCritical G k)
    (hGb : deletionNumber G = b) : f k n = b := by
  apply Nat.le_antisymm
  · rw [← hGb]
    exact f_le_deletionNumber hG
  · exact le_f_of_forall_critical ⟨G, hG⟩ hlower

/-- The exact chromatic-number definition is equivalent to the convenient
coloring formulation at a successor. -/
theorem isCritical_succ_iff {V : Type u}
    (G : SimpleGraph V) (k : ℕ) :
    IsCritical G (k + 1) ↔
      G.Colorable (k + 1) ∧ ¬G.Colorable k ∧
        ∀ H : G.Subgraph, H < ⊤ → H.coe.Colorable k := by
  change
    (G.chromaticNumber = (k : ℕ∞) + 1 ∧
      ∀ H : G.Subgraph, H < ⊤ → H.coe.chromaticNumber < (k : ℕ∞) + 1) ↔ _
  rw [chromaticNumber_eq_iff_colorable_not_colorable]
  constructor
  · rintro ⟨⟨hcol, hncol⟩, hproper⟩
    refine ⟨hcol, hncol, ?_⟩
    intro H hH
    rw [← chromaticNumber_le_iff_colorable]
    exact (ENat.lt_add_one_iff (by simp : (k : ℕ∞) ≠ ⊤)).mp (hproper H hH)
  · rintro ⟨hcol, hncol, hproper⟩
    refine ⟨⟨hcol, hncol⟩, ?_⟩
    intro H hH
    exact (ENat.lt_add_one_iff (by simp : (k : ℕ∞) ≠ ⊤)).mpr
      (chromaticNumber_le_iff_colorable.mpr (hproper H hH))

/-- A vertex-critical obstruction contains a spanning, fully critical
edge-minimal obstruction.  Intersecting a bipartizing set with the new edge
set cannot increase its size. -/
theorem exists_critical_subgraph_le_of_vertex_deletions
    {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (q m : ℕ)
    (hncol : ¬ G.Colorable q)
    (hvertex : ∀ v : V, (G.induce ({v}ᶜ : Set V)).Colorable q)
    (hbip : CanBipartizeBy G m) :
    ∃ H : SimpleGraph V, H ≤ G ∧ ¬ H.Colorable q ∧
      IsCritical H (q + 1) ∧
      ∃ m' ≤ m, CanBipartizeBy H m' := by
  classical
  let counts : Set ℕ :=
    {r | ∃ H : SimpleGraph V, H ≤ G ∧ ¬ H.Colorable q ∧ H.edgeFinset.card = r}
  have hcounts : counts.Nonempty := ⟨G.edgeFinset.card, G, le_rfl, hncol, rfl⟩
  have hminmem : sInf counts ∈ counts := Nat.sInf_mem hcounts
  obtain ⟨H, hHG, hHncol, hHcard⟩ := hminmem
  have hminimal {J : SimpleGraph V} (hJG : J ≤ G) (hJncol : ¬ J.Colorable q) :
      H.edgeFinset.card ≤ J.edgeFinset.card := by
    rw [hHcard]
    exact Nat.sInf_le ⟨J, hJG, hJncol, rfl⟩
  have hproper : ∀ K : H.Subgraph, K < ⊤ → K.coe.Colorable q := by
    intro K hK
    by_cases hspan : K.verts = Set.univ
    · have hKle : K.spanningCoe ≤ H := K.spanningCoe_le
      have hKne : K.spanningCoe ≠ H := by
        intro heq
        apply hK.ne
        apply Subgraph.verts_spanningCoe_injective
        apply Prod.ext
        · simpa [hspan]
        · simpa [heq]
      have hKlt : K.spanningCoe < H := lt_of_le_of_ne hKle hKne
      have hKcol : K.spanningCoe.Colorable q := by
        by_contra hnot
        have hcardle := hminimal (hKle.trans hHG) hnot
        have hcardlt : K.spanningCoe.edgeFinset.card < H.edgeFinset.card :=
          Finset.card_lt_card (edgeFinset_strict_mono hKlt)
        exact (Nat.not_lt_of_ge hcardle) hcardlt
      exact Colorable.of_hom K.coeEmbeddingSpanningCoe hKcol
    · obtain ⟨v, hv⟩ := (Set.ne_univ_iff_exists_notMem K.verts).mp hspan
      let φfun : K.verts → ({v}ᶜ : Set V) := fun x ↦ ⟨x.1, by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          intro hx
          apply hv
          exact hx ▸ x.property⟩
      let φ : K.coe →g G.induce ({v}ᶜ : Set V) := RelHom.mk φfun (by
        intro a b hab
        change G.Adj a.1 b.1
        exact hHG (K.adj_sub hab))
      exact Colorable.of_hom φ (hvertex v)
  have hHsucc : H.Colorable (q + 1) := by
    let v : V := Classical.choice inferInstance
    obtain ⟨C⟩ := hvertex v
    let D : V → Fin (q + 1) := fun w ↦
      if hw : w = v then ⟨q, Nat.lt_add_one q⟩
      else Fin.castSucc (C ⟨w, by simpa using hw⟩)
    refine ⟨⟨D, ?_⟩⟩
    intro a b hab
    have hGab : G.Adj a b := hHG hab
    rw [top_adj]
    by_cases ha : a = v
    · subst a
      have hb : b ≠ v := hGab.ne.symm
      simp only [D, dif_pos rfl, dif_neg hb]
      change (Fin.last q) ≠ Fin.castSucc _
      exact (Fin.castSucc_ne_last _).symm
    · by_cases hb : b = v
      · subst b
        simp only [D, dif_neg ha, dif_pos rfl]
        change Fin.castSucc _ ≠ Fin.last q
        exact Fin.castSucc_ne_last _
      · simp only [D, dif_neg ha, dif_neg hb]
        intro heq
        have hne : C ⟨a, by simpa using ha⟩ ≠ C ⟨b, by simpa using hb⟩ :=
          C.valid (induce_adj.mpr hGab)
        apply hne
        exact Fin.castSucc_injective q heq
  have hcritical : IsCritical H (q + 1) :=
    (isCritical_succ_iff H q).2 ⟨hHsucc, hHncol, hproper⟩
  obtain ⟨E, hEG, hEcard, hGbip⟩ := hbip
  let E' : Set (Sym2 V) := E ∩ H.edgeSet
  have hE'H : E' ⊆ H.edgeSet := Set.inter_subset_right
  have hE'card_le : E'.ncard ≤ m := by
    rw [← hEcard]
    exact Set.ncard_inter_le_ncard_left E H.edgeSet
  have hdel_le : H.deleteEdges E' ≤ G.deleteEdges E := by
    rw [show H.deleteEdges E' = H.deleteEdges E by
      exact (H.deleteEdges_eq_inter_edgeSet E).symm]
    exact deleteEdges_mono hHG
  have hHbip : (H.deleteEdges E').IsBipartite :=
    Colorable.mono_left hdel_le hGbip
  exact ⟨H, hHG, hHncol, hcritical, E'.ncard, hE'card_le,
    E', hE'H, rfl, hHbip⟩

/-! ## The Kempe-chain lower bound -/

theorem choose_le_card_of_color_pair_witness
    {V : Type u} [Fintype V] [DecidableEq V]
    {q : ℕ} (F : Finset (Sym2 V)) (c : V → Fin q)
    (h : ∀ p : {p : Sym2 (Fin q) // ¬ p.IsDiag},
      ∃ e : Sym2 V, e ∈ F ∧ Sym2.map c e = p.1) :
    q.choose 2 ≤ F.card := by
  classical
  choose e heF hec using h
  let g : {p : Sym2 (Fin q) // ¬ p.IsDiag} → F := fun p ↦ ⟨e p, heF p⟩
  have hg : Function.Injective g := by
    intro p p' hpp'
    apply Subtype.ext
    rw [← hec p, ← hec p']
    exact congrArg (fun x : F ↦ Sym2.map c x.1) hpp'
  rw [← Fintype.card_fin q, ← Sym2.card_subtype_not_diag]
  simpa using Fintype.card_le_of_injective g hg

theorem exists_neighbor_of_color
    {V : Type u} {G : SimpleGraph V} {q : ℕ} {v : V}
    (hnc : ¬ G.Colorable q)
    (c : (G.deleteIncidenceSet v).Coloring (Fin q)) (i : Fin q) :
    ∃ a, G.Adj v a ∧ c a = i := by
  classical
  by_contra! h
  apply hnc
  refine ⟨SimpleGraph.Coloring.mk (fun x ↦ if x = v then i else c x) ?_⟩
  intro x y hxy
  have hxy_ne : x ≠ y := hxy.ne
  by_cases hx : x = v
  · subst x
    have hy : y ≠ v := fun hyv ↦ hxy_ne hyv.symm
    simp only [ite_true, hy, ite_false]
    exact (h y hxy).symm
  · by_cases hy : y = v
    · subst y
      simp only [hx, ite_false, ite_true]
      exact h x hxy.symm
    · simp only [hx, hy, ite_false]
      exact c.valid (deleteIncidenceSet_adj.mpr ⟨hxy, hx, hy⟩)

def kempeGraph {V : Type u} (G : SimpleGraph V) (v : V)
    {q : ℕ} (c : V → Fin q) (i j : Fin q) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ≠ v ∧ y ≠ v ∧
    (c x = i ∨ c x = j) ∧ (c y = i ∨ c y = j)
  symm := ⟨by
    intro x y h
    exact ⟨h.1.symm, h.2.2.1, h.2.1, h.2.2.2.2, h.2.2.2.1⟩⟩
  loopless := ⟨by
    intro x h
    exact h.1.ne rfl⟩

@[simp] theorem kempeGraph_adj {V : Type u} {G : SimpleGraph V} {v : V}
    {q : ℕ} {c : V → Fin q} {i j : Fin q} {x y : V} :
    (kempeGraph G v c i j).Adj x y ↔
      G.Adj x y ∧ x ≠ v ∧ y ≠ v ∧
        (c x = i ∨ c x = j) ∧ (c y = i ∨ c y = j) := Iff.rfl

def inKempeSwitch {V : Type u} (G : SimpleGraph V) (v : V)
    {q : ℕ} (c : V → Fin q) (i j : Fin q) (x : V) : Prop :=
  ∃ a, G.Adj v a ∧ c a = i ∧ (kempeGraph G v c i j).Reachable a x

theorem inKempeSwitch_of_neighbor {V : Type u} {G : SimpleGraph V} {v : V}
    {q : ℕ} {c : V → Fin q} {i j : Fin q} {x : V}
    (hx : G.Adj v x) (hcx : c x = i) :
    inKempeSwitch G v c i j x :=
  ⟨x, hx, hcx, .rfl⟩

theorem inKempeSwitch_of_adj_right {V : Type u} {G : SimpleGraph V} {v : V}
    {q : ℕ} {c : V → Fin q} {i j : Fin q} {x y : V}
    (hx : inKempeSwitch G v c i j x)
    (hxy : (kempeGraph G v c i j).Adj x y) :
    inKempeSwitch G v c i j y := by
  obtain ⟨a, hva, hca, hax⟩ := hx
  exact ⟨a, hva, hca, hax.trans hxy.reachable⟩

private theorem walk_endpoint_mem_colors {V : Type u} {G : SimpleGraph V} {v : V}
    {q : ℕ} {c : V → Fin q} {i j : Fin q} {x y : V}
    (p : (kempeGraph G v c i j).Walk x y) (hx : c x = i ∨ c x = j) :
    c y = i ∨ c y = j := by
  induction p with
  | nil => exact hx
  | cons hxy p ih =>
      exact ih (kempeGraph_adj.mp hxy).2.2.2.2

theorem inKempeSwitch_color {V : Type u} {G : SimpleGraph V} {v : V}
    {q : ℕ} {c : V → Fin q} {i j : Fin q} {x : V}
    (hx : inKempeSwitch G v c i j x) : c x = i ∨ c x = j := by
  obtain ⟨a, -, hca, ⟨p⟩⟩ := hx
  exact walk_endpoint_mem_colors p (Or.inl hca)

theorem exists_kempe_neighbor_pair
    {V : Type u} {G : SimpleGraph V} {q : ℕ} {v : V}
    (hnc : ¬ G.Colorable q)
    (c : (G.deleteIncidenceSet v).Coloring (Fin q))
    (i j : Fin q) (hij : i ≠ j) :
    ∃ a b, G.Adj v a ∧ c a = i ∧ G.Adj v b ∧ c b = j ∧
      (kempeGraph G v c i j).Reachable a b := by
  classical
  by_contra hno
  have hdis : ∀ a b, G.Adj v a → c a = i → G.Adj v b → c b = j →
      ¬ (kempeGraph G v c i j).Reachable a b := by
    intro a b hva hca hvb hcb hab
    exact hno ⟨a, b, hva, hca, hvb, hcb, hab⟩
  let R : V → Prop := inKempeSwitch G v c i j
  let s' : V → Fin q := fun x ↦ if R x then Equiv.swap i j (c x) else c x
  have hR_color : ∀ {x}, R x → c x = i ∨ c x = j := by
    intro x hx
    exact inKempeSwitch_color hx
  have hR_of_adj : ∀ {x y}, R x → (kempeGraph G v c i j).Adj x y → R y := by
    intro x y hx hxy
    exact inKempeSwitch_of_adj_right hx hxy
  have hneighbor : ∀ {y}, G.Adj v y → s' y ≠ i := by
    intro y hvy
    by_cases hcyi : c y = i
    · have hRy : R y := inKempeSwitch_of_neighbor hvy hcyi
      simpa [s', hRy, hcyi] using hij.symm
    · by_cases hcyj : c y = j
      · have hnRy : ¬ R y := by
          rintro ⟨a, hva, hca, hay⟩
          exact hdis a y hva hca hvy hcyj hay
        simp [s', hnRy, hcyi]
      · have hnRy : ¬ R y := fun hRy ↦ (hR_color hRy).elim hcyi hcyj
        simp [s', hnRy, hcyi]
  have hmixed : ∀ {x y}, G.Adj x y → x ≠ v → y ≠ v →
      R x → ¬ R y → s' x ≠ s' y := by
    intro x y hxy hxv hyv hRx hnRy heq
    have hcx := hR_color hRx
    rcases hcx with hcxi | hcxj
    · have hcyj : c y = j := by
        simpa [s', hRx, hnRy, hcxi] using heq.symm
      have hK : (kempeGraph G v c i j).Adj x y :=
        kempeGraph_adj.mpr ⟨hxy, hxv, hyv, Or.inl hcxi, Or.inr hcyj⟩
      exact hnRy (hR_of_adj hRx hK)
    · have hcyi : c y = i := by
        simpa [s', hRx, hnRy, hcxj] using heq.symm
      have hK : (kempeGraph G v c i j).Adj x y :=
        kempeGraph_adj.mpr ⟨hxy, hxv, hyv, Or.inr hcxj, Or.inl hcyi⟩
      exact hnRy (hR_of_adj hRx hK)
  apply hnc
  refine ⟨SimpleGraph.Coloring.mk (fun x ↦ if x = v then i else s' x) ?_⟩
  intro x y hxy
  have hxy_ne : x ≠ y := hxy.ne
  by_cases hxv : x = v
  · subst x
    have hyv : y ≠ v := fun hy ↦ hxy_ne hy.symm
    simp only [ite_true, hyv, ite_false]
    exact (hneighbor hxy).symm
  · by_cases hyv : y = v
    · subst y
      simp only [hxv, ite_false, ite_true]
      exact hneighbor hxy.symm
    · simp only [hxv, hyv, ite_false]
      have hcxy : c x ≠ c y :=
        c.valid (deleteIncidenceSet_adj.mpr ⟨hxy, hxv, hyv⟩)
      by_cases hRx : R x <;> by_cases hRy : R y
      · simpa [s', hRx, hRy] using (Equiv.swap i j).injective.ne hcxy
      · exact hmixed hxy hxv hyv hRx hRy
      · exact (hmixed hxy.symm hyv hxv hRy hRx).symm
      · simpa [s', hRx, hRy] using hcxy

theorem kempe_edge_color_pair
    {V : Type u} {G : SimpleGraph V} {q : ℕ} {v : V}
    (c : (G.deleteIncidenceSet v).Coloring (Fin q))
    (i j : Fin q) (hij : i ≠ j) {e : Sym2 V}
    (he : e ∈ (kempeGraph G v c i j).edgeSet) :
    Sym2.map c e = s(i, j) := by
  induction e using Sym2.ind with
  | _ x y =>
      rw [Sym2.map_mk]
      have hxy : (kempeGraph G v c i j).Adj x y := by
        simpa only [mem_edgeSet] using he
      have hcxy : c x ≠ c y :=
        c.valid (deleteIncidenceSet_adj.mpr ⟨hxy.1, hxy.2.1, hxy.2.2.1⟩)
      rcases hxy.2.2.2.1 with hxi | hxj <;>
        rcases hxy.2.2.2.2 with hyi | hyj
      · exact (hcxy (hxi.trans hyi.symm)).elim
      · simpa [hxi, hyj]
      · simpa [hxj, hyi]
      · exact (hcxy (hxj.trans hyj.symm)).elim

private def kempe_bool_coloring
    {V : Type u} {G : SimpleGraph V} {q : ℕ} {v : V}
    (c : (G.deleteIncidenceSet v).Coloring (Fin q))
    (i j : Fin q) (hij : i ≠ j) :
    (kempeGraph G v c i j).Coloring Bool := by
  refine SimpleGraph.Coloring.mk (fun x ↦ decide (c x = i)) ?_
  intro x y hxy
  simp only [ne_eq, decide_eq_decide]
  have hcxy : c x ≠ c y :=
    c.valid (deleteIncidenceSet_adj.mpr ⟨hxy.1, hxy.2.1, hxy.2.2.1⟩)
  rcases hxy.2.2.2.1 with hxi | hxj <;>
    rcases hxy.2.2.2.2 with hyi | hyj
  · simp_all
  · simpa [hxi, hyj] using hij.symm
  · simp_all
  · simp_all

theorem exists_exceptional_edge_on_kempe_walk
    {V : Type u} [DecidableEq V] {G : SimpleGraph V} {q : ℕ} {v : V}
    (F : Finset (Sym2 V))
    (hincident : ∀ e ∈ F, v ∉ e)
    (bcol : (G.deleteEdges (F : Set (Sym2 V))).Coloring Bool)
    (c : (G.deleteIncidenceSet v).Coloring (Fin q))
    (i j : Fin q) (hij : i ≠ j)
    {a b : V} (hva : G.Adj v a) (hca : c a = i)
    (hvb : G.Adj v b) (hcb : c b = j)
    (hab : (kempeGraph G v c i j).Reachable a b) :
    ∃ e, e ∈ F ∧ Sym2.map c e = s(i, j) := by
  classical
  obtain ⟨p⟩ := hab
  let K := kempeGraph G v c i j
  have hKG : K ≤ G := fun _ _ h ↦ h.1
  let pG : G.Walk a b := p.transfer G fun e he ↦
    edgeSet_mono hKG (p.edges_subset_edgeSet he)
  have hpG_edges : pG.edges = p.edges := by simp [pG]
  have hpG_length : pG.length = p.length := by simp [pG]
  have hpOdd : Odd p.length := by
    let kc := kempe_bool_coloring c i j hij
    rw [kc.odd_length_iff_not_congr p]
    change (¬ decide (c a = i) = true) ↔ decide (c b = i) = true
    simpa [hca, hcb] using hij.symm
  by_contra hnone
  have hp_avoids : ∀ e, e ∈ pG.edges → e ∉ (F : Set (Sym2 V)) := by
    intro e hep heF
    apply hnone
    refine ⟨e, heF, kempe_edge_color_pair c i j hij ?_⟩
    exact p.edges_subset_edgeSet (hpG_edges ▸ hep)
  let pH := pG.toDeleteEdges (F : Set (Sym2 V)) hp_avoids
  have hpH_length : pH.length = p.length := by
    simp [pH, hpG_length]
  have hva_notF : s(v, a) ∉ F := fun h ↦ hincident _ h (by simp)
  have hvb_notF : s(v, b) ∉ F := fun h ↦ hincident _ h (by simp)
  have hvaH : (G.deleteEdges (F : Set (Sym2 V))).Adj v a :=
    deleteEdges_adj.mpr ⟨hva, by simpa using hva_notF⟩
  have hvbH : (G.deleteEdges (F : Set (Sym2 V))).Adj v b :=
    deleteEdges_adj.mpr ⟨hvb, by simpa using hvb_notF⟩
  have hba : bcol v ≠ bcol a := bcol.valid hvaH
  have hbb : bcol v ≠ bcol b := bcol.valid hvbH
  have habcol : bcol a ↔ bcol b := by
    cases hv : bcol v <;> cases ha : bcol a <;> cases hb : bcol b <;> simp_all
  have hpEven : Even pH.length :=
    (bcol.even_length_iff_congr pH).mpr habcol
  exact (Nat.not_even_iff_odd.mpr (hpH_length.symm ▸ hpOdd)) hpEven

theorem kempe_lower_bound
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {q : ℕ} {v : V}
    (F : Finset (Sym2 V))
    (hincident : ∀ e ∈ F, v ∉ e)
    (hbip : (G.deleteEdges (F : Set (Sym2 V))).Colorable 2)
    (hnc : ¬ G.Colorable q)
    (c : (G.deleteIncidenceSet v).Coloring (Fin q)) :
    q.choose 2 ≤ F.card := by
  classical
  let bcol : (G.deleteEdges (F : Set (Sym2 V))).Coloring Bool :=
    recolorOfEquiv _ finTwoEquiv hbip.some
  apply choose_le_card_of_color_pair_witness F c
  rintro ⟨p, hp⟩
  induction p using Sym2.ind with
  | _ i j =>
      have hij : i ≠ j := by
        intro h
        subst j
        exact hp (by simp)
      obtain ⟨a, b, hva, hca, hvb, hcb, hab⟩ :=
        exists_kempe_neighbor_pair hnc c i j hij
      obtain ⟨e, heF, hec⟩ :=
        exists_exceptional_edge_on_kempe_walk F hincident bcol c i j hij
          hva hca hvb hcb hab
      exact ⟨e, heF, hec⟩

theorem exists_vertex_not_incident
    {V : Type u} [Fintype V] [DecidableEq V]
    (F : Finset (Sym2 V)) (hcard : 2 * F.card < Fintype.card V) :
    ∃ v : V, ∀ e ∈ F, v ∉ e := by
  classical
  let S : Finset V := F.biUnion Sym2.toFinset
  have h_each : ∀ e ∈ F, e.toFinset.card ≤ 2 := by
    intro e _
    rw [Sym2.card_toFinset]
    split <;> omega
  have hSle : S.card ≤ F.card * 2 :=
    Finset.card_biUnion_le_card_mul F Sym2.toFinset 2 h_each
  have hSlt : S.card < Fintype.card V := by omega
  have hex : ∃ v : V, v ∉ S := by
    by_contra! hall
    have hSuniv : S = Finset.univ := Finset.eq_univ_of_forall hall
    rw [hSuniv, Finset.card_univ] at hSlt
    exact (lt_irrefl _ hSlt)
  obtain ⟨v, hv⟩ := hex
  refine ⟨v, fun e heF hve ↦ hv ?_⟩
  exact Finset.mem_biUnion.mpr ⟨e, heF, Sym2.mem_toFinset.mpr hve⟩

theorem kempe_lower_bound_of_many_vertices
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {q : ℕ}
    (F : Finset (Sym2 V))
    (hcard : 2 * F.card < Fintype.card V)
    (hbip : (G.deleteEdges (F : Set (Sym2 V))).Colorable 2)
    (hnc : ¬ G.Colorable q)
    (hvertex : ∀ v : V, (G.deleteIncidenceSet v).Colorable q) :
    q.choose 2 ≤ F.card := by
  classical
  obtain ⟨v, hv⟩ := exists_vertex_not_incident F hcard
  exact kempe_lower_bound F hv hbip hnc (hvertex v).some

theorem deleteIncidenceSet_colorable_of_proper_subgraphs
    {V : Type u} {G : SimpleGraph V} {q : ℕ} (hq : 0 < q)
    (hproper : ∀ H : G.Subgraph, H < ⊤ → H.coe.Colorable q) (v : V) :
    (G.deleteIncidenceSet v).Colorable q := by
  classical
  let H : G.Subgraph := (⊤ : G.Subgraph).deleteVerts {v}
  have hHlt : H < ⊤ := by
    refine lt_of_le_of_ne le_top ?_
    intro heq
    have hvtop : v ∈ (⊤ : G.Subgraph).verts := by simp
    have hvH : v ∈ H.verts := heq ▸ hvtop
    simpa [H] using hvH
  obtain ⟨c⟩ := hproper H hHlt
  let zero : Fin q := ⟨0, hq⟩
  let C : V → Fin q := fun x ↦ if hx : x = v then zero else
    c ⟨x, by simp [H, hx]⟩
  refine ⟨SimpleGraph.Coloring.mk C ?_⟩
  intro x y hxy
  have hxv : x ≠ v := (deleteIncidenceSet_adj.mp hxy).2.1
  have hyv : y ≠ v := (deleteIncidenceSet_adj.mp hxy).2.2
  simp only [C, dif_neg hxv, dif_neg hyv]
  apply c.valid
  exact Subgraph.deleteVerts_adj.mpr
    ⟨by simp, hxv, by simp, hyv, (deleteIncidenceSet_adj.mp hxy).1⟩

/-- The uniform half of Rödl--Tuza: above the explicit vertex threshold,
every critical graph needs at least one deleted edge for every unordered pair
of old colors. -/
theorem critical_deletionNumber_lower
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {q : ℕ} (hq : 3 ≤ q)
    (hsize : 2 * q.choose 2 - 1 ≤ Fintype.card V)
    (hcrit : IsCritical G (q + 1)) :
    q.choose 2 ≤ deletionNumber G := by
  classical
  apply le_deletionNumber_of_forall
  intro m hm
  obtain ⟨E, hEG, hEcard, hEbip⟩ := hm
  by_contra hnot
  have hmB : m < q.choose 2 := Nat.lt_of_not_ge hnot
  have hBpos : 0 < q.choose 2 := Nat.choose_pos (by omega)
  let F : Finset (Sym2 V) := E.toFinset
  have hFcoe : (F : Set (Sym2 V)) = E := by simp [F]
  have hFcard : F.card = m :=
    calc
      F.card = (F : Set (Sym2 V)).ncard := (Set.ncard_coe_finset F).symm
      _ = E.ncard := congrArg Set.ncard hFcoe
      _ = m := hEcard
  have hlarge : 2 * F.card < Fintype.card V := by
    rw [hFcard]
    omega
  obtain ⟨-, hncol, hproper⟩ := (isCritical_succ_iff G q).mp hcrit
  have hvertex : ∀ v : V, (G.deleteIncidenceSet v).Colorable q :=
    deleteIncidenceSet_colorable_of_proper_subgraphs (by omega) hproper
  have hbound := kempe_lower_bound_of_many_vertices F hlarge
    (hFcoe ▸ hEbip) hncol hvertex
  omega

/-! ## The odd-order obstruction -/

/-- Vertices of the odd-order construction.  The `c` index `j` represents
the color `j + 1`. -/
inductive OddVertex (q L : ℕ)
  | p : Fin q → OddVertex q L
  | c : Fin (q - 1) → OddVertex q L
  | x : Fin (L + 1) → OddVertex q L
  deriving DecidableEq, Fintype

private def oddAdj (q L : ℕ) : OddVertex q L → OddVertex q L → Prop
  | .p i, .p j => i ≠ j
  | .p i, .c j => i.val ≠ j.val + 1
  | .c j, .p i => i.val ≠ j.val + 1
  | .c _, .c _ => False
  | .p i, .x s => (Odd s.val ∧ 2 ≤ i.val) ∨ (s.val = L ∧ i.val = 1)
  | .x s, .p i => (Odd s.val ∧ 2 ≤ i.val) ∨ (s.val = L ∧ i.val = 1)
  | .c j, .x s => (Even s.val ∧ 1 ≤ j.val) ∨ (s.val = 0 ∧ j.val = 0)
  | .x s, .c j => (Even s.val ∧ 1 ≤ j.val) ∨ (s.val = 0 ∧ j.val = 0)
  | .x s, .x t => s.val + 1 = t.val ∨ t.val + 1 = s.val

private lemma oddAdj_symm (q L : ℕ) : Std.Symm (oddAdj q L) := by
  constructor
  intro v w
  cases v <;> cases w <;> simp only [oddAdj, ne_eq] <;> aesop

private lemma oddAdj_loopless (q L : ℕ) : Std.Irrefl (oddAdj q L) := by
  constructor
  intro v
  cases v <;> simp [oddAdj]

/-- The explicit odd-order graph from the proof. -/
def oddGraph (q L : ℕ) : SimpleGraph (OddVertex q L) where
  Adj := oddAdj q L
  symm := oddAdj_symm q L
  loopless := oddAdj_loopless q L

@[simp] lemma oddGraph_adj_p_p {q L : ℕ} {i j : Fin q} :
    (oddGraph q L).Adj (.p i) (.p j) ↔ i ≠ j := Iff.rfl

@[simp] lemma oddGraph_adj_p_c {q L : ℕ} {i : Fin q} {j : Fin (q - 1)} :
    (oddGraph q L).Adj (.p i) (.c j) ↔ i.val ≠ j.val + 1 := Iff.rfl

@[simp] lemma oddGraph_adj_c_p {q L : ℕ} {i : Fin q} {j : Fin (q - 1)} :
    (oddGraph q L).Adj (.c j) (.p i) ↔ i.val ≠ j.val + 1 := Iff.rfl

@[simp] lemma oddGraph_adj_c_c {q L : ℕ} {i j : Fin (q - 1)} :
    ¬(oddGraph q L).Adj (.c i) (.c j) := by simp [oddGraph, oddAdj]

@[simp] lemma oddGraph_adj_p_x {q L : ℕ} {i : Fin q} {s : Fin (L + 1)} :
    (oddGraph q L).Adj (.p i) (.x s) ↔
      (Odd s.val ∧ 2 ≤ i.val) ∨ (s.val = L ∧ i.val = 1) := Iff.rfl

@[simp] lemma oddGraph_adj_x_p {q L : ℕ} {i : Fin q} {s : Fin (L + 1)} :
    (oddGraph q L).Adj (.x s) (.p i) ↔
      (Odd s.val ∧ 2 ≤ i.val) ∨ (s.val = L ∧ i.val = 1) := Iff.rfl

@[simp] lemma oddGraph_adj_c_x {q L : ℕ} {j : Fin (q - 1)} {s : Fin (L + 1)} :
    (oddGraph q L).Adj (.c j) (.x s) ↔
      (Even s.val ∧ 1 ≤ j.val) ∨ (s.val = 0 ∧ j.val = 0) := Iff.rfl

@[simp] lemma oddGraph_adj_x_c {q L : ℕ} {j : Fin (q - 1)} {s : Fin (L + 1)} :
    (oddGraph q L).Adj (.x s) (.c j) ↔
      (Even s.val ∧ 1 ≤ j.val) ∨ (s.val = 0 ∧ j.val = 0) := Iff.rfl

@[simp] lemma oddGraph_adj_x_x {q L : ℕ} {s t : Fin (L + 1)} :
    (oddGraph q L).Adj (.x s) (.x t) ↔
      s.val + 1 = t.val ∨ t.val + 1 = s.val := Iff.rfl

private def oddPEmbedding (q L : ℕ) : Fin q ↪ OddVertex q L where
  toFun := OddVertex.p
  inj' := by intro i j h; cases h; rfl

private def oddExceptionalFinset (q L : ℕ) :
    Finset (Sym2 (OddVertex q L)) :=
  (⊤ : SimpleGraph (Fin q)).edgeFinset.map (oddPEmbedding q L).sym2Map

/-- The `q`-clique whose deletion makes the odd construction bipartite. -/
def oddExceptional (q L : ℕ) : Set (Sym2 (OddVertex q L)) :=
  oddExceptionalFinset q L

lemma oddExceptional_ncard (q L : ℕ) :
    (oddExceptional q L).ncard = q.choose 2 := by
  classical
  rw [oddExceptional, Set.ncard_coe_finset, oddExceptionalFinset,
    Finset.card_map]
  simpa using (card_edgeFinset_top_eq_card_choose_two (V := Fin q))

private lemma oddExceptional_pair {q L : ℕ} (i j : Fin q) (hij : i ≠ j) :
    s(OddVertex.p i, OddVertex.p j) ∈ oddExceptional q L := by
  classical
  apply Finset.mem_map.2
  refine ⟨s(i, j), ?_, ?_⟩
  · simpa using hij
  · apply Sym2.eq_iff.2
    exact Or.inl ⟨rfl, rfl⟩

private def oddBipColor {q L : ℕ} : OddVertex q L → Fin 2
  | .p _ => 0
  | .c _ => 1
  | .x s => ⟨s.val % 2, Nat.mod_lt _ (by omega)⟩

private lemma oddBipColor_x_zero {q L : ℕ} {s : Fin (L + 1)}
    (hs : Even s.val) : oddBipColor (q := q) (.x s) = 0 := by
  ext
  simp [oddBipColor, Nat.even_iff] at hs ⊢
  omega

private lemma oddBipColor_x_one {q L : ℕ} {s : Fin (L + 1)}
    (hs : Odd s.val) : oddBipColor (q := q) (.x s) = 1 := by
  ext
  simpa [oddBipColor, Nat.odd_iff] using hs

lemma odd_delete_exceptional_isBipartite {q L : ℕ} (hL : Odd L) :
    ((oddGraph q L).deleteEdges (oddExceptional q L)).IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk oddBipColor ?_⟩
  intro u v huv
  rw [deleteEdges_adj] at huv
  rcases huv with ⟨huv, hnot⟩
  cases u <;> cases v
  case p.p i j =>
    exact fun h ↦ hnot (oddExceptional_pair i j (oddGraph_adj_p_p.mp huv))
  case p.c => simp [oddBipColor]
  case c.p => simp [oddBipColor]
  case c.c => simp at huv
  case p.x i s =>
    rcases oddGraph_adj_p_x.mp huv with h | h
    · rw [oddBipColor_x_one h.1]
      simp [oddBipColor]
    · have hs : Odd s.val := by simpa [h.1] using hL
      rw [oddBipColor_x_one hs]
      simp [oddBipColor]
  case x.p s i =>
    rcases oddGraph_adj_x_p.mp huv with h | h
    · rw [oddBipColor_x_one h.1]
      simp [oddBipColor]
    · have hs : Odd s.val := by simpa [h.1] using hL
      rw [oddBipColor_x_one hs]
      simp [oddBipColor]
  case c.x j s =>
    rcases oddGraph_adj_c_x.mp huv with h | h
    · rw [oddBipColor_x_zero h.1]
      simp [oddBipColor]
    · rw [oddBipColor_x_zero (h.1 ▸ ⟨0, rfl⟩)]
      simp [oddBipColor]
  case x.c s j =>
    rcases oddGraph_adj_x_c.mp huv with h | h
    · rw [oddBipColor_x_zero h.1]
      simp [oddBipColor]
    · rw [oddBipColor_x_zero (h.1 ▸ ⟨0, rfl⟩)]
      simp [oddBipColor]
  case x.x s t =>
    intro heq
    have heq' := congrArg Fin.val heq
    simp only [oddBipColor] at heq'
    rcases oddGraph_adj_x_x.mp huv with h | h <;> omega

lemma oddExceptional_subset_edgeSet (q L : ℕ) :
    oddExceptional q L ⊆ (oddGraph q L).edgeSet := by
  classical
  intro e he
  change e ∈ oddExceptionalFinset q L at he
  obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_map.mp he
  induction e₀ using Sym2.ind with
  | _ i j =>
      change s(OddVertex.p i, OddVertex.p j) ∈ (oddGraph q L).edgeSet
      rw [mem_edgeSet]
      exact oddGraph_adj_p_p.mpr (by simpa using he₀)

lemma odd_canBipartizeBy {q L : ℕ} (hL : Odd L) :
    CanBipartizeBy (oddGraph q L) (q.choose 2) :=
  ⟨oddExceptional q L, oddExceptional_subset_edgeSet q L,
    oddExceptional_ncard q L, odd_delete_exceptional_isBipartite hL⟩

private def oddCIndex {q : ℕ} (i : Fin (q - 1)) : Fin q :=
  ⟨i.val + 1, by omega⟩

private def oddPredIndex {q : ℕ} (j : Fin q) (hj : 1 ≤ j.val) : Fin (q - 1) :=
  ⟨j.val - 1, by omega⟩

@[simp] private lemma oddCIndex_predIndex {q : ℕ} (j : Fin q)
    (hj : 1 ≤ j.val) : oddCIndex (oddPredIndex j hj) = j := by
  ext
  simp [oddCIndex, oddPredIndex]
  omega

private def oddQzero {q : ℕ} (hq : 1 ≤ q) : Fin q := ⟨0, by omega⟩
private def oddQone {q : ℕ} (hq : 2 ≤ q) : Fin q := ⟨1, by omega⟩

private lemma odd_adj_c_p {q L : ℕ} {i : Fin (q - 1)} {j : Fin q}
    (hij : j ≠ oddCIndex i) :
    (oddGraph q L).Adj (.c i) (.p j) := by
  rw [oddGraph_adj_c_p]
  intro h
  apply hij
  apply Fin.ext
  simpa [oddCIndex] using h

private lemma odd_adj_x_p_of_odd {q L : ℕ} {s : Fin (L + 1)} {j : Fin q}
    (hs : Odd s.val) (hj : 2 ≤ j.val) :
    (oddGraph q L).Adj (.x s) (.p j) :=
  oddGraph_adj_x_p.mpr (Or.inl ⟨hs, hj⟩)

private lemma odd_adj_x_c_of_even {q L : ℕ} {s : Fin (L + 1)}
    {j : Fin (q - 1)} (hs : Even s.val) (hj : j.val ≠ 0) :
    (oddGraph q L).Adj (.x s) (.c j) :=
  oddGraph_adj_x_c.mpr (Or.inl ⟨hs, by omega⟩)

private lemma odd_adj_x_succ {q L : ℕ} (s : ℕ) (hs : s < L) :
    (oddGraph q L).Adj (.x ⟨s, by omega⟩) (.x ⟨s + 1, by omega⟩) :=
  oddGraph_adj_x_x.mpr (Or.inl rfl)

private lemma odd_pColor_injective {q L : ℕ}
    (C : (oddGraph q L).Coloring (Fin q)) :
    Function.Injective (fun i : Fin q => C (.p i)) := by
  exact C.injective_comp_of_pairwise_adj OddVertex.p
    (fun _ _ hij => oddGraph_adj_p_p.mpr hij)

private lemma odd_pColor_surjective {q L : ℕ}
    (C : (oddGraph q L).Coloring (Fin q)) :
    Function.Surjective (fun i : Fin q => C (.p i)) :=
  Finite.injective_iff_surjective.mp (odd_pColor_injective C)

private lemma odd_color_c_eq {q L : ℕ}
    (C : (oddGraph q L).Coloring (Fin q)) (i : Fin (q - 1)) :
    C (.c i) = C (.p (oddCIndex i)) := by
  obtain ⟨j, hj⟩ := odd_pColor_surjective C (C (.c i))
  by_cases hji : j = oddCIndex i
  · simpa [hji] using hj.symm
  · exact False.elim (C.valid (odd_adj_c_p hji) hj.symm)

private lemma odd_color_x_two_options {q L : ℕ} (hq : 3 ≤ q)
    (C : (oddGraph q L).Coloring (Fin q)) (s : Fin (L + 1)) :
    C (.x s) = C (.p (oddQzero (by omega))) ∨
      C (.x s) = C (.p (oddQone (by omega))) := by
  obtain ⟨j, hj⟩ := odd_pColor_surjective C (C (.x s))
  have hjlt : j.val < 2 := by
    by_contra hn
    have hj2 : 2 ≤ j.val := by omega
    rcases Nat.even_or_odd s.val with hs | hs
    · let i : Fin (q - 1) := oddPredIndex j (by omega)
      have hi0 : i.val ≠ 0 := by simp [i, oddPredIndex]; omega
      have hadj := odd_adj_x_c_of_even (q := q) hs hi0
      have hc := odd_color_c_eq C i
      exact C.valid hadj (hc.trans (by simpa [i] using hj)).symm
    · exact C.valid (odd_adj_x_p_of_odd hs hj2) hj.symm
  have hz : j = oddQzero (by omega) ∨ j = oddQone (by omega) := by
    by_cases h : j.val = 0
    · left; ext; simpa [oddQzero]
    · right; ext; simp [oddQone]; omega
  rcases hz with hz | ho
  · left
    rw [← hz]
    exact hj.symm
  · right
    rw [← ho]
    exact hj.symm

private def oddXAt {L : ℕ} (m : ℕ) (hm : m ≤ L) : Fin (L + 1) :=
  ⟨m, by omega⟩

private lemma odd_adj_xzero_czero {q L : ℕ} (hq : 3 ≤ q) :
    (oddGraph q L).Adj (.x (oddXAt 0 (by omega)))
      (.c ⟨0, by omega⟩) :=
  oddGraph_adj_x_c.mpr (Or.inr ⟨rfl, rfl⟩)

private lemma odd_adj_xlast_pone {q L : ℕ} (hq : 3 ≤ q) :
    (oddGraph q L).Adj (.x (oddXAt L (by omega)))
      (.p (oddQone (by omega))) :=
  oddGraph_adj_x_p.mpr (Or.inr ⟨rfl, rfl⟩)

private lemma odd_color_xzero_eq {q L : ℕ} (hq : 3 ≤ q)
    (C : (oddGraph q L).Coloring (Fin q)) :
    C (.x (oddXAt 0 (by omega))) = C (.p (oddQzero (by omega))) := by
  rcases odd_color_x_two_options hq C (oddXAt 0 (by omega)) with h | h
  · exact h
  · have hc := odd_color_c_eq C (⟨0, by omega⟩ : Fin (q - 1))
    have hci : oddCIndex (⟨0, by omega⟩ : Fin (q - 1)) =
        oddQone (by omega) := by ext; rfl
    exact False.elim
      (C.valid (odd_adj_xzero_czero hq) (h.trans (by simpa [hci] using hc.symm)))

private lemma odd_color_xlast_eq {q L : ℕ} (hq : 3 ≤ q)
    (C : (oddGraph q L).Coloring (Fin q)) :
    C (.x (oddXAt L (by omega))) = C (.p (oddQzero (by omega))) := by
  rcases odd_color_x_two_options hq C (oddXAt L (by omega)) with h | h
  · exact h
  · exact False.elim (C.valid (odd_adj_xlast_pone hq) h)

private lemma odd_path_colors {q L : ℕ} (hq : 3 ≤ q)
    (C : (oddGraph q L).Coloring (Fin q)) (m : ℕ) (hm : m ≤ L) :
    (Even m → C (.x (oddXAt m hm)) = C (.p (oddQzero (by omega)))) ∧
    (Odd m → C (.x (oddXAt m hm)) = C (.p (oddQone (by omega)))) := by
  induction m with
  | zero =>
      constructor
      · intro
        simpa only [oddXAt] using odd_color_xzero_eq hq C
      · rintro ⟨a, ha⟩
        omega
  | succ m ih =>
      have hmL : m < L := by omega
      have ih := ih (by omega)
      have hadj := C.valid (odd_adj_x_succ (q := q) m hmL)
      have hop := odd_color_x_two_options hq C (oddXAt (m + 1) hm)
      rcases Nat.even_or_odd m with he | ho
      · have hold := ih.1 he
        have hnew := hop.resolve_left (fun hn => hadj (hold.trans hn.symm))
        constructor
        · rintro ⟨a, ha⟩
          rcases he with ⟨b, hb⟩
          omega
        · intro
          simpa only [Nat.succ_eq_add_one, oddXAt] using hnew
      · have hold := ih.2 ho
        have hnew := hop.resolve_right (fun hn => hadj (hold.trans hn.symm))
        constructor
        · intro
          simpa only [Nat.succ_eq_add_one, oddXAt] using hnew
        · rintro ⟨a, ha⟩
          rcases ho with ⟨b, hb⟩
          omega

lemma oddGraph_not_colorable {q L : ℕ} (hq : 3 ≤ q) (hL : Odd L) :
    ¬(oddGraph q L).Colorable q := by
  rintro ⟨C⟩
  have hpath := (odd_path_colors hq C L (by omega)).2 hL
  have hend := odd_color_xlast_eq hq C
  have h01 : oddQzero (q := q) (by omega) ≠ oddQone (q := q) (by omega) := by
    intro h
    have h' := congrArg Fin.val h
    simp [oddQzero, oddQone] at h'
  exact C.valid (oddGraph_adj_p_p.mpr h01) (hend.symm.trans hpath)

/- The oriented half of `oddAdj`, used to reduce the explicit deletion
coloring checks to nine constructor pairs. -/
private def oddRel (q L : ℕ) : OddVertex q L → OddVertex q L → Prop
  | .p _, .p _ => True
  | .c i, .p j => j.val ≠ i.val + 1
  | .x s, .c j => (Even s.val ∧ j.val ≠ 0) ∨ (s.val = 0 ∧ j.val = 0)
  | .x s, .p j => (Odd s.val ∧ 2 ≤ j.val) ∨ (s.val = L ∧ j.val = 1)
  | .x s, .x t => t.val = s.val + 1
  | _, _ => False

private lemma oddGraph_adj_iff_rel {q L : ℕ} (u v : OddVertex q L) :
    (oddGraph q L).Adj u v ↔ u ≠ v ∧ (oddRel q L u v ∨ oddRel q L v u) := by
  cases u <;> cases v <;>
    simp only [oddGraph_adj_p_p, oddGraph_adj_p_c, oddGraph_adj_c_p,
      oddGraph_adj_c_c, oddGraph_adj_p_x, oddGraph_adj_x_p,
      oddGraph_adj_c_x, oddGraph_adj_x_c, oddGraph_adj_x_x,
      oddRel, ne_eq] <;> aesop <;> omega

namespace OddDelete

open OddVertex

private abbrev graph := oddGraph
private abbrev rel := oddRel

private lemma graph_adj {q L : ℕ} (u v : OddVertex q L) :
    (graph q L).Adj u v ↔ u ≠ v ∧ (rel q L u v ∨ rel q L v u) :=
  oddGraph_adj_iff_rel u v

private lemma odd_of_rel_x_p {q L : ℕ} (hL : Odd L)
    {s : Fin (L + 1)} {j : Fin q} (h : rel q L (x s) (p j)) : Odd s.val := by
  rcases h with h | h
  · exact h.1
  · simpa [h.1] using hL

private lemma even_of_rel_x_c {q L : ℕ} {s : Fin (L + 1)}
    {j : Fin (q - 1)} (h : rel q L (x s) (c j)) : Even s.val := by
  rcases h with h | h
  · exact h.1
  · rw [h.1]
    exact ⟨0, rfl⟩

private def otherColorNat {q : ℕ} (i : Fin q) : ℕ :=
  if i.val = 0 then 1 else 0

private lemma otherColorNat_lt {q : ℕ} (hq : 3 ≤ q) (i : Fin q) :
    otherColorNat i < q := by
  unfold otherColorNat
  split <;> omega

private lemma otherColorNat_ne {q : ℕ} (i : Fin q) : otherColorNat i ≠ i.val := by
  unfold otherColorNat
  split <;> omega

private def deletePColorNat {q L : ℕ} (i : Fin q) : OddVertex q L → ℕ
  | p j => j.val
  | c _ => i.val
  | x s => if Even s.val then otherColorNat i else i.val

private def deletePColor {q L : ℕ} (hq : 3 ≤ q) (i : Fin q)
    (v : OddVertex q L) : Fin q :=
  ⟨deletePColorNat i v, by
    cases v with
    | p j => exact j.isLt
    | c => exact i.isLt
    | x s =>
        simp only [deletePColorNat]
        split <;> simp_all [otherColorNat_lt hq i]⟩

private lemma deletePColorNat_ne_of_rel {q L : ℕ} (hL : Odd L)
    (i : Fin q) {u v : OddVertex q L}
    (hne : u ≠ v) (huv : rel q L u v) (hu : u ≠ p i) (hv : v ≠ p i) :
    deletePColorNat i u ≠ deletePColorNat i v := by
  cases u <;> cases v
  case p.p j k =>
    simp only [deletePColorNat]
    intro hjk
    apply hne
    simp [Fin.ext hjk]
  case c.p j k =>
    simp only [deletePColorNat]
    intro hik
    apply hv
    simp only [OddVertex.p.injEq]
    exact Fin.ext hik.symm
  case x.p s j =>
    simp only [deletePColorNat]
    have hs : Odd s.val := odd_of_rel_x_p hL huv
    have hneven : ¬ Even s.val := Nat.not_even_iff_odd.mpr hs
    simp only [if_neg hneven]
    intro hij
    apply hv
    simp only [OddVertex.p.injEq]
    exact Fin.ext hij.symm
  case x.c s j =>
    simp only [deletePColorNat]
    rw [if_pos (even_of_rel_x_c huv)]
    exact otherColorNat_ne i
  case x.x s t =>
    simp only [deletePColorNat, rel, oddRel] at huv ⊢
    have hpar : Even s.val ↔ ¬ Even t.val := by
      simp [Nat.even_iff]
      omega
    by_cases hs : Even s.val
    · rw [if_pos hs, if_neg (hpar.mp hs)]
      exact otherColorNat_ne i
    · have ht : Even t.val := by
        by_contra hnt
        exact hs (hpar.mpr hnt)
      rw [if_neg hs, if_pos ht]
      exact (otherColorNat_ne i).symm
  all_goals simp [rel, oddRel] at huv

private lemma deletePColor_valid {q L : ℕ} (hq : 3 ≤ q) (hL : Odd L)
    (i : Fin q) {u v : OddVertex q L}
    (huv : ((graph q L).deleteIncidenceSet (p i)).Adj u v) :
    deletePColor hq i u ≠ deletePColor hq i v := by
  rw [deleteIncidenceSet_adj, graph_adj] at huv
  rcases huv with ⟨⟨hne, huv | huv⟩, hu, hv⟩
  · exact Fin.ne_of_val_ne (deletePColorNat_ne_of_rel hL i hne huv hu hv)
  · exact Fin.ne_of_val_ne
      (deletePColorNat_ne_of_rel hL i hne.symm huv hv hu).symm

private lemma delete_p_colorable {q L : ℕ} (hq : 3 ≤ q) (hL : Odd L)
    (i : Fin q) : ((graph q L).deleteIncidenceSet (p i)).Colorable q :=
  ⟨SimpleGraph.Coloring.mk (deletePColor hq i) (deletePColor_valid hq hL i)⟩

private def deleteCColorNat {q L : ℕ} (i : Fin (q - 1)) : OddVertex q L → ℕ
  | p j => j.val
  | c j => j.val + 1
  | x s => if Even s.val then i.val + 1 else 0

private def deleteCColor {q L : ℕ} (hq : 3 ≤ q) (i : Fin (q - 1))
    (v : OddVertex q L) : Fin q :=
  ⟨deleteCColorNat i v, by
    cases v with
    | p j => exact j.isLt
    | c j => dsimp [deleteCColorNat]; omega
    | x s =>
        simp only [deleteCColorNat]
        split <;> omega⟩

private lemma deleteCColorNat_ne_of_rel {q L : ℕ} (hL : Odd L)
    (i : Fin (q - 1)) {u v : OddVertex q L}
    (hne : u ≠ v) (huv : rel q L u v) (hu : u ≠ c i) (hv : v ≠ c i) :
    deleteCColorNat i u ≠ deleteCColorNat i v := by
  cases u <;> cases v
  case p.p j k =>
    simp only [deleteCColorNat]
    intro hjk
    apply hne
    simp [Fin.ext hjk]
  case c.p j k =>
    simp only [deleteCColorNat, rel, oddRel] at huv
    exact huv.symm
  case x.p s j =>
    simp only [deleteCColorNat]
    have hs : Odd s.val := odd_of_rel_x_p hL huv
    rw [if_neg (Nat.not_even_iff_odd.mpr hs)]
    simp only [rel, oddRel] at huv
    omega
  case x.c s j =>
    simp only [deleteCColorNat]
    rw [if_pos (even_of_rel_x_c huv)]
    intro hij
    apply hv
    simp only [OddVertex.c.injEq]
    apply Fin.ext
    omega
  case x.x s t =>
    simp only [deleteCColorNat, rel, oddRel] at huv ⊢
    have hpar : Even s.val ↔ ¬ Even t.val := by
      simp [Nat.even_iff]
      omega
    by_cases hs : Even s.val
    · rw [if_pos hs, if_neg (hpar.mp hs)]
      omega
    · have ht : Even t.val := by
        by_contra hnt
        exact hs (hpar.mpr hnt)
      rw [if_neg hs, if_pos ht]
      omega
  all_goals simp [rel, oddRel] at huv

private lemma deleteCColor_valid {q L : ℕ} (hq : 3 ≤ q) (hL : Odd L)
    (i : Fin (q - 1)) {u v : OddVertex q L}
    (huv : ((graph q L).deleteIncidenceSet (c i)).Adj u v) :
    deleteCColor hq i u ≠ deleteCColor hq i v := by
  rw [deleteIncidenceSet_adj, graph_adj] at huv
  rcases huv with ⟨⟨hne, huv | huv⟩, hu, hv⟩
  · exact Fin.ne_of_val_ne (deleteCColorNat_ne_of_rel hL i hne huv hu hv)
  · exact Fin.ne_of_val_ne
      (deleteCColorNat_ne_of_rel hL i hne.symm huv hv hu).symm

private lemma delete_c_colorable {q L : ℕ} (hq : 3 ≤ q) (hL : Odd L)
    (i : Fin (q - 1)) : ((graph q L).deleteIncidenceSet (c i)).Colorable q :=
  ⟨SimpleGraph.Coloring.mk (deleteCColor hq i) (deleteCColor_valid hq hL i)⟩

private def deleteXColorNat {q L : ℕ} (cut : Fin (L + 1)) : OddVertex q L → ℕ
  | p j => j.val
  | c j => j.val + 1
  | x m =>
      if m.val < cut.val then m.val % 2
      else if m = cut then 0
      else (m.val + 1) % 2

private def deleteXColor {q L : ℕ} (hq : 3 ≤ q) (cut : Fin (L + 1))
    (v : OddVertex q L) : Fin q :=
  ⟨deleteXColorNat cut v, by
    cases v with
    | p j => exact j.isLt
    | c j => dsimp [deleteXColorNat]; omega
    | x m =>
        simp only [deleteXColorNat]
        split
        · exact (Nat.mod_lt _ (by omega)).trans (by omega)
        · split
          · omega
          · exact (Nat.mod_lt _ (by omega)).trans (by omega)⟩

private lemma deleteXColorNat_ne_of_rel {q L : ℕ} (hq : 3 ≤ q) (hL : Odd L)
    (cut : Fin (L + 1)) {u v : OddVertex q L} (hne : u ≠ v)
    (huv : rel q L u v) (hu : u ≠ x cut) (hv : v ≠ x cut) :
    deleteXColorNat (q := q) cut u ≠ deleteXColorNat cut v := by
  cases u <;> cases v
  case p.p j k =>
    simp only [deleteXColorNat]
    intro hjk
    apply hne
    simp [Fin.ext hjk]
  case c.p j k =>
    simp only [deleteXColorNat, rel, oddRel] at huv ⊢
    exact huv.symm
  case x.p m j =>
    simp only [rel, oddRel] at huv
    rcases huv with ⟨hmOdd, hj⟩ | ⟨hmL, hj⟩
    · simp only [deleteXColorNat]
      split_ifs with hbefore hcut
      · simp [Nat.odd_iff] at hmOdd
        omega
      · exact (hu (by rw [hcut])).elim
      · simp [Nat.odd_iff] at hmOdd
        omega
    · have hmval : m.val = L := hmL
      have hmcut : m ≠ cut := by
        intro h
        exact hu (by simp [h])
      have hcutlt : cut.val < L := by
        have hmle := cut.isLt
        have hneval : cut.val ≠ L := by
          intro h
          apply hmcut
          apply Fin.ext
          omega
        omega
      simp only [deleteXColorNat]
      rw [if_neg (by omega), if_neg hmcut]
      simp [Nat.odd_iff] at hL
      omega
  case x.c m j =>
    simp only [rel, oddRel] at huv
    rcases huv with ⟨hmEven, hj⟩ | ⟨hm0, hj0⟩
    · simp only [deleteXColorNat]
      split_ifs with hbefore hcut
      · simp [Nat.even_iff] at hmEven
        omega
      · exact (hu (by rw [hcut])).elim
      · simp [Nat.even_iff] at hmEven
        omega
    · have hmval : m.val = 0 := hm0
      have hmcut : m ≠ cut := by
        intro h
        exact hu (by simp [h])
      have hzero_lt : 0 < cut.val := by
        by_contra hn
        apply hmcut
        apply Fin.ext
        omega
      simp only [deleteXColorNat]
      rw [if_pos (by omega)]
      omega
  case x.x m n =>
    simp only [rel, oddRel] at huv
    have hmcut : m ≠ cut := by
      intro h
      exact hu (by simp [h])
    have hncut : n ≠ cut := by
      intro h
      exact hv (by simp [h])
    have hmval : m.val ≠ cut.val := fun h => hmcut (Fin.ext h)
    have hnval : n.val ≠ cut.val := fun h => hncut (Fin.ext h)
    simp only [deleteXColorNat]
    split_ifs <;> omega
  all_goals simp [rel, oddRel] at huv

private lemma deleteXColor_valid {q L : ℕ} (hq : 3 ≤ q) (hL : Odd L)
    (cut : Fin (L + 1)) {u v : OddVertex q L}
    (huv : ((graph q L).deleteIncidenceSet (x cut)).Adj u v) :
    deleteXColor hq cut u ≠ deleteXColor hq cut v := by
  rw [deleteIncidenceSet_adj, graph_adj] at huv
  rcases huv with ⟨⟨hne, huv | huv⟩, hu, hv⟩
  · exact Fin.ne_of_val_ne (deleteXColorNat_ne_of_rel hq hL cut hne huv hu hv)
  · exact Fin.ne_of_val_ne
      (deleteXColorNat_ne_of_rel hq hL cut hne.symm huv hv hu).symm

private lemma delete_x_colorable {q L : ℕ} (hq : 3 ≤ q) (hL : Odd L)
    (cut : Fin (L + 1)) : ((graph q L).deleteIncidenceSet (x cut)).Colorable q :=
  ⟨SimpleGraph.Coloring.mk (deleteXColor hq cut) (deleteXColor_valid hq hL cut)⟩

theorem delete_vertex_colorable {q L : ℕ} (hq : 3 ≤ q) (hL : Odd L)
    (v : OddVertex q L) : ((graph q L).deleteIncidenceSet v).Colorable q := by
  cases v with
  | p i => exact delete_p_colorable hq hL i
  | c i => exact delete_c_colorable hq hL i
  | x i => exact delete_x_colorable hq hL i

theorem induce_compl_vertex_colorable {q L : ℕ} (hq : 3 ≤ q) (hL : Odd L)
    (v : OddVertex q L) : ((graph q L).induce ({v}ᶜ : Set _)).Colorable q := by
  obtain ⟨C⟩ := delete_vertex_colorable hq hL v
  refine ⟨SimpleGraph.Coloring.mk (fun x ↦ C x.1) ?_⟩
  intro x y hxy
  apply C.valid
  rw [deleteIncidenceSet_adj]
  refine ⟨induce_adj.mp hxy, ?_, ?_⟩
  · simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using x.2
  · simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using y.2

end OddDelete

/-! ## The even-order obstruction -/

namespace EvenConstruction

open Function

inductive EvenVertex (q t : ℕ)
  | a : Fin (q - 1) → EvenVertex q t
  | b : Fin (q - 1) → EvenVertex q t
  | z : EvenVertex q t
  | w : EvenVertex q t
  | x : Fin t → EvenVertex q t
  | y : Fin t → EvenVertex q t
  deriving DecidableEq, Fintype

open EvenVertex

private def lastColor (q : ℕ) (hq : 3 ≤ q) : Fin (q - 1) :=
  ⟨q - 2, by omega⟩

def EvenAdj (q t : ℕ) : EvenVertex q t → EvenVertex q t → Prop
  | a i, a j => i ≠ j
  | a j, b i => i ≠ j
  | b i, a j => i ≠ j
  | w, b _ | b _, w => True
  | z, a _ | a _, z => True
  | z, b _ | b _, z => True
  | z, w | w, z => t = 0
  | z, x s | x s, z => s.1 = 0
  | x s, y r | y r, x s => s = r ∨ s.1 = r.1 + 1
  | y s, w | w, y s => s.1 + 1 = t
  | x _, b i | b i, x _ => i.1 + 2 < q
  | y _, a i | a i, y _ => i.1 + 2 < q
  | _, _ => False

noncomputable instance evenAdjDecidable (q t : ℕ) : DecidableRel (EvenAdj q t) :=
  Classical.decRel _

private lemma evenAdj_symm (q t : ℕ) : Std.Symm (EvenAdj q t) := by
  constructor
  intro u v huv
  cases u <;> cases v <;> simp_all [EvenAdj, ne_comm, eq_comm]

private lemma evenAdj_irrefl (q t : ℕ) : Std.Irrefl (EvenAdj q t) := by
  constructor
  intro u
  cases u <;> simp [EvenAdj]

def evenGraph (q t : ℕ) : SimpleGraph (EvenVertex q t) where
  Adj := EvenAdj q t
  symm := evenAdj_symm q t
  loopless := evenAdj_irrefl q t

@[simp] lemma evenGraph_adj (q t : ℕ) (u v : EvenVertex q t) :
    (evenGraph q t).Adj u v ↔ EvenAdj q t u v := Iff.rfl

private def side {q t : ℕ} : EvenVertex q t → Bool
  | a _ | w | x _ => false
  | b _ | z | y _ => true

private def Exceptional {q t : ℕ} : EvenVertex q t → EvenVertex q t → Prop
  | a i, a j => i ≠ j
  | z, b _ | b _, z => True
  | _, _ => False

private lemma exceptional_symm {q t : ℕ} : Std.Symm (@Exceptional q t) := by
  constructor
  intro u v huv
  cases u <;> cases v <;> simp_all [Exceptional, ne_comm]

private lemma adj_not_exceptional_side_ne {q t : ℕ} {u v : EvenVertex q t}
    (huv : EvenAdj q t u v) (hne : ¬ Exceptional u v) : side u ≠ side v := by
  cases u <;> cases v <;> simp_all [EvenAdj, Exceptional, side]

private lemma exceptional_subgraph {q t : ℕ} {u v : EvenVertex q t}
    (h : Exceptional u v) : EvenAdj q t u v := by
  cases u <;> cases v <;> simp_all [EvenAdj, Exceptional]

private def exceptionalEdgeSet (q t : ℕ) : Set (Sym2 (EvenVertex q t)) :=
  Sym2.fromRel (@exceptional_symm q t)

private lemma deleteExceptional_bipartite (q t : ℕ) :
    ((evenGraph q t).deleteEdges (exceptionalEdgeSet q t)).IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk (fun v => if side v then (1 : Fin 2) else 0) ?_⟩
  intro u v huv
  rw [deleteEdges_adj] at huv
  have hs : side u ≠ side v := by
    apply adj_not_exceptional_side_ne huv.1
    intro he
    apply huv.2
    simpa [exceptionalEdgeSet, Sym2.fromRel_prop] using he
  cases hsu : side u <;> cases hsv : side v <;> simp_all

private def core {q t : ℕ} : Option (Fin (q - 1)) → EvenVertex q t
  | none => z
  | some i => a i

private lemma coreColor_bijective {q t : ℕ} (hq : 3 ≤ q)
    (C : (evenGraph q t).Coloring (Fin q)) :
    Function.Bijective (fun i => C (core i)) := by
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro i j hij
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j =>
        exfalso
        exact (C.valid (v := z) (w := a j)
          (show (evenGraph q t).Adj z (a j) by simp [evenGraph, EvenAdj])) hij
    | some i =>
      cases j with
      | none =>
        exfalso
        exact (C.valid (v := a i) (w := z)
          (show (evenGraph q t).Adj (a i) z by simp [evenGraph, EvenAdj])) hij
      | some j =>
        simp only [Option.some.injEq]
        by_contra hij'
        exact (C.valid (v := a i) (w := a j)
          (show (evenGraph q t).Adj (a i) (a j) by simpa [evenGraph, EvenAdj])) hij
  · simp
    omega

private lemma canonical_b_color {q t : ℕ} (hq : 3 ≤ q)
    (C : (evenGraph q t).Coloring (Fin q)) (i : Fin (q - 1)) :
    C (b i) = C (a i) := by
  have hs := (coreColor_bijective hq C).2 (C (b i))
  obtain ⟨j, hj⟩ := hs
  cases j with
  | none =>
    exfalso
    exact (C.valid (v := b i) (w := z)
      (show (evenGraph q t).Adj (b i) z by simp [evenGraph, EvenAdj])) hj.symm
  | some j =>
    change C (a j) = C (b i) at hj
    by_cases hji : j = i
    · subst j
      exact hj.symm
    · exfalso
      have hij : i ≠ j := fun h => hji h.symm
      exact (C.valid (v := b i) (w := a j)
        (show (evenGraph q t).Adj (b i) (a j) by simpa [evenGraph, EvenAdj])) hj.symm

private lemma canonical_w_color {q t : ℕ} (hq : 3 ≤ q)
    (C : (evenGraph q t).Coloring (Fin q)) : C w = C z := by
  have hs := (coreColor_bijective hq C).2 (C w)
  obtain ⟨i, hi⟩ := hs
  cases i with
  | none => exact hi.symm
  | some i =>
    exfalso
    have hb := canonical_b_color hq C i
    exact (C.valid (v := w) (w := b i)
      (show (evenGraph q t).Adj w (b i) by simp [evenGraph, EvenAdj]))
      (hi.symm.trans hb.symm)

private lemma internal_x_colors {q t : ℕ} (hq : 3 ≤ q)
    (C : (evenGraph q t).Coloring (Fin q)) (s : Fin t) :
    C (x s) = C (a (lastColor q hq)) ∨ C (x s) = C z := by
  have hs := (coreColor_bijective hq C).2 (C (x s))
  obtain ⟨i, hi⟩ := hs
  cases i with
  | none => exact Or.inr hi.symm
  | some i =>
    by_cases hh : i = lastColor q hq
    · exact Or.inl (hi.symm.trans (congrArg (fun j => C (a j)) hh))
    · exfalso
      have hlt : i.1 + 2 < q := by
        have hi' := i.2
        have hhval : i.1 ≠ q - 2 := by
          intro heq
          apply hh
          apply Fin.ext
          simpa [lastColor] using heq
        omega
      have hb := canonical_b_color hq C i
      exact (C.valid (v := x s) (w := b i)
        (show (evenGraph q t).Adj (x s) (b i) by simpa [evenGraph, EvenAdj]))
        (hi.symm.trans hb.symm)

private lemma internal_y_colors {q t : ℕ} (hq : 3 ≤ q)
    (C : (evenGraph q t).Coloring (Fin q)) (s : Fin t) :
    C (y s) = C (a (lastColor q hq)) ∨ C (y s) = C z := by
  have hs := (coreColor_bijective hq C).2 (C (y s))
  obtain ⟨i, hi⟩ := hs
  cases i with
  | none => exact Or.inr hi.symm
  | some i =>
    by_cases hh : i = lastColor q hq
    · exact Or.inl (hi.symm.trans (congrArg (fun j => C (a j)) hh))
    · exfalso
      have hlt : i.1 + 2 < q := by
        have hi' := i.2
        have hhval : i.1 ≠ q - 2 := by
          intro heq
          apply hh
          apply Fin.ext
          simpa [lastColor] using heq
        omega
      exact (C.valid (v := y s) (w := a i)
        (show (evenGraph q t).Adj (y s) (a i) by simpa [evenGraph, EvenAdj])) hi.symm

theorem evenGraph_not_colorable (q t : ℕ) (hq : 3 ≤ q) :
    ¬ (evenGraph q t).Colorable q := by
  rintro ⟨C⟩
  have hw : C w = C z := canonical_w_color hq C
  cases t with
  | zero =>
    exact (C.valid (v := z) (w := w)
      (show (evenGraph q 0).Adj z w by simp [evenGraph, EvenAdj])) hw.symm
  | succ n =>
    have hpath : ∀ s : Fin (n + 1),
        C (x s) = C (a (lastColor q hq)) ∧ C (y s) = C z := by
      intro s
      induction s using Fin.induction with
      | zero =>
        have hxalt := internal_x_colors hq C (0 : Fin (n + 1))
        have hx : C (x (0 : Fin (n + 1))) = C (a (lastColor q hq)) := by
          rcases hxalt with hx | hx
          · exact hx
          · exact False.elim ((C.valid (v := z) (w := x 0)
              (show (evenGraph q (n + 1)).Adj z (x 0) by
                simp [evenGraph, EvenAdj])) hx.symm)
        have hyalt := internal_y_colors hq C (0 : Fin (n + 1))
        have hy : C (y (0 : Fin (n + 1))) = C z := by
          rcases hyalt with hy | hy
          · exact False.elim ((C.valid (v := x 0) (w := y 0)
              (show (evenGraph q (n + 1)).Adj (x 0) (y 0) by
                simp [evenGraph, EvenAdj])) (hx.trans hy.symm))
          · exact hy
        exact ⟨hx, hy⟩
      | succ i ih =>
        have hxalt := internal_x_colors hq C i.succ
        have hx : C (x i.succ) = C (a (lastColor q hq)) := by
          rcases hxalt with hx | hx
          · exact hx
          · exact False.elim ((C.valid (v := y i.castSucc) (w := x i.succ)
              (show (evenGraph q (n + 1)).Adj (y i.castSucc) (x i.succ) by
                simp [evenGraph, EvenAdj])) (ih.2.trans hx.symm))
        have hyalt := internal_y_colors hq C i.succ
        have hy : C (y i.succ) = C z := by
          rcases hyalt with hy | hy
          · exact False.elim ((C.valid (v := x i.succ) (w := y i.succ)
              (show (evenGraph q (n + 1)).Adj (x i.succ) (y i.succ) by
                simp [evenGraph, EvenAdj])) (hx.trans hy.symm))
          · exact hy
        exact ⟨hx, hy⟩
    have hyLast := (hpath (Fin.last n)).2
    exact (C.valid (v := y (Fin.last n)) (w := w)
      (show (evenGraph q (n + 1)).Adj (y (Fin.last n)) w by
        simp [evenGraph, EvenAdj])) (hyLast.trans hw.symm)

private def VertexProperNat {q t : ℕ} (c : EvenVertex q t → ℕ)
    (v : EvenVertex q t) : Prop :=
  ∀ r s, EvenAdj q t r s → r ≠ v → s ≠ v → c r ≠ c s

private def VertexBoundedNat {q t : ℕ} (c : EvenVertex q t → ℕ) : Prop :=
  ∀ v, c v < q

private def vertexOtherIndex {q : ℕ} (hq : 3 ≤ q)
    (i : Fin (q - 1)) : Fin (q - 1) :=
  if hi : i.1 = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩

private lemma vertexOtherIndex_ne {q : ℕ} (hq : 3 ≤ q) (i : Fin (q - 1)) :
    i ≠ vertexOtherIndex hq i := by
  simp [vertexOtherIndex]
  split_ifs with hi <;> simp_all [Fin.ext_iff]

private def colorDeleteA {q t : ℕ} (i d : Fin (q - 1)) : EvenVertex q t → ℕ
  | a j => j.1
  | b _ | y _ => q - 1
  | z => i.1
  | w | x _ => d.1

private lemma colorDeleteA_bounded {q t : ℕ} (hq : 3 ≤ q)
    (i d : Fin (q - 1)) : VertexBoundedNat (@colorDeleteA q t i d) := by
  intro v
  cases v <;> simp [colorDeleteA] <;> omega

private lemma colorDeleteA_proper {q t : ℕ} (hq : 3 ≤ q)
    (i d : Fin (q - 1)) (hid : i ≠ d) :
    VertexProperNat (@colorDeleteA q t i d) (a i) := by
  rintro r s hrs hri hsi heq
  cases r <;> cases s <;> simp_all [EvenAdj, colorDeleteA]
  all_goals omega

private def colorDeleteB {q t : ℕ} (i : Fin (q - 1)) : EvenVertex q t → ℕ
  | a j | b j => j.1
  | z | y _ => q - 1
  | w => i.1
  | x _ => q - 2

private lemma colorDeleteB_bounded {q t : ℕ} (hq : 3 ≤ q)
    (i : Fin (q - 1)) : VertexBoundedNat (@colorDeleteB q t i) := by
  intro v
  cases v <;> simp [colorDeleteB] <;> omega

private lemma colorDeleteB_proper {q t : ℕ} (hq : 3 ≤ q) (i : Fin (q - 1)) :
    VertexProperNat (@colorDeleteB q t i) (b i) := by
  rintro r s hrs hri hsi heq
  cases r <;> cases s <;> simp_all [EvenAdj, colorDeleteB]
  all_goals omega

private def colorDeleteZ {q t : ℕ} : EvenVertex q t → ℕ
  | a j => j.1
  | b _ | z | y _ => q - 1
  | w | x _ => 0

private lemma colorDeleteZ_bounded {q t : ℕ} (hq : 3 ≤ q) :
    VertexBoundedNat (@colorDeleteZ q t) := by
  intro v
  cases v <;> simp [colorDeleteZ] <;> omega

private lemma colorDeleteZ_proper {q t : ℕ} (hq : 3 ≤ q) :
    VertexProperNat (@colorDeleteZ q t) z := by
  rintro r s hrs hrz hsz heq
  cases r <;> cases s <;> simp_all [EvenAdj, colorDeleteZ]
  all_goals omega

private def colorDeleteW {q t : ℕ} : EvenVertex q t → ℕ
  | a j | b j => j.1
  | z | w | y _ => q - 1
  | x _ => q - 2

private lemma colorDeleteW_bounded {q t : ℕ} (hq : 3 ≤ q) :
    VertexBoundedNat (@colorDeleteW q t) := by
  intro v
  cases v <;> simp [colorDeleteW] <;> omega

private lemma colorDeleteW_proper {q t : ℕ} (hq : 3 ≤ q) :
    VertexProperNat (@colorDeleteW q t) w := by
  rintro r s hrs hrw hsw heq
  cases r <;> cases s <;> simp_all [EvenAdj, colorDeleteW]
  all_goals omega

private def colorDeleteX {q t : ℕ} (cut : Fin t) : EvenVertex q t → ℕ
  | a j | b j => j.1
  | z | w => q - 1
  | x r => if r = cut then 0 else if r.1 < cut.1 then q - 2 else q - 1
  | y r => if r.1 < cut.1 then q - 1 else q - 2

private lemma colorDeleteX_bounded {q t : ℕ} (hq : 3 ≤ q) (cut : Fin t) :
    VertexBoundedNat (colorDeleteX (q := q) cut) := by
  intro v
  cases v <;> simp [colorDeleteX] <;> (try split_ifs) <;> omega

private lemma colorDeleteX_proper {q t : ℕ} (hq : 3 ≤ q) (cut : Fin t) :
    VertexProperNat (colorDeleteX (q := q) cut) (x cut) := by
  have ht : 0 < t := Nat.zero_lt_of_lt cut.isLt
  rintro r s hrs hrc hsc heq
  cases r <;> cases s <;>
    simp_all [EvenAdj, colorDeleteX] <;> (try split_ifs at *)
  all_goals omega

private def colorDeleteY {q t : ℕ} (cut : Fin t) : EvenVertex q t → ℕ
  | a j | b j => j.1
  | z | w => q - 1
  | x r => if r.1 ≤ cut.1 then q - 2 else q - 1
  | y r => if r = cut then 0 else if r.1 < cut.1 then q - 1 else q - 2

private lemma colorDeleteY_bounded {q t : ℕ} (hq : 3 ≤ q) (cut : Fin t) :
    VertexBoundedNat (colorDeleteY (q := q) cut) := by
  intro v
  cases v <;> simp [colorDeleteY] <;> (try split_ifs) <;> omega

private lemma colorDeleteY_proper {q t : ℕ} (hq : 3 ≤ q) (cut : Fin t) :
    VertexProperNat (colorDeleteY (q := q) cut) (y cut) := by
  have ht : 0 < t := Nat.zero_lt_of_lt cut.isLt
  rintro r s hrs hrc hsc heq
  cases r <;> cases s <;>
    simp_all [EvenAdj, colorDeleteY] <;> (try split_ifs at *)
  all_goals omega

private def natToFinVertexColor {q t : ℕ} (c : EvenVertex q t → ℕ)
    (hc : VertexBoundedNat c) : EvenVertex q t → Fin q :=
  fun v => ⟨c v, hc v⟩

private lemma deleteIncidenceSet_colorable_of_nat {q t : ℕ} {v : EvenVertex q t}
    {c : EvenVertex q t → ℕ} (hc : VertexBoundedNat c) (hp : VertexProperNat c v) :
    ((evenGraph q t).deleteIncidenceSet v).Colorable q := by
  refine ⟨SimpleGraph.Coloring.mk (natToFinVertexColor c hc) ?_⟩
  intro r s hrs heq
  rw [deleteIncidenceSet_adj] at hrs
  exact hp r s hrs.1 hrs.2.1 hrs.2.2 (congrArg Fin.val heq)

theorem evenGraph_deleteIncidenceSet_colorable {q t : ℕ} (hq : 3 ≤ q) :
    ∀ v : EvenVertex q t, ((evenGraph q t).deleteIncidenceSet v).Colorable q := by
  intro v
  cases v with
  | a i =>
    exact deleteIncidenceSet_colorable_of_nat
      (colorDeleteA_bounded hq i (vertexOtherIndex hq i))
      (colorDeleteA_proper hq i (vertexOtherIndex hq i) (vertexOtherIndex_ne hq i))
  | b i =>
    exact deleteIncidenceSet_colorable_of_nat
      (colorDeleteB_bounded hq i) (colorDeleteB_proper hq i)
  | z =>
    exact deleteIncidenceSet_colorable_of_nat
      (colorDeleteZ_bounded hq) (colorDeleteZ_proper hq)
  | w =>
    exact deleteIncidenceSet_colorable_of_nat
      (colorDeleteW_bounded hq) (colorDeleteW_proper hq)
  | x cut =>
    exact deleteIncidenceSet_colorable_of_nat
      (colorDeleteX_bounded hq cut) (colorDeleteX_proper hq cut)
  | y cut =>
    exact deleteIncidenceSet_colorable_of_nat
      (colorDeleteY_bounded hq cut) (colorDeleteY_proper hq cut)

theorem evenGraph_induce_compl_vertex_colorable {q t : ℕ} (hq : 3 ≤ q)
    (v : EvenVertex q t) : ((evenGraph q t).induce ({v}ᶜ : Set _)).Colorable q := by
  obtain ⟨C⟩ := evenGraph_deleteIncidenceSet_colorable hq v
  refine ⟨SimpleGraph.Coloring.mk (fun x ↦ C x.1) ?_⟩
  intro x y hxy
  apply C.valid
  rw [deleteIncidenceSet_adj]
  refine ⟨induce_adj.mp hxy, ?_, ?_⟩
  · simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using x.2
  · simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using y.2

private def aEmbedding (q t : ℕ) : Fin (q - 1) ↪ EvenVertex q t where
  toFun := a
  inj' _ _ h := by simpa using h

private def zbEmbedding (q t : ℕ) : Fin (q - 1) ↪ Sym2 (EvenVertex q t) where
  toFun i := s(z, b i)
  inj' i j h := by simpa [Sym2.eq_iff] using h

private def aExceptionalEdges (q t : ℕ) : Finset (Sym2 (EvenVertex q t)) :=
  (⊤ : SimpleGraph (Fin (q - 1))).edgeFinset.map (aEmbedding q t).sym2Map

private def zbExceptionalEdges (q t : ℕ) : Finset (Sym2 (EvenVertex q t)) :=
  Finset.univ.map (zbEmbedding q t)

def evenExceptionalFinset (q t : ℕ) : Finset (Sym2 (EvenVertex q t)) :=
  aExceptionalEdges q t ∪ zbExceptionalEdges q t

private lemma exceptional_disjoint (q t : ℕ) :
    Disjoint (aExceptionalEdges q t) (zbExceptionalEdges q t) := by
  rw [Finset.disjoint_left]
  intro e heA heB
  simp only [aExceptionalEdges, Finset.mem_map] at heA
  simp only [zbExceptionalEdges, Finset.mem_map, Finset.mem_univ, true_and] at heB
  obtain ⟨ab, _, rfl⟩ := heA
  obtain ⟨i, hi⟩ := heB
  revert hi
  refine Sym2.inductionOn ab ?_
  intro r s hi
  change s(z, b i) = s(a r, a s) at hi
  simpa [Sym2.eq_iff] using hi

lemma evenExceptionalFinset_card (q t : ℕ) (hq : 3 ≤ q) :
    (evenExceptionalFinset q t).card = q.choose 2 := by
  have ha : (aExceptionalEdges q t).card = (q - 1).choose 2 := by
    rw [aExceptionalEdges, Finset.card_map,
      card_edgeFinset_top_eq_card_choose_two]
    simp
  have hb : (zbExceptionalEdges q t).card = q - 1 := by
    simp [zbExceptionalEdges]
  rw [evenExceptionalFinset,
    Finset.card_union_of_disjoint (exceptional_disjoint q t), ha, hb]
  have hq' : q = (q - 1) + 1 := by omega
  calc
    (q - 1).choose 2 + (q - 1) = (q - 1).choose 2 + (q - 1).choose 1 := by simp
    _ = ((q - 1) + 1).choose 2 := by
      simpa [Nat.add_comm] using (Nat.choose_succ_succ (q - 1) 1).symm
    _ = q.choose 2 := by rw [← hq']

private lemma mem_evenExceptionalFinset_iff {q t : ℕ}
    {u v : EvenVertex q t} :
    s(u, v) ∈ evenExceptionalFinset q t ↔ Exceptional u v := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · simp only [aExceptionalEdges, Finset.mem_map] at h
      obtain ⟨e, he, huv⟩ := h
      revert he huv
      refine Sym2.inductionOn e ?_
      intro i j he huv
      simp only [SimpleGraph.mem_edgeFinset, mem_edgeSet, top_adj] at he
      simp only [Function.Embedding.sym2Map_apply] at huv
      change s(a i, a j) = s(u, v) at huv
      rw [Sym2.eq_iff] at huv
      rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simpa [Exceptional] using he
      · simpa [Exceptional] using he.symm
    · simp only [zbExceptionalEdges, Finset.mem_map, Finset.mem_univ, true_and] at h
      obtain ⟨i, huv⟩ := h
      change s(z, b i) = s(u, v) at huv
      rw [Sym2.eq_iff] at huv
      rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [Exceptional]
  · intro h
    cases u <;> cases v <;> simp_all only [Exceptional]
    case a.a i j =>
      apply Finset.mem_union_left
      rw [aExceptionalEdges, Finset.mem_map]
      exact ⟨s(i, j), by
        simp [SimpleGraph.mem_edgeFinset, mem_edgeSet, h], by
        rw [Function.Embedding.sym2Map_apply, Sym2.map_mk]
        rfl⟩
    case b.z i =>
      apply Finset.mem_union_right
      rw [zbExceptionalEdges, Finset.mem_map]
      exact ⟨i, Finset.mem_univ _, (Sym2.eq_swap : s(z, b i) = s(b i, z))⟩
    case z.b i =>
      apply Finset.mem_union_right
      rw [zbExceptionalEdges, Finset.mem_map]
      exact ⟨i, Finset.mem_univ _, rfl⟩

lemma even_delete_exceptional_bipartite (q t : ℕ) :
    ((evenGraph q t).deleteEdges
      (evenExceptionalFinset q t : Set (Sym2 (EvenVertex q t)))).IsBipartite := by
  rw [show (evenExceptionalFinset q t : Set (Sym2 (EvenVertex q t))) =
      exceptionalEdgeSet q t by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
      simp [exceptionalEdgeSet, Sym2.fromRel_prop, mem_evenExceptionalFinset_iff]]
  exact deleteExceptional_bipartite q t

lemma evenExceptional_subset_edgeSet (q t : ℕ) :
    (evenExceptionalFinset q t : Set (Sym2 (EvenVertex q t))) ⊆
      (evenGraph q t).edgeSet := by
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
    rw [mem_edgeSet]
    exact exceptional_subgraph
      ((mem_evenExceptionalFinset_iff (q := q) (t := t)).mp he)

lemma even_canBipartizeBy (q t : ℕ) (hq : 3 ≤ q) :
    CanBipartizeBy (evenGraph q t) (q.choose 2) := by
  refine ⟨(evenExceptionalFinset q t : Set _),
    evenExceptional_subset_edgeSet q t, ?_, even_delete_exceptional_bipartite q t⟩
  rw [Set.ncard_coe_finset, evenExceptionalFinset_card q t hq]

end EvenConstruction

/-! ## Relabeling and assembly of the upper bound -/

private def sym2Equiv {V W : Type*} (e : V ≃ W) : Sym2 V ≃ Sym2 W where
  toFun := Sym2.map e
  invFun := Sym2.map e.symm
  left_inv x := by
    induction x using Sym2.inductionOn with
    | _ a b => simp
  right_inv x := by
    induction x using Sym2.inductionOn with
    | _ a b => simp

theorem canBipartizeBy_comap_equiv {V W : Type*} [Fintype V] [Fintype W]
    (e : V ≃ W) {G : SimpleGraph W} {m : ℕ}
    (h : CanBipartizeBy G m) : CanBipartizeBy (G.comap e) m := by
  classical
  obtain ⟨E, hEG, hEcard, hEbip⟩ := h
  let E' : Set (Sym2 V) := (sym2Equiv e) ⁻¹' E
  have hE'sub : E' ⊆ (G.comap e).edgeSet := by
    intro p hp
    have hpG := hEG hp
    induction p using Sym2.inductionOn with
    | _ a b =>
      rw [mem_edgeSet]
      change G.Adj (e a) (e b) at hpG
      exact hpG
  have hE'card : E'.ncard = m := by
    change ((sym2Equiv e) ⁻¹' E).ncard = m
    rw [Set.ncard_preimage_of_injective_subset_range
      (sym2Equiv e).injective (by simp [(sym2Equiv e).surjective.range_eq]), hEcard]
  refine ⟨E', hE'sub, hE'card, ?_⟩
  have heq : (G.comap e).deleteEdges E' = (G.deleteEdges E).comap e := by
    ext a b
    simp [E', sym2Equiv, deleteEdges_adj]
  rw [heq]
  exact (SimpleGraph.colorable_congr
    (SimpleGraph.Iso.comap e (G.deleteEdges E))).mpr hEbip

private lemma bijOn_compl_singleton {V W : Type*} (e : V ≃ W) (v : V) :
    Set.BijOn e ({v}ᶜ : Set V) ({e v}ᶜ : Set W) := by
  refine ⟨?_, e.injective.injOn, ?_⟩
  · intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
    intro h
    exact hx (e.injective h)
  · intro y hy
    refine ⟨e.symm y, ?_, by simp⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hy ⊢
    intro h
    apply hy
    calc
      y = e (e.symm y) := (e.apply_symm_apply y).symm
      _ = e v := congrArg e h

theorem induce_compl_colorable_comap_equiv {V W : Type*}
    (e : V ≃ W) {G : SimpleGraph W} {q : ℕ}
    (h : ∀ w : W, (G.induce ({w}ᶜ : Set W)).Colorable q) :
    ∀ v : V, ((G.comap e).induce ({v}ᶜ : Set V)).Colorable q := by
  intro v
  let φ : G.comap e ≃g G := SimpleGraph.Iso.comap e G
  exact (SimpleGraph.colorable_congr
    (φ.induce (bijOn_compl_singleton e v))).mpr (h (e v))

theorem exists_critical_comap_of_obstruction
    {V W : Type*} [Fintype V] [Fintype W] [Nonempty V]
    (e : V ≃ W) (G : SimpleGraph W) (q m : ℕ)
    (hncol : ¬ G.Colorable q)
    (hvertex : ∀ w : W, (G.induce ({w}ᶜ : Set W)).Colorable q)
    (hbip : CanBipartizeBy G m) :
    ∃ H : SimpleGraph V, IsCritical H (q + 1) ∧ deletionNumber H ≤ m := by
  let G' : SimpleGraph V := G.comap e
  have hncol' : ¬ G'.Colorable q := by
    intro hcol
    exact hncol ((SimpleGraph.colorable_congr
      (SimpleGraph.Iso.comap e G)).mp hcol)
  have hvertex' : ∀ v : V, (G'.induce ({v}ᶜ : Set V)).Colorable q :=
    induce_compl_colorable_comap_equiv e hvertex
  have hbip' : CanBipartizeBy G' m := canBipartizeBy_comap_equiv e hbip
  obtain ⟨H, -, -, hHcrit, m', hm', hHm'⟩ :=
    exists_critical_subgraph_le_of_vertex_deletions G' q m hncol' hvertex' hbip'
  exact ⟨H, hHcrit, (deletionNumber_le_of_canBipartizeBy hHm').trans hm'⟩

private def oddVertexEquiv (q L : ℕ) :
    OddVertex q L ≃ Fin q ⊕ (Fin (q - 1) ⊕ Fin (L + 1)) where
  toFun
    | .p i => Sum.inl i
    | .c i => Sum.inr (Sum.inl i)
    | .x i => Sum.inr (Sum.inr i)
  invFun
    | Sum.inl i => .p i
    | Sum.inr (Sum.inl i) => .c i
    | Sum.inr (Sum.inr i) => .x i
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with x | (x | x) <;> rfl

private def evenVertexEquiv (q t : ℕ) :
    EvenConstruction.EvenVertex q t ≃
      Fin (q - 1) ⊕ (Fin (q - 1) ⊕
        (Unit ⊕ (Unit ⊕ (Fin t ⊕ Fin t)))) where
  toFun
    | .a i => Sum.inl i
    | .b i => Sum.inr (Sum.inl i)
    | .z => Sum.inr (Sum.inr (Sum.inl ()))
    | .w => Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))
    | .x i => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))
    | .y i => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr i))))
  invFun
    | Sum.inl i => .a i
    | Sum.inr (Sum.inl i) => .b i
    | Sum.inr (Sum.inr (Sum.inl _)) => .z
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => .w
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))) => .x i
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr i)))) => .y i
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with x | (x | (_ | (_ | (x | x)))) <;> rfl

@[simp] lemma card_oddVertex (q L : ℕ) :
    Fintype.card (OddVertex q L) = q + (q - 1) + (L + 1) := by
  rw [Fintype.card_congr (oddVertexEquiv q L)]
  simp
  omega

@[simp] lemma card_evenVertex (q t : ℕ) :
    Fintype.card (EvenConstruction.EvenVertex q t) =
      (q - 1) + (q - 1) + 2 + t + t := by
  rw [Fintype.card_congr (evenVertexEquiv q t)]
  simp
  omega

/-- The two explicit parity families provide an admissible graph of every
order `n ≥ 2q`. -/
theorem exists_critical_fin_deletion_le {q n : ℕ} (hq : 3 ≤ q)
    (hn : 2 * q ≤ n) :
    ∃ H : SimpleGraph (Fin n),
      IsCritical H (q + 1) ∧ deletionNumber H ≤ q.choose 2 := by
  let _ : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  rcases Nat.even_or_odd n with heven | hodd
  · obtain ⟨r, hr⟩ := heven
    have hqr : q ≤ r := by omega
    let t := r - q
    have hnform : n = 2 * q + 2 * t := by
      dsimp [t]
      omega
    let e : Fin n ≃ EvenConstruction.EvenVertex q t :=
      Fintype.equivOfCardEq (by simp [hnform]; omega)
    exact exists_critical_comap_of_obstruction e
      (EvenConstruction.evenGraph q t) q (q.choose 2)
      (EvenConstruction.evenGraph_not_colorable q t hq)
      (EvenConstruction.evenGraph_induce_compl_vertex_colorable hq)
      (EvenConstruction.even_canBipartizeBy q t hq)
  · obtain ⟨r, hr⟩ := hodd
    have hqr : q ≤ r := by omega
    let t := r - q
    let L := 2 * t + 1
    have hL : Odd L := ⟨t, rfl⟩
    have hnform : n = 2 * q + 2 * t + 1 := by
      dsimp [t]
      omega
    let e : Fin n ≃ OddVertex q L :=
      Fintype.equivOfCardEq (by simp [hnform, L]; omega)
    exact exists_critical_comap_of_obstruction e (oddGraph q L) q (q.choose 2)
      (oddGraph_not_colorable hq hL)
      (OddDelete.induce_compl_vertex_colorable hq hL)
      (odd_canBipartizeBy hL)

/-- An explicit threshold for the Rödl--Tuza equality. -/
def threshold (q : ℕ) : ℕ := max (2 * q) (2 * q.choose 2 - 1)

/-- **Resolution of Erdős Problem 744.**  Here the chromatic number is
`q + 1`, so the value is `choose q 2 = choose ((q + 1) - 1) 2`. -/
theorem erdos_744 {q n : ℕ} (hq : 3 ≤ q) (hn : threshold q ≤ n) :
    f (q + 1) n = q.choose 2 := by
  have hnconstruct : 2 * q ≤ n :=
    (le_max_left (2 * q) (2 * q.choose 2 - 1)).trans hn
  have hnlarge : 2 * q.choose 2 - 1 ≤ n :=
    (le_max_right (2 * q) (2 * q.choose 2 - 1)).trans hn
  obtain ⟨H, hHcrit, hHdel⟩ := exists_critical_fin_deletion_le hq hnconstruct
  apply Nat.le_antisymm
  · exact (f_le_deletionNumber hHcrit).trans hHdel
  · apply le_f_of_forall_critical ⟨H, hHcrit⟩
    intro G hG
    apply critical_deletionNumber_lower hq
    · simpa using hnlarge
    · exact hG

/-- The original indexing: for every fixed chromatic number `k ≥ 4`, the
extremal function is eventually the constant `choose (k - 1) 2`. -/
theorem erdos_744_eventually (k : ℕ) (hk : 4 ≤ k) :
    ∀ᶠ n in atTop, f k n = (k - 1).choose 2 := by
  let q := k - 1
  have hq : 3 ≤ q := by dsimp [q]; omega
  filter_upwards [eventually_ge_atTop (threshold q)] with n hn
  have h := erdos_744 hq hn
  simpa [q, Nat.sub_add_cancel (by omega : 1 ≤ k)] using h

/-- Thus the proposed convergence to infinity is false for every `k ≥ 4`. -/
theorem erdos_744_not_tendsto_atTop (k : ℕ) (hk : 4 ≤ k) :
    ¬ Tendsto (f k) atTop atTop := by
  intro htop
  have hconst := erdos_744_eventually k hk
  obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.mp htop) ((k - 1).choose 2 + 1)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hconst
  let n := max N M
  have hle := hN n (le_max_left N M)
  have heq := hM n (le_max_right N M)
  omega

/-- In particular, the first open case is eventually equal to `3`. -/
theorem erdos_744_four : ∀ᶠ n in atTop, f 4 n = 3 := by
  simpa using erdos_744_eventually 4 (by omega)

/-- A stronger form of the logarithmic corollary: no natural-valued function
which tends to infinity can be an eventual lower bound for `f 4`. -/
theorem erdos_744_four_has_no_divergent_lower_bound (g : ℕ → ℕ)
    (hg : Tendsto g atTop atTop) :
    ¬ ∀ᶠ n in atTop, g n ≤ f 4 n := by
  intro hge
  obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.mp hg) 4
  obtain ⟨M, hM⟩ := eventually_atTop.mp hge
  obtain ⟨K, hK⟩ := eventually_atTop.mp erdos_744_four
  let n := max N (max M K)
  have hgn := hN n (le_max_left N (max M K))
  have hn := hM n ((le_max_left M K).trans (le_max_right N (max M K)))
  have hf := hK n ((le_max_right M K).trans (le_max_right N (max M K)))
  omega

#print axioms Erdos744.erdos_744

end Erdos744
