/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-!
# Erdős Problem 594

Every graph with no countable proper coloring contains all sufficiently large
odd cycles.  The mathematical proof and the correspondence between its lemmas
and this development are in `tex/594.tex`.
-/

open Function Set SimpleGraph
open scoped Ordinal

namespace Erdos594

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u}

/-- A graph is uncountably chromatic when it has no coloring by natural numbers. -/
def IsUncountablyChromatic (G : SimpleGraph V) : Prop :=
  IsEmpty (G.Coloring ℕ)

lemma isUncountablyChromatic_iff_not_nonempty {G : SimpleGraph V} :
    IsUncountablyChromatic G ↔ ¬ Nonempty (G.Coloring ℕ) := by
  simp [IsUncountablyChromatic]

/-! ## Combining countable colorings -/

/-- Color a graph by choosing a countable coloring on every connected component. -/
noncomputable def coloringOfConnectedComponents (G : SimpleGraph V)
    (C : (c : G.ConnectedComponent) → c.toSimpleGraph.Coloring ℕ) :
    G.Coloring ℕ :=
  G.homOfConnectedComponents C

/-- If every connected component is countably colorable, so is the whole graph. -/
lemma nonempty_coloring_of_components (G : SimpleGraph V)
    (h : ∀ c : G.ConnectedComponent, Nonempty (c.toSimpleGraph.Coloring ℕ)) :
    Nonempty (G.Coloring ℕ) := by
  classical
  exact ⟨coloringOfConnectedComponents G (fun c ↦ Classical.choice (h c))⟩

/-- An uncountably chromatic graph has an uncountably chromatic connected component. -/
lemma exists_uncountably_chromatic_component {G : SimpleGraph V}
    (hG : IsUncountablyChromatic G) :
    ∃ c : G.ConnectedComponent, IsUncountablyChromatic c.toSimpleGraph := by
  rw [isUncountablyChromatic_iff_not_nonempty] at hG
  simp_rw [isUncountablyChromatic_iff_not_nonempty]
  by_contra! h
  exact hG (nonempty_coloring_of_components G h)

/-- A finite edge-union of countably colorable graphs is countably colorable. -/
lemma nonempty_coloring_of_le_iSup {n : ℕ} {G : SimpleGraph V}
    (H : Fin n → SimpleGraph V) (hle : G ≤ ⨆ i, H i)
    (hH : ∀ i, Nonempty ((H i).Coloring ℕ)) :
    Nonempty (G.Coloring ℕ) := by
  classical
  let C : (i : Fin n) → (H i).Coloring ℕ := fun i ↦ Classical.choice (hH i)
  let color : V → ℕ := fun v ↦ Encodable.encode (fun i ↦ C i v)
  refine ⟨SimpleGraph.Coloring.mk color ?_⟩
  intro v w hvw heq
  have hfun : (fun i ↦ C i v) = fun i ↦ C i w :=
    Encodable.encode_injective heq
  have hi : ∃ i, (H i).Adj v w := by
    simpa only [iSup_adj] using hle hvw
  obtain ⟨i, hi⟩ := hi
  exact (C i).valid hi (congrFun hfun i)

/-- In a finite edge decomposition of an uncountably chromatic graph, one
summand is uncountably chromatic. -/
lemma exists_uncountably_chromatic_of_le_iSup {n : ℕ} {G : SimpleGraph V}
    (H : Fin n → SimpleGraph V) (hle : G ≤ ⨆ i, H i)
    (hG : IsUncountablyChromatic G) :
    ∃ i, IsUncountablyChromatic (H i) := by
  rw [isUncountablyChromatic_iff_not_nonempty] at hG
  simp_rw [isUncountablyChromatic_iff_not_nonempty]
  by_contra! h
  exact hG (nonempty_coloring_of_le_iSup H hle h)

/-! ## Breadth-first layers -/

/-- Vertices at graph distance `i` from a root.  This is used only in a
connected graph, so the junk value of `SimpleGraph.dist` off the root component
does not arise. -/
def layer (G : SimpleGraph V) (root : V) (i : ℕ) : Set V :=
  {v | G.dist root v = i}

@[simp]
lemma mem_layer {G : SimpleGraph V} {root v : V} {i : ℕ} :
    v ∈ layer G root i ↔ G.dist root v = i :=
  Iff.rfl

/-- Countable colorings of all distance layers combine to color a connected graph. -/
lemma nonempty_coloring_of_layers {G : SimpleGraph V} (_hconn : G.Connected) (root : V)
    (h : ∀ i : ℕ, Nonempty ((G.induce (layer G root i)).Coloring ℕ)) :
    Nonempty (G.Coloring ℕ) := by
  classical
  let C : (i : ℕ) → (G.induce (layer G root i)).Coloring ℕ :=
    fun i ↦ Classical.choice (h i)
  let D : ℕ → V → ℕ := fun i v ↦
    if hv : v ∈ layer G root i then C i ⟨v, hv⟩ else 0
  let color : V → ℕ := fun v ↦
    Nat.pairEquiv (G.dist root v, D (G.dist root v) v)
  refine ⟨SimpleGraph.Coloring.mk color ?_⟩
  intro v w hvw heq
  have hp := Nat.pairEquiv.injective heq
  have hdist : G.dist root v = G.dist root w := congrArg Prod.fst hp
  have hcolor : D (G.dist root v) v = D (G.dist root w) w := congrArg Prod.snd hp
  have hv : v ∈ layer G root (G.dist root w) := hdist
  have hw : w ∈ layer G root (G.dist root w) := rfl
  have hadj : (G.induce (layer G root (G.dist root w))).Adj
      ⟨v, hv⟩ ⟨w, hw⟩ := hvw
  exact (C (G.dist root w)).valid hadj (by simpa [D, layer, hdist, hv, hw] using hcolor)

/-- Some breadth-first layer of a connected uncountably chromatic graph is
uncountably chromatic. -/
lemma exists_uncountably_chromatic_layer {G : SimpleGraph V}
    (hconn : G.Connected) (hG : IsUncountablyChromatic G) (root : V) :
    ∃ i : ℕ, IsUncountablyChromatic (G.induce (layer G root i)) := by
  rw [isUncountablyChromatic_iff_not_nonempty] at hG
  simp_rw [isUncountablyChromatic_iff_not_nonempty]
  by_contra! h
  exact hG (nonempty_coloring_of_layers hconn root h)

/-! ## Two geodesics and their last common vertex -/

/-- On a path, a vertex lying strictly after `w` has a strictly longer
initial segment than `w`.  Expressing "after" by membership in `dropUntil`
avoids choosing numerical positions in later arguments. -/
lemma length_takeUntil_lt_of_mem_dropUntil {G : SimpleGraph V} {a b w x : V}
    (p : G.Walk a b) (hp : p.IsPath) (hw : w ∈ p.support)
    (hx : x ∈ (p.dropUntil w hw).support) (xw : x ≠ w) :
    (p.takeUntil w hw).length <
      (p.takeUntil x (p.support_dropUntil_subset_support hw hx)).length := by
  classical
  let pw := p.takeUntil w hw
  let pr := p.dropUntil w hw
  obtain ⟨n, hxn, hnle⟩ := Walk.mem_support_iff_exists_getVert.mp hx
  change n ≤ pr.length at hnle
  have hnpos : 0 < n := by
    apply Nat.pos_of_ne_zero
    intro hn
    subst n
    exact xw (by simpa [pr] using hxn.symm)
  have hlen : pw.length + pr.length = p.length := by
    simpa only [Walk.length_append] using congrArg Walk.length (p.take_spec hw)
  have hposle : pw.length + n ≤ p.length := by omega
  have hget : p.getVert (pw.length + n) = x := by
    conv_lhs => rw [← p.take_spec hw]
    rw [Walk.getVert_append]
    simpa [pw, pr, hnpos.ne'] using hxn
  have hend : p.getVert
      (p.takeUntil x (p.support_dropUntil_subset_support hw hx)).length = x :=
    p.getVert_length_takeUntil _
  have heq : pw.length + n =
      (p.takeUntil x (p.support_dropUntil_subset_support hw hx)).length :=
    hp.getVert_injOn hposle (p.length_takeUntil_le_length _) (hget.trans hend.symm)
  change pw.length < (p.takeUntil x (p.support_dropUntil_subset_support hw hx)).length
  omega

/-- Every initial segment of a geodesic from `root` is again geodesic. -/
lemma length_takeUntil_eq_dist_of_geodesic {G : SimpleGraph V} {root u x : V}
    (p : G.Walk root u) (hp : p.length = G.dist root u) (hx : x ∈ p.support) :
    (p.takeUntil x hx).length = G.dist root x :=
  length_eq_dist_of_subwalk hp (p.isSubwalk_takeUntil hx)

/-- Distinct vertices in one breadth-first layer are joined through earlier
layers by a simple path of positive even length, bounded by twice the layer
index. -/
lemma exists_even_detour {G : SimpleGraph V} (hconn : G.Connected)
    {root u v : V} {i : ℕ} (hu : G.dist root u = i) (hv : G.dist root v = i)
    (huv : u ≠ v) :
    ∃ m < i, ∃ q : G.Walk u v,
      q.IsPath ∧ q.length = 2 * (m + 1) ∧
        ∀ x ∈ q.support, x ≠ u → x ≠ v → G.dist root x < i := by
  classical
  obtain ⟨p, hp_path, hp_len⟩ := hconn.exists_path_of_dist root u
  obtain ⟨r, hr_path, hr_len⟩ := hconn.exists_path_of_dist root v
  let common : Finset V := p.support.toFinset ∩ r.support.toFinset
  have hcommon : common.Nonempty := by
    refine ⟨root, ?_⟩
    simp [common, p.start_mem_support, r.start_mem_support]
  obtain ⟨w, hw_common, hw_max⟩ :=
    common.exists_max_image (G.dist root) hcommon
  have hwp : w ∈ p.support := by
    exact (by simpa [common] using hw_common : w ∈ p.support ∧ w ∈ r.support).1
  have hwr : w ∈ r.support := by
    exact (by simpa [common] using hw_common : w ∈ p.support ∧ w ∈ r.support).2
  have hp_take : (p.takeUntil w hwp).length = G.dist root w :=
    length_takeUntil_eq_dist_of_geodesic p hp_len hwp
  have hr_take : (r.takeUntil w hwr).length = G.dist root w :=
    length_takeUntil_eq_dist_of_geodesic r hr_len hwr
  have hdist_le : G.dist root w ≤ i := by
    have := p.length_takeUntil_le_length hwp
    omega
  have hdist_lt : G.dist root w < i := by
    refine lt_of_le_of_ne hdist_le ?_
    intro heq
    have hwu : w = u := by
      rw [← p.getVert_length_takeUntil hwp, hp_take, heq, ← hu, ← hp_len,
        p.getVert_length]
    have hwv : w = v := by
      rw [← r.getVert_length_takeUntil hwr, hr_take, heq, ← hv, ← hr_len,
        r.getVert_length]
    exact huv (hwu.symm.trans hwv)
  let pu : G.Walk u w := (p.dropUntil w hwp).reverse
  let rv : G.Walk w v := r.dropUntil w hwr
  have hpu_path : pu.IsPath := (hp_path.dropUntil hwp).reverse
  have hrv_path : rv.IsPath := hr_path.dropUntil hwr
  have hdisj : pu.support.Disjoint rv.support.tail := by
    intro x hxpu hxrv
    have hxpd : x ∈ (p.dropUntil w hwp).support := by
      simpa [pu, Walk.support_reverse] using hxpu
    have hxrd : x ∈ (r.dropUntil w hwr).support := List.mem_of_mem_tail hxrv
    have hwnot : w ∉ rv.support.tail := by
      have hn := hrv_path.support_nodup
      rw [← rv.cons_tail_support] at hn
      exact hn.notMem
    have hxw : x ≠ w := fun h ↦ by subst x; exact hwnot hxrv
    have hxp : x ∈ p.support := p.support_dropUntil_subset_support hwp hxpd
    have hxr : x ∈ r.support := r.support_dropUntil_subset_support hwr hxrd
    have hxcommon : x ∈ common := by simpa [common] using And.intro hxp hxr
    have hle := hw_max x hxcommon
    have hlt := length_takeUntil_lt_of_mem_dropUntil p hp_path hwp hxpd hxw
    have hxp_take := length_takeUntil_eq_dist_of_geodesic p hp_len hxp
    omega
  let q : G.Walk u v := pu.append rv
  have hq_path : q.IsPath := by
    change (pu.append rv).IsPath
    rw [Walk.isPath_def, Walk.support_append, List.nodup_append']
    exact ⟨hpu_path.support_nodup, hrv_path.support_nodup.tail, hdisj⟩
  have hp_drop : (p.dropUntil w hwp).length = i - G.dist root w := by
    have hsplit : (p.takeUntil w hwp).length + (p.dropUntil w hwp).length = p.length := by
      simpa only [Walk.length_append] using congrArg Walk.length (p.take_spec hwp)
    omega
  have hr_drop : (r.dropUntil w hwr).length = i - G.dist root w := by
    have hsplit : (r.takeUntil w hwr).length + (r.dropUntil w hwr).length = r.length := by
      simpa only [Walk.length_append] using congrArg Walk.length (r.take_spec hwr)
    omega
  let m := i - G.dist root w - 1
  have hm : m < i := by omega
  refine ⟨m, hm, q, hq_path, ?_, ?_⟩
  · simp only [q, Walk.length_append, pu, rv, Walk.length_reverse]
    omega
  · intro x hxq hxu hxv
    change x ∈ (pu.append rv).support at hxq
    rw [Walk.mem_support_append_iff] at hxq
    rcases hxq with hxpu | hxrv
    · have hxpd : x ∈ (p.dropUntil w hwp).support := by
        simpa [pu, Walk.support_reverse] using hxpu
      have hxp : x ∈ p.support := p.support_dropUntil_subset_support hwp hxpd
      have htake := length_takeUntil_eq_dist_of_geodesic p hp_len hxp
      have hlt := p.length_takeUntil_lt_length hxp hxu
      omega
    · have hxr : x ∈ r.support :=
        r.support_dropUntil_subset_support hwr hxrv
      have htake := length_takeUntil_eq_dist_of_geodesic r hr_len hxr
      have hlt := r.length_takeUntil_lt_length hxr hxv
      omega

/-! ## The finite edge decomposition of a layer -/

/-- There is an even `u`--`v` path of the prescribed length whose internal
vertices lie strictly below layer `i`. -/
def HasEvenDetour (G : SimpleGraph V) (root : V) (i m : ℕ) (u v : V) : Prop :=
  ∃ q : G.Walk u v,
    q.IsPath ∧ q.length = 2 * (m + 1) ∧
      ∀ x ∈ q.support, x ≠ u → x ≠ v → G.dist root x < i

/-- The `m`-th auxiliary graph in the Erdős--Hajnal--Shelah decomposition of
one breadth-first layer. -/
def detourGraph (G : SimpleGraph V) (root : V) (i m : ℕ) :
    SimpleGraph (layer G root i) where
  Adj u v := G.Adj u.1 v.1 ∧ HasEvenDetour G root i m u.1 v.1
  symm := ⟨fun u v h ↦ by
    rcases h with ⟨huv, q, hq, hlen, hinterior⟩
    refine ⟨huv.symm, q.reverse, hq.reverse, by simpa, ?_⟩
    intro x hx hxv hxu
    exact hinterior x (by simpa [Walk.support_reverse] using hx) hxu hxv⟩
  loopless := ⟨fun v h ↦ G.loopless.irrefl v.1 h.1⟩

/-- Every edge inside layer `i` belongs to one of the `i` detour graphs. -/
lemma induce_layer_le_iSup_detourGraph {G : SimpleGraph V} (hconn : G.Connected)
    (root : V) (i : ℕ) :
    G.induce (layer G root i) ≤ ⨆ m : Fin i, detourGraph G root i m := by
  intro u v huv
  have huv_val : (u : V) ≠ (v : V) := fun h ↦ huv.ne (Subtype.ext h)
  obtain ⟨m, hm, q, hq, hlen, hinterior⟩ :=
    exists_even_detour hconn u.property v.property huv_val
  rw [iSup_adj]
  refine ⟨⟨m, hm⟩, ?_⟩
  change G.Adj u.1 v.1 ∧ HasEvenDetour G root i m u.1 v.1
  exact ⟨huv, q, hq, hlen, hinterior⟩

/-- An uncountably chromatic layer has an uncountably chromatic detour class. -/
lemma exists_uncountably_chromatic_detourGraph {G : SimpleGraph V}
    (hconn : G.Connected) (root : V) (i : ℕ)
    (hi : IsUncountablyChromatic (G.induce (layer G root i))) :
    ∃ m : Fin i, IsUncountablyChromatic (detourGraph G root i m) :=
  exists_uncountably_chromatic_of_le_iSup
    (fun m : Fin i ↦ detourGraph G root i m)
    (induce_layer_le_iSup_detourGraph hconn root i) hi

/-! ## Replacing one edge of an even cycle -/

/-- The forgetful homomorphism from a detour graph to the original graph. -/
def detourGraphHom (G : SimpleGraph V) (root : V) (i m : ℕ) :
    detourGraph G root i m →g G where
  toFun v := v.1
  map_rel' h := h.1

/-- Replacing the first edge of a `2j`-cycle in the `m`-th detour graph by
its associated path produces a simple odd cycle of length `2 (m+j) + 1` in
the original graph. -/
lemma exists_odd_cycle_of_detour_cycle {G : SimpleGraph V} {root : V} {i m j : ℕ}
    {z : layer G root i} (c : (detourGraph G root i m).Walk z z)
    (hc : c.IsCycle) (hlen : c.length = 2 * j) :
    ∃ (v : V) (w : G.Walk v v), w.IsCycle ∧ w.length = 2 * (m + j) + 1 := by
  cases c with
  | nil => simp [Walk.isCycle_def] at hc
  | cons hadj p =>
      have hp : p.IsPath := (Walk.cons_isCycle_iff p hadj).mp hc |>.1
      have hp_len : p.length + 1 = 2 * j := by
        rw [← Walk.length_cons hadj p]
        exact hlen
      rcases hadj with ⟨hadjG, q, hq, hq_len, hq_interior⟩
      let f := detourGraphHom G root i m
      let pG := p.map f
      have hpG : pG.IsPath := hp.map Subtype.val_injective
      have hdisj : q.support.tail.Disjoint pG.support.tail := by
        rw [List.disjoint_left]
        intro x hxq hxp
        have hxq' : x ∈ q.support := List.mem_of_mem_tail hxq
        have hxu : x ≠ (z : V) := by
          have hn : ((z : V) :: q.support.tail).Nodup := by
            simpa only [q.cons_tail_support] using hq.support_nodup
          exact fun h ↦ (List.nodup_cons.mp hn).1 (h ▸ hxq)
        have hlt := hq_interior x hxq' hxu (by
          intro hx
          subst x
          have hn := hpG.support_nodup
          rw [← pG.cons_tail_support] at hn
          exact (List.nodup_cons.mp hn).1 hxp)
        rw [Walk.support_map] at hxp
        obtain ⟨y, hyp, hyx⟩ := List.mem_map.mp (List.mem_of_mem_tail hxp)
        have hy_layer : G.dist root (y : V) = i := y.property
        simp only [f, detourGraphHom] at hyx
        subst x
        change G.dist root (y : V) < i at hlt
        omega
      refine ⟨z, q.append pG, ?_, ?_⟩
      · exact hq.isCycle_append hpG hdisj (Or.inl (by omega))
      · have hlength : q.length + p.length = 2 * (m + j) + 1 := by omega
        calc
          (q.append pG).length = q.length + pG.length := Walk.length_append q pG
          _ = 2 * (m + j) + 1 := by simpa [pG] using hlength

/-! ## The Erdős--Hajnal finite-bipartite theorem -/

/-- A concrete copy of `K_(n,n)`: the two maps are automatically disjoint,
since a common value would create a loop. -/
def ContainsCompleteBipartite (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ l r : Fin n ↪ V, ∀ a b, G.Adj (l a) (r b)

/-- Common neighbors of the range of a finite embedding. -/
def commonNeighbors (G : SimpleGraph V) {n : ℕ} (f : Fin n ↪ V) : Set V :=
  {v | ∀ a, G.Adj (f a) v}

lemma commonNeighbors_finite_of_no_completeBipartite {G : SimpleGraph V} {n : ℕ}
    (hfree : ¬ ContainsCompleteBipartite G n) (f : Fin n ↪ V) :
    (commonNeighbors G f).Finite := by
  rw [← Set.finite_coe_iff]
  by_contra hinf
  letI : Infinite (commonNeighbors G f) := not_finite_iff_infinite.mp hinf
  let g₀ : Fin n ↪ commonNeighbors G f :=
    Fin.valEmbedding.trans (Infinite.natEmbedding (commonNeighbors G f))
  let g : Fin n ↪ V := g₀.trans (Function.Embedding.subtype _)
  apply hfree
  refine ⟨f, g, fun a b ↦ ?_⟩
  exact (g₀ b).property a

/-- One finitary closure step: adjoin the common neighbors of every embedded
`n`-set already contained in `A`. -/
def commonStep (G : SimpleGraph V) (n : ℕ) (A : Set V) : Set V :=
  A ∪ ⋃ f : Fin n ↪ A, commonNeighbors G (f.trans (Function.Embedding.subtype _))

lemma subset_commonStep (G : SimpleGraph V) (n : ℕ) (A : Set V) :
    A ⊆ commonStep G n A :=
  subset_union_left

lemma commonStep_mono (G : SimpleGraph V) (n : ℕ) : Monotone (commonStep G n) := by
  intro A B hAB x hx
  rcases hx with hx | hx
  · exact Or.inl (hAB hx)
  · right
    simp only [mem_iUnion] at hx ⊢
    obtain ⟨f, hxf⟩ := hx
    let e : A ↪ B := Set.embeddingOfSubset A B hAB
    refine ⟨f.trans e, ?_⟩
    exact hxf

lemma mk_commonStep_le {G : SimpleGraph V} {n : ℕ}
    (hfree : ¬ ContainsCompleteBipartite G n) (A : Set V) :
    Cardinal.mk (commonStep G n A) ≤ max (Cardinal.mk A) Cardinal.aleph0 := by
  let K : Cardinal := max (Cardinal.mk A) Cardinal.aleph0
  have hK : Cardinal.aleph0 ≤ K := le_max_right _ _
  have hindex : Cardinal.mk (Fin n ↪ A) ≤ K := by
    calc
      Cardinal.mk (Fin n ↪ A) ≤ Cardinal.mk (Fin n → A) :=
        Cardinal.mk_embedding_le_arrow _ _
      _ = Cardinal.mk A ^ (n : Cardinal) := by simp
      _ ≤ K := Cardinal.power_nat_le_max
  have hfiber : ∀ f : Fin n ↪ A,
      Cardinal.mk (commonNeighbors G (f.trans (Function.Embedding.subtype _))) ≤ K := by
    intro f
    exact (Cardinal.lt_aleph0_iff_set_finite.mpr
      (commonNeighbors_finite_of_no_completeBipartite hfree _)).le.trans hK
  have hunion : Cardinal.mk (⋃ f : Fin n ↪ A,
      commonNeighbors G (f.trans (Function.Embedding.subtype _))) ≤ K := by
    refine (Cardinal.mk_iUnion_le _).trans ?_
    refine (mul_le_mul' hindex (ciSup_le' hfiber)).trans ?_
    exact (Cardinal.mul_eq_self hK).le
  unfold commonStep
  refine (Cardinal.mk_union_le _ _).trans ?_
  exact (add_le_add (le_max_left _ _) hunion).trans (Cardinal.add_eq_self hK).le

/-- The closure obtained by iterating `commonStep` countably many times. -/
def commonClosure (G : SimpleGraph V) (n : ℕ) (A : Set V) : Set V :=
  ⋃ k : ℕ, (commonStep G n)^[k] A

lemma subset_commonClosure (G : SimpleGraph V) (n : ℕ) (A : Set V) :
    A ⊆ commonClosure G n A := by
  intro x hx
  rw [commonClosure, mem_iUnion]
  exact ⟨0, hx⟩

lemma commonStep_iterates_mono (G : SimpleGraph V) (n : ℕ) (A : Set V) :
    Monotone (fun k ↦ (commonStep G n)^[k] A) :=
  (commonStep_mono G n).monotone_iterate_of_le_map (subset_commonStep G n A)

lemma mk_commonStep_iterate_le {G : SimpleGraph V} {n : ℕ}
    (hfree : ¬ ContainsCompleteBipartite G n) (A : Set V) (k : ℕ) :
    Cardinal.mk ((commonStep G n)^[k] A) ≤ max (Cardinal.mk A) Cardinal.aleph0 := by
  let K : Cardinal := max (Cardinal.mk A) Cardinal.aleph0
  have hK : Cardinal.aleph0 ≤ K := le_max_right _ _
  induction k with
  | zero => exact le_max_left _ _
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact (mk_commonStep_le hfree _).trans (max_le ih hK)

lemma mk_commonClosure_le {G : SimpleGraph V} {n : ℕ}
    (hfree : ¬ ContainsCompleteBipartite G n) (A : Set V) :
    Cardinal.mk (commonClosure G n A) ≤ max (Cardinal.mk A) Cardinal.aleph0 := by
  let K : Cardinal := max (Cardinal.mk A) Cardinal.aleph0
  have hK : Cardinal.aleph0 ≤ K := le_max_right _ _
  unfold commonClosure
  have hUnion := Cardinal.mk_iUnion_le_lift
    (fun k : ℕ ↦ (commonStep G n)^[k] A)
  rw [Cardinal.lift_id'.{0, u}] at hUnion
  simp only [Cardinal.lift_id'.{0, u}] at hUnion
  have hNat : Cardinal.lift.{u} (Cardinal.mk ℕ) ≤ K := by simpa using hK
  have hiter : (⨆ k : ℕ, Cardinal.mk ((commonStep G n)^[k] A)) ≤ K :=
    ciSup_le' (mk_commonStep_iterate_le hfree A)
  exact hUnion.trans (Cardinal.mul_le_of_le hK hNat hiter)

/-- The countable iteration is closed under taking common neighbors of an
embedded `n`-set.  Finiteness of `Fin n` lets us put all generators in one
finite stage. -/
lemma commonNeighbors_subset_commonClosure {G : SimpleGraph V} {n : ℕ} (A : Set V)
    (f : Fin n ↪ commonClosure G n A) :
    commonNeighbors G (f.trans (Function.Embedding.subtype _)) ⊆
      commonClosure G n A := by
  classical
  have hfstage : ∀ a : Fin n, ∃ k : ℕ, (f a : V) ∈ (commonStep G n)^[k] A := by
    intro a
    simpa only [commonClosure, mem_iUnion] using (f a).property
  choose k hk using hfstage
  let K : ℕ := Finset.univ.sup k
  have hkK (a : Fin n) : k a ≤ K := by
    exact Finset.le_sup (f := k) (Finset.mem_univ a)
  let fK : Fin n ↪ ((commonStep G n)^[K] A) :=
    { toFun := fun a ↦
        ⟨f a, (commonStep_iterates_mono G n A (hkK a)) (hk a)⟩
      inj' := by
        intro a b hab
        apply f.injective
        have hv : (f a : V) = (f b : V) :=
          congrArg (fun z : ((commonStep G n)^[K] A) ↦ (z : V)) hab
        exact Subtype.ext hv }
  intro x hx
  have hxK : x ∈ commonNeighbors G
      (fK.trans (Function.Embedding.subtype _)) := by
    intro a
    exact hx a
  have hxstep : x ∈ commonStep G n ((commonStep G n)^[K] A) := by
    right
    rw [mem_iUnion]
    exact ⟨fK, hxK⟩
  rw [commonClosure, mem_iUnion]
  refine ⟨K + 1, ?_⟩
  simpa only [Function.iterate_succ_apply'] using hxstep

lemma commonClosure_mono (G : SimpleGraph V) (n : ℕ) :
    Monotone (commonClosure G n) := by
  intro A B hAB x hx
  rw [commonClosure, mem_iUnion] at hx ⊢
  obtain ⟨k, hx⟩ := hx
  exact ⟨k, ((commonStep_mono G n).iterate k hAB) hx⟩

/-- Finitarity of the closure at a limit: an element generated from the strict
initial segment below `a` is already generated from the closed initial segment
below some single `b < a`. -/
lemma mem_commonClosure_Iio_exists_Iic [LinearOrder V] {G : SimpleGraph V}
    {n : ℕ} (hn : 0 < n) {a x : V}
    (hx : x ∈ commonClosure G n (Iio a)) :
    ∃ b < a, x ∈ commonClosure G n (Iic b) := by
  classical
  rw [commonClosure, mem_iUnion] at hx
  obtain ⟨k, hx⟩ := hx
  induction k generalizing x with
  | zero =>
      refine ⟨x, hx, subset_commonClosure G n (Iic x) ?_⟩
      exact le_rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply'] at hx
      rcases hx with hx | hx
      · exact ih hx
      · simp only [mem_iUnion] at hx
        obtain ⟨f, hxf⟩ := hx
        have hgen : ∀ j : Fin n, ∃ b < a,
            (f j : V) ∈ commonClosure G n (Iic b) := by
          intro j
          exact ih (f j).property
        choose b hb_lt hb_mem using hgen
        letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
        have huniv : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty
        let bmax : V := Finset.univ.sup' huniv b
        have hb_le (j : Fin n) : b j ≤ bmax := by
          exact Finset.le_sup' b (Finset.mem_univ j)
        have hbmax_lt : bmax < a := by
          rw [Finset.sup'_lt_iff]
          intro j hj
          exact hb_lt j
        let fmax : Fin n ↪ commonClosure G n (Iic bmax) :=
          { toFun := fun j ↦
              ⟨f j, (commonClosure_mono G n
                (show Iic (b j) ⊆ Iic bmax by
                  intro y hy
                  exact hy.trans (hb_le j))) (hb_mem j)⟩
            inj' := by
              intro j₁ j₂ hj
              apply f.injective
              have hv : (f j₁ : V) = (f j₂ : V) :=
                congrArg (fun z : commonClosure G n (Iic bmax) ↦ (z : V)) hj
              exact Subtype.ext hv }
        refine ⟨bmax, hbmax_lt, ?_⟩
        apply commonNeighbors_subset_commonClosure (G := G) (A := Iic bmax) fmax
        intro j
        exact hxf j

/-- The first closed initial segment which generates a vertex. -/
noncomputable def closureRank [LinearOrder V] [WellFoundedLT V]
    (G : SimpleGraph V) (n : ℕ) (v : V) : V :=
  wellFounded_lt.min {a | v ∈ commonClosure G n (Iic a)}
    ⟨v, subset_commonClosure G n (Iic v) le_rfl⟩

lemma closureRank_mem [LinearOrder V] [WellFoundedLT V]
    (G : SimpleGraph V) (n : ℕ) (v : V) :
    v ∈ commonClosure G n (Iic (closureRank G n v)) :=
  by
    unfold closureRank
    exact wellFounded_lt.min_mem {a | v ∈ commonClosure G n (Iic a)}
      ⟨v, subset_commonClosure G n (Iic v) le_rfl⟩

lemma closureRank_le_of_mem [LinearOrder V] [WellFoundedLT V]
    (G : SimpleGraph V) (n : ℕ) {v a : V}
    (h : v ∈ commonClosure G n (Iic a)) :
    closureRank G n v ≤ a := by
  apply le_of_not_gt
  intro ha
  unfold closureRank at ha
  exact wellFounded_lt.not_lt_min {b | v ∈ commonClosure G n (Iic b)} h ha

lemma closureRank_not_mem_strict [LinearOrder V] [WellFoundedLT V]
    {G : SimpleGraph V} {n : ℕ} (hn : 0 < n) (v : V) :
    v ∉ commonClosure G n (Iio (closureRank G n v)) := by
  intro hv
  obtain ⟨b, hb, hvb⟩ := mem_commonClosure_Iio_exists_Iic hn hv
  exact (not_lt_of_ge (closureRank_le_of_mem G n hvb)) hb

/-- Vertices born at one closure rank. -/
def rankFiber [LinearOrder V] [WellFoundedLT V]
    (G : SimpleGraph V) (n : ℕ) (a : V) : Set V :=
  {v | closureRank G n v = a}

lemma rankFiber_subset_closedInitial [LinearOrder V] [WellFoundedLT V]
    (G : SimpleGraph V) (n : ℕ) (a : V) :
    rankFiber G n a ⊆ commonClosure G n (Iic a) := by
  intro v hv
  change closureRank G n v = a at hv
  rw [← hv]
  exact closureRank_mem G n v

lemma mk_rankFiber_lt [LinearOrder V] [WellFoundedLT V]
    {G : SimpleGraph V} {n : ℕ} (hfree : ¬ ContainsCompleteBipartite G n)
    (huncountable : Cardinal.aleph0 < Cardinal.mk V)
    (hord : (Cardinal.mk V).ord = typeLT V) (a : V) :
    Cardinal.mk (rankFiber G n a) < Cardinal.mk V := by
  have hIio : Cardinal.mk (Iio a) < Cardinal.mk V :=
    Cardinal.mk_Iio_lt a hord
  have hIic : Cardinal.mk (Iic a) < Cardinal.mk V := by
    rw [← Iio_insert]
    exact Cardinal.mk_insert_le.trans_lt
      (Cardinal.add_lt_of_lt huncountable.le hIio
        (Cardinal.one_lt_aleph0.trans huncountable))
  have hmax : max (Cardinal.mk (Iic a)) Cardinal.aleph0 < Cardinal.mk V :=
    max_lt hIic huncountable
  exact (Cardinal.mk_subtype_mono (rankFiber_subset_closedInitial G n a)).trans_lt
    ((mk_commonClosure_le hfree (Iic a)).trans_lt hmax)

/-- Cross-block neighbors which were born at an earlier closure rank. -/
def earlierCrossNeighbors [LinearOrder V] [WellFoundedLT V]
    (G : SimpleGraph V) (n : ℕ) (v : V) : Set V :=
  {w | closureRank G n w < closureRank G n v ∧ G.Adj w v}

lemma earlierCrossNeighbors_finite [LinearOrder V] [WellFoundedLT V]
    {G : SimpleGraph V} {n : ℕ} (hn : 0 < n) (v : V) :
    (earlierCrossNeighbors G n v).Finite := by
  rw [← Set.finite_coe_iff]
  by_contra hinf
  letI : Infinite (earlierCrossNeighbors G n v) := not_finite_iff_infinite.mp hinf
  let f : Fin n ↪ earlierCrossNeighbors G n v :=
    Fin.valEmbedding.trans (Infinite.natEmbedding (earlierCrossNeighbors G n v))
  let fcl : Fin n ↪ commonClosure G n (Iio (closureRank G n v)) :=
    { toFun := fun j ↦
        ⟨f j, commonClosure_mono G n
          (show Iic (closureRank G n (f j : V)) ⊆ Iio (closureRank G n v) by
            intro x hx
            exact lt_of_le_of_lt hx (f j).property.1)
          (closureRank_mem G n (f j : V))⟩
      inj' := by
        intro j₁ j₂ hj
        apply f.injective
        have hv : (f j₁ : V) = (f j₂ : V) :=
          congrArg
            (fun z : commonClosure G n (Iio (closureRank G n v)) ↦ (z : V)) hj
        exact Subtype.ext hv }
  have hvcommon : v ∈ commonNeighbors G
      (fcl.trans (Function.Embedding.subtype _)) := by
    intro j
    exact (f j).property.2
  exact closureRank_not_mem_strict hn v
    (commonNeighbors_subset_commonClosure (G := G)
      (A := Iio (closureRank G n v)) fcl hvcommon)

private noncomputable def finitePredecessorColorStep {r : V → V → Prop}
    (G : SimpleGraph V) (hfin : ∀ v, {w | r w v ∧ G.Adj w v}.Finite)
    (v : V) (rec : ∀ w, r w v → ℕ) : ℕ :=
  letI : Finite {w // r w v ∧ G.Adj w v} :=
    Set.finite_coe_iff.mpr (hfin v)
  letI : Fintype {w // r w v ∧ G.Adj w v} := Fintype.ofFinite _
  (Finset.univ.sup fun w : {w // r w v ∧ G.Adj w v} ↦ rec w.1 w.2.1) + 1

/-- Greedy natural-number coloring along a well-founded relation, assuming
that every vertex has only finitely many adjacent predecessors. -/
noncomputable def finitePredecessorColor {r : V → V → Prop} (hr : WellFounded r)
    (G : SimpleGraph V) (hfin : ∀ v, {w | r w v ∧ G.Adj w v}.Finite) : V → ℕ :=
  hr.fix (finitePredecessorColorStep G hfin)

lemma finitePredecessorColor_ne {r : V → V → Prop} (hr : WellFounded r)
    (G : SimpleGraph V) (hfin : ∀ v, {w | r w v ∧ G.Adj w v}.Finite)
    {u v : V} (huv : r u v) (hadj : G.Adj u v) :
    finitePredecessorColor hr G hfin u ≠ finitePredecessorColor hr G hfin v := by
  unfold finitePredecessorColor
  apply ne_of_lt
  conv_rhs => rw [WellFounded.fix_eq]
  unfold finitePredecessorColorStep
  letI : Finite {w // r w v ∧ G.Adj w v} :=
    Set.finite_coe_iff.mpr (hfin v)
  letI : Fintype {w // r w v ∧ G.Adj w v} := Fintype.ofFinite _
  exact Nat.lt_succ_of_le <| Finset.le_sup
    (f := fun w : {w // r w v ∧ G.Adj w v} ↦
      hr.fix (finitePredecessorColorStep G hfin) w.1)
    (show (⟨u, huv, hadj⟩ : {w // r w v ∧ G.Adj w v}) ∈ Finset.univ by simp)

def closureRankLT [LinearOrder V] [WellFoundedLT V]
    (G : SimpleGraph V) (n : ℕ) (u v : V) : Prop :=
  closureRank G n u < closureRank G n v

lemma closureRankLT_wf [LinearOrder V] [WellFoundedLT V]
    (G : SimpleGraph V) (n : ℕ) : WellFounded (closureRankLT G n) :=
  InvImage.wf (closureRank G n) wellFounded_lt

/-- A proper coloring of all edges joining distinct rank fibers. -/
noncomputable def crossFiberColor [LinearOrder V] [WellFoundedLT V]
    (G : SimpleGraph V) (n : ℕ) (hn : 0 < n) : V → ℕ :=
  finitePredecessorColor (closureRankLT_wf G n) G
    (earlierCrossNeighbors_finite (G := G) hn)

lemma crossFiberColor_ne [LinearOrder V] [WellFoundedLT V]
    (G : SimpleGraph V) (n : ℕ) (hn : 0 < n) {u v : V}
    (hrank : closureRank G n u < closureRank G n v) (hadj : G.Adj u v) :
    crossFiberColor G n hn u ≠ crossFiberColor G n hn v :=
  finitePredecessorColor_ne (closureRankLT_wf G n) G
    (earlierCrossNeighbors_finite (G := G) hn) hrank hadj

lemma nonempty_coloring_of_mk_le_aleph0 (G : SimpleGraph V)
    (hV : Cardinal.mk V ≤ Cardinal.aleph0) : Nonempty (G.Coloring ℕ) := by
  have he : Nonempty (V ↪ ℕ) := Cardinal.lift_mk_le'.mp (by simpa using hV)
  let e : V ↪ ℕ := Classical.choice he
  refine ⟨SimpleGraph.Coloring.mk e ?_⟩
  intro u v huv heq
  exact G.ne_of_adj huv (e.injective heq)

lemma no_completeBipartite_induce {G : SimpleGraph V} {n : ℕ}
    (hfree : ¬ ContainsCompleteBipartite G n) (S : Set V) :
    ¬ ContainsCompleteBipartite (G.induce S) n := by
  rintro ⟨l, r, hlr⟩
  apply hfree
  refine ⟨l.trans (Function.Embedding.subtype _),
    r.trans (Function.Embedding.subtype _), fun a b ↦ ?_⟩
  exact hlr a b

/-- Erdős--Hajnal: omitting one finite complete bipartite graph forces a
countable coloring.  The proof is by induction on the cardinality of the
vertex type, using the closure-rank blocks above. -/
theorem nonempty_coloring_of_no_completeBipartite {n : ℕ} (hn : 0 < n) :
    ∀ {V : Type u} (G : SimpleGraph V),
      ¬ ContainsCompleteBipartite G n → Nonempty (G.Coloring ℕ) := by
  intro V
  let P : Cardinal.{u} → Prop := fun c ↦
    ∀ (W : Type u), Cardinal.mk W = c → ∀ (G : SimpleGraph W),
      ¬ ContainsCompleteBipartite G n → Nonempty (G.Coloring ℕ)
  have hP : ∀ c : Cardinal.{u}, P c := by
    intro c
    induction c using WellFoundedLT.induction with
    | ind c ih =>
        intro W hW G hfree
        by_cases hcount : Cardinal.mk W ≤ Cardinal.aleph0
        · exact nonempty_coloring_of_mk_le_aleph0 G hcount
        · have huncountable : Cardinal.aleph0 < Cardinal.mk W := lt_of_not_ge hcount
          obtain ⟨r, hr, hord⟩ := Cardinal.exists_ord_eq W
          letI : IsWellOrder W r := hr
          letI : LinearOrder W := IsWellOrder.linearOrder r
          letI : WellFoundedLT W := ⟨hr.wf⟩
          have hord' : (Cardinal.mk W).ord = typeLT W := hord
          have hfiberColor (a : W) :
              Nonempty ((G.induce (rankFiber G n a)).Coloring ℕ) := by
            have hsmall := mk_rankFiber_lt hfree huncountable hord' a
            have hi := ih (Cardinal.mk (rankFiber G n a)) (hsmall.trans_eq hW)
            exact hi (rankFiber G n a) rfl (G.induce (rankFiber G n a))
              (no_completeBipartite_induce hfree _)
          let C : (a : W) → (G.induce (rankFiber G n a)).Coloring ℕ :=
            fun a ↦ Classical.choice (hfiberColor a)
          let D : W → W → ℕ := fun a v ↦
            if hv : v ∈ rankFiber G n a then C a ⟨v, hv⟩ else 0
          let color : W → ℕ := fun v ↦ Nat.pairEquiv
            (D (closureRank G n v) v, crossFiberColor G n hn v)
          refine ⟨SimpleGraph.Coloring.mk color ?_⟩
          intro v w hvw heq
          have hp := Nat.pairEquiv.injective heq
          by_cases hrank : closureRank G n v = closureRank G n w
          · have hv : v ∈ rankFiber G n (closureRank G n v) := rfl
            have hw : w ∈ rankFiber G n (closureRank G n v) := by
              exact hrank.symm
            have hlocal := (C (closureRank G n v)).valid
              (show (G.induce (rankFiber G n (closureRank G n v))).Adj
                ⟨v, hv⟩ ⟨w, hw⟩ from hvw)
            apply hlocal
            have hfst := congrArg Prod.fst hp
            change D (closureRank G n v) v = D (closureRank G n w) w at hfst
            have hDeq : D (closureRank G n v) v = D (closureRank G n v) w := by
              calc
                D (closureRank G n v) v = D (closureRank G n w) w := hfst
                _ = D (closureRank G n v) w :=
                  congrArg (fun a ↦ D a w) hrank.symm
            simpa only [D, dif_pos hv, dif_pos hw] using hDeq
          · have hcross : crossFiberColor G n hn v = crossFiberColor G n hn w :=
              congrArg Prod.snd hp
            rcases lt_or_gt_of_ne hrank with hlt | hgt
            · exact (crossFiberColor_ne G n hn hlt hvw) hcross
            · exact (crossFiberColor_ne G n hn hgt hvw.symm) hcross.symm
  exact hP (Cardinal.mk V) V rfl

/-! ## Even cycles in uncountably chromatic graphs -/

/-- The alternating vertices of a concrete `K_(j,j)` form a simple cycle of
length `2 * j`. -/
lemma exists_even_cycle_of_completeBipartite {G : SimpleGraph V} {j : ℕ}
    (hj : 2 ≤ j) (hK : ContainsCompleteBipartite G j) :
    ∃ (v : V) (w : G.Walk v v), w.IsCycle ∧ w.length = 2 * j := by
  rcases hK with ⟨l, r, hlr⟩
  have heven : Even (j * 2) := ⟨j, by omega⟩
  let idx : Fin (j * 2) → Fin j := fun x ↦ ⟨x.val / 2, by omega⟩
  let leftColor : Fin (j * 2) → Prop := fun x ↦ x.val % 2 = 0
  let f : Fin (j * 2) ↪ V :=
    ⟨fun x ↦ if leftColor x then l (idx x) else r (idx x), by
      intro x y hxy
      by_cases hx : leftColor x <;> by_cases hy : leftColor y
      · have hidx : idx x = idx y := l.injective (by simpa [hx, hy] using hxy)
        apply Fin.ext
        have hmodx : x.val % 2 = 0 := hx
        have hmody : y.val % 2 = 0 := hy
        have hdiv : x.val / 2 = y.val / 2 := congrArg Fin.val hidx
        omega
      · have hcross : G.Adj (l (idx x)) (r (idx y)) := hlr _ _
        have heq : l (idx x) = r (idx y) := by simpa [hx, hy] using hxy
        exact (hcross.ne heq).elim
      · have hcross : G.Adj (l (idx y)) (r (idx x)) := hlr _ _
        have heq : r (idx x) = l (idx y) := by simpa [hx, hy] using hxy
        exact (hcross.ne heq.symm).elim
      · have hidx : idx x = idx y := r.injective (by simpa [hx, hy] using hxy)
        apply Fin.ext
        have hmodx : x.val % 2 = 1 := by omega
        have hmody : y.val % 2 = 1 := by omega
        have hdiv : x.val / 2 = y.val / 2 := congrArg Fin.val hidx
        omega⟩
  let φ : cycleGraph (j * 2) →g G :=
    ⟨f, by
      intro x y hxy
      have hcolor := (cycleGraph.bicoloring_of_even (j * 2) heven).valid hxy
      change decide (leftColor x) ≠ decide (leftColor y) at hcolor
      by_cases hx : leftColor x <;> by_cases hy : leftColor y
      · exact (hcolor (by simp [hx, hy])).elim
      · change G.Adj (if leftColor x then l (idx x) else r (idx x))
          (if leftColor y then l (idx y) else r (idx y))
        simpa [hx, hy] using hlr (idx x) (idx y)
      · change G.Adj (if leftColor x then l (idx x) else r (idx x))
          (if leftColor y then l (idx y) else r (idx y))
        simpa [hx, hy] using (hlr (idx y) (idx x)).symm
      · exact (hcolor (by simp [hx, hy])).elim⟩
  have hcopy : cycleGraph (j * 2) ⊑ G := ⟨⟨φ, f.injective⟩⟩
  obtain ⟨v, w, hw, hlen⟩ :=
    (cycleGraph_isContained_iff (n := j * 2) (by omega)).mp hcopy
  exact ⟨v, w, hw, by omega⟩

/-- Every uncountably chromatic graph contains a simple cycle of each even
length at least four. -/
lemma exists_even_cycle_of_uncountably_chromatic {G : SimpleGraph V}
    (hG : IsUncountablyChromatic G) {j : ℕ} (hj : 2 ≤ j) :
    ∃ (v : V) (w : G.Walk v v), w.IsCycle ∧ w.length = 2 * j := by
  have hK : ContainsCompleteBipartite G j := by
    by_contra hfree
    exact (isUncountablyChromatic_iff_not_nonempty.mp hG)
      (nonempty_coloring_of_no_completeBipartite (by omega) G hfree)
  exact exists_even_cycle_of_completeBipartite hj hK

/-! ## Assembly of the Erdős--Hajnal--Shelah argument -/

/-- The theorem for a connected graph.  The threshold is two more than the
index of the uncountably chromatic detour class. -/
lemma eventually_odd_cycles_of_connected {G : SimpleGraph V}
    (hconn : G.Connected) (hG : IsUncountablyChromatic G) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      ∃ (v : V) (w : G.Walk v v), w.IsCycle ∧ w.length = 2 * k + 1 := by
  let root : V := Classical.choice hconn.nonempty
  obtain ⟨i, hi⟩ := exists_uncountably_chromatic_layer hconn hG root
  obtain ⟨m, hm⟩ := exists_uncountably_chromatic_detourGraph hconn root i hi
  refine ⟨m.val + 2, fun k hk ↦ ?_⟩
  let j := k - m.val
  have hj : 2 ≤ j := by omega
  obtain ⟨z, c, hc, hlen⟩ :=
    exists_even_cycle_of_uncountably_chromatic hm hj
  obtain ⟨v, w, hw, hwlen⟩ :=
    exists_odd_cycle_of_detour_cycle c hc hlen
  refine ⟨v, w, hw, ?_⟩
  omega

end

end Erdos594

/-- Erdős Problem 594: every graph without a countable coloring contains a
cycle of every sufficiently large odd length. -/
theorem erdos_594 :
    ∀ (V : Type) (G : SimpleGraph V), IsEmpty (G.Coloring ℕ) →
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
        ∃ (v : V) (w : G.Walk v v), w.IsCycle ∧ w.length = 2 * k + 1 := by
  intro V G hG
  obtain ⟨c, hc⟩ := Erdos594.exists_uncountably_chromatic_component
    (G := G) hG
  obtain ⟨N, hN⟩ := Erdos594.eventually_odd_cycles_of_connected
    c.connected_toSimpleGraph hc
  refine ⟨N, fun k hk ↦ ?_⟩
  obtain ⟨v, w, hw, hlen⟩ := hN k hk
  let f := c.toSimpleGraph_hom
  refine ⟨f v, w.map f, hw.map Subtype.val_injective, ?_⟩
  simpa [f] using hlen

#print axioms erdos_594
