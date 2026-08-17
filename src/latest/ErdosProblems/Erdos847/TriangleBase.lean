/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos846

/-!
# The triangle hypergraph used as the first finite model for Erdős 847

The vertices are the (increasingly oriented) edges of a complete graph.  Three
vertices form a hyperedge when the corresponding graph edges are the boundary
of a graph triangle.  This file records the three elementary properties of
this model: its finite Ramsey property, the max-cut half-density estimate, and
its linearity (hence, in particular, exclusion of `K₄⁽³⁾` minus an edge).
-/

namespace Erdos847TriangleBase

open Erdos846
open scoped BigOperators

/-- The increasingly oriented edges of the complete graph on `Fin N`, written
as pairs of natural numbers so that we can directly reuse `Erdos846`'s Ramsey
and max-cut arguments. -/
def vertices (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range N).product (Finset.range N)).filter fun e ↦ e.1 < e.2

@[simp] lemma mem_vertices {N : ℕ} {e : ℕ × ℕ} :
    e ∈ vertices N ↔ e.1 < e.2 ∧ e.2 < N := by
  rcases e with ⟨a, b⟩
  simp [vertices]
  omega

/-- Hyperedges are triples of graph edges forming a graph triangle. -/
abbrev IsHyperedge := Erdos846.IsTriangle

/-- The complete-graph triangle hypergraph is Ramsey: for every number of
colors, one sufficiently large finite base has a monochromatic hyperedge. -/
theorem exists_monochromatic_hyperedge (r : ℕ) :
    ∃ N : ℕ, ∀ color : (ℕ × ℕ) → Fin r,
      ∃ e₀ ∈ vertices N, ∃ e₁ ∈ vertices N, ∃ e₂ ∈ vertices N,
        e₀ ≠ e₁ ∧ e₀ ≠ e₂ ∧ e₁ ≠ e₂ ∧
          IsHyperedge e₀ e₁ e₂ ∧
          color e₀ = color e₁ ∧ color e₁ = color e₂ := by
  obtain ⟨N, hN⟩ := Erdos846.finite_ramsey r
  refine ⟨N, fun color ↦ ?_⟩
  obtain ⟨i, j, k, hij, hjk, hkN, hc₀, hc₁⟩ := hN color
  refine ⟨(i, j), ?_, (j, k), ?_, (i, k), ?_, ?_, ?_, ?_, ?_, hc₀, hc₁⟩
  · exact mem_vertices.mpr ⟨hij, lt_trans hjk hkN⟩
  · exact mem_vertices.mpr ⟨hjk, hkN⟩
  · exact mem_vertices.mpr ⟨lt_trans hij hjk, hkN⟩
  · intro h
    have := congrArg Prod.fst h
    simp at this
    omega
  · intro h
    have := congrArg Prod.snd h
    simp at this
    omega
  · intro h
    have := congrArg Prod.fst h
    simp at this
    omega
  · exact ⟨i, j, k, hij, hjk, rfl⟩

/-- The same Ramsey statement for a coloring whose domain is exactly the
finite vertex set (rather than an ambient coloring of all natural pairs). -/
theorem exists_monochromatic_hyperedge_on_vertices (r : ℕ) :
    ∃ N : ℕ, ∀ color : {e // e ∈ vertices N} → Fin r,
      ∃ e₀ e₁ e₂ : {e // e ∈ vertices N},
        e₀ ≠ e₁ ∧ e₀ ≠ e₂ ∧ e₁ ≠ e₂ ∧
          IsHyperedge e₀.1 e₁.1 e₂.1 ∧
          color e₀ = color e₁ ∧ color e₁ = color e₂ := by
  obtain ⟨N, hN⟩ := exists_monochromatic_hyperedge r
  refine ⟨N + 2, fun color ↦ ?_⟩
  have hdefault : (0, 1) ∈ vertices (N + 2) := mem_vertices.mpr ⟨by omega, by omega⟩
  let defaultVertex : {e // e ∈ vertices (N + 2)} := ⟨(0, 1), hdefault⟩
  let ambientColor : (ℕ × ℕ) → Fin r := fun e ↦
    if he : e ∈ vertices (N + 2) then color ⟨e, he⟩ else color defaultVertex
  obtain ⟨e₀, he₀, e₁, he₁, e₂, he₂, h₀₁, h₀₂, h₁₂, htri, hc₀, hc₁⟩ := hN ambientColor
  have he₀' : e₀ ∈ vertices (N + 2) := by
    have he := mem_vertices.mp he₀
    exact mem_vertices.mpr ⟨he.1, lt_trans he.2 (by omega)⟩
  have he₁' : e₁ ∈ vertices (N + 2) := by
    have he := mem_vertices.mp he₁
    exact mem_vertices.mpr ⟨he.1, lt_trans he.2 (by omega)⟩
  have he₂' : e₂ ∈ vertices (N + 2) := by
    have he := mem_vertices.mp he₂
    exact mem_vertices.mpr ⟨he.1, lt_trans he.2 (by omega)⟩
  refine ⟨⟨e₀, he₀'⟩, ⟨e₁, he₁'⟩, ⟨e₂, he₂'⟩, ?_, ?_, ?_, htri, ?_, ?_⟩
  · intro h
    exact h₀₁ (congrArg Subtype.val h)
  · intro h
    exact h₀₂ (congrArg Subtype.val h)
  · intro h
    exact h₁₂ (congrArg Subtype.val h)
  · dsimp [ambientColor] at hc₀
    rw [dif_pos he₀', dif_pos he₁'] at hc₀
    exact hc₀
  · dsimp [ambientColor] at hc₁
    rw [dif_pos he₁', dif_pos he₂'] at hc₁
    exact hc₁

/-- Every family of base edges has a triangle-free subfamily containing at
least half its members.  This is the ordinary maximum-cut argument. -/
theorem exists_half_triangleFree_subset {N : ℕ} (S : Finset (ℕ × ℕ))
    (hS : S ⊆ vertices N) :
    ∃ C ⊆ S, 2 * C.card ≥ S.card ∧
      ∀ e₀ ∈ C, ∀ e₁ ∈ C, ∀ e₂ ∈ C,
        e₀ ≠ e₁ → e₀ ≠ e₂ → e₁ ≠ e₂ → ¬ IsHyperedge e₀ e₁ e₂ := by
  have hlt : ∀ e ∈ S, e.1 < e.2 := fun e he ↦ (mem_vertices.mp (hS he)).1
  obtain ⟨C, hCS, hhalf, hfree⟩ := Erdos846.mantel_half S hlt
  refine ⟨C, hCS, ?_, hfree⟩
  have hhalf' : (S.card : ℝ) ≤ 2 * C.card := by linarith
  exact_mod_cast hhalf'

/-- Weighted form of the max-cut estimate, with an explicit bound on all
endpoints.  The induction assigns the last graph vertex to whichever side
captures at least half of the total incident weight. -/
private theorem weighted_maxCut_bounded (n : ℕ) (S : Finset (ℕ × ℕ))
    (weight : (ℕ × ℕ) → ℕ)
    (hne : ∀ e ∈ S, e.1 ≠ e.2)
    (hbound : ∀ e ∈ S, e.1 < n ∧ e.2 < n) :
    ∃ cut : ℕ → Bool,
      2 * ∑ e ∈ S.filter (fun e ↦ cut e.1 ≠ cut e.2), weight e ≥
        ∑ e ∈ S, weight e := by
  induction n generalizing S with
  | zero =>
      refine ⟨fun _ ↦ true, ?_⟩
      have hS0 : S = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro e he
        exact Nat.not_lt_zero e.1 (hbound e he).1
      simp [hS0]
  | succ n ih =>
      let old := S.filter (fun e ↦ e.1 < n ∧ e.2 < n)
      let fresh := S.filter (fun e ↦ ¬ (e.1 < n ∧ e.2 < n))
      have hold_bound : ∀ e ∈ old, e.1 < n ∧ e.2 < n := by
        intro e he
        exact (Finset.mem_filter.mp he).2
      have hold_ne : ∀ e ∈ old, e.1 ≠ e.2 := by
        intro e he
        exact hne e (Finset.mem_filter.mp he).1
      obtain ⟨cut, hcut⟩ := ih old hold_ne hold_bound
      have htotal :
          (∑ e ∈ S, weight e) =
            (∑ e ∈ old, weight e) + ∑ e ∈ fresh, weight e := by
        simpa [old, fresh] using
          (Finset.sum_filter_add_sum_filter_not S
            (fun e : ℕ × ℕ ↦ e.1 < n ∧ e.2 < n) weight).symm
      have hsplit (g : ℕ → Bool) :
          (∑ e ∈ S.filter (fun e ↦ g e.1 ≠ g e.2), weight e) =
            (∑ e ∈ old.filter (fun e ↦ g e.1 ≠ g e.2), weight e) +
              ∑ e ∈ fresh.filter (fun e ↦ g e.1 ≠ g e.2), weight e := by
        let p : ℕ × ℕ → Prop := fun e ↦ e.1 < n ∧ e.2 < n
        let q : ℕ × ℕ → Prop := fun e ↦ g e.1 ≠ g e.2
        have hpartition := Finset.sum_filter_add_sum_filter_not (S.filter q) p weight
        have hleft : (S.filter q).filter p = old.filter q := by
          ext e
          simp [old, p, q, and_left_comm, and_assoc, and_comm]
        have hright : (S.filter q).filter (fun e ↦ ¬ p e) = fresh.filter q := by
          ext e
          simp [fresh, p, q, and_assoc, and_comm]
        rw [hleft, hright] at hpartition
        exact hpartition.symm
      let cutTrue := fun x ↦ if x = n then true else cut x
      let cutFalse := fun x ↦ if x = n then false else cut x
      have htrue_old :
          (∑ e ∈ old.filter (fun e ↦ cutTrue e.1 ≠ cutTrue e.2), weight e) =
            ∑ e ∈ old.filter (fun e ↦ cut e.1 ≠ cut e.2), weight e := by
        have hfilters :
            old.filter (fun e ↦ cutTrue e.1 ≠ cutTrue e.2) =
              old.filter (fun e ↦ cut e.1 ≠ cut e.2) := by
          apply Finset.filter_congr
          intro e he
          have heb := hold_bound e he
          simp [cutTrue, Nat.ne_of_lt heb.1, Nat.ne_of_lt heb.2]
        rw [hfilters]
      have hfalse_old :
          (∑ e ∈ old.filter (fun e ↦ cutFalse e.1 ≠ cutFalse e.2), weight e) =
            ∑ e ∈ old.filter (fun e ↦ cut e.1 ≠ cut e.2), weight e := by
        have hfilters :
            old.filter (fun e ↦ cutFalse e.1 ≠ cutFalse e.2) =
              old.filter (fun e ↦ cut e.1 ≠ cut e.2) := by
          apply Finset.filter_congr
          intro e he
          have heb := hold_bound e he
          simp [cutFalse, Nat.ne_of_lt heb.1, Nat.ne_of_lt heb.2]
        rw [hfilters]
      have hfresh_complement :
          fresh.filter (fun e ↦ cutFalse e.1 ≠ cutFalse e.2) =
            fresh.filter (fun e ↦ ¬ (cutTrue e.1 ≠ cutTrue e.2)) := by
        apply Finset.filter_congr
        intro e he
        have heS : e ∈ S := (Finset.mem_filter.mp he).1
        have hnot : ¬ (e.1 < n ∧ e.2 < n) := (Finset.mem_filter.mp he).2
        have hb := hbound e heS
        have hneq := hne e heS
        have hcases : (e.1 = n ∧ e.2 < n) ∨ (e.1 < n ∧ e.2 = n) := by omega
        rcases hcases with h | h
        · cases hcut2 : cut e.2 <;>
            simp [cutTrue, cutFalse, h.1, Nat.ne_of_lt h.2, hcut2]
        · cases hcut1 : cut e.1 <;>
            simp [cutTrue, cutFalse, Nat.ne_of_lt h.1, h.2, hcut1]
      have hfresh_sum :
          (∑ e ∈ fresh.filter (fun e ↦ cutTrue e.1 ≠ cutTrue e.2), weight e) +
              ∑ e ∈ fresh.filter (fun e ↦ cutFalse e.1 ≠ cutFalse e.2), weight e =
            ∑ e ∈ fresh, weight e := by
        rw [hfresh_complement]
        exact Finset.sum_filter_add_sum_filter_not fresh
          (fun e ↦ cutTrue e.1 ≠ cutTrue e.2) weight
      have hone :
          2 * (∑ e ∈ fresh.filter (fun e ↦ cutTrue e.1 ≠ cutTrue e.2), weight e) ≥
              ∑ e ∈ fresh, weight e ∨
            2 * (∑ e ∈ fresh.filter (fun e ↦ cutFalse e.1 ≠ cutFalse e.2), weight e) ≥
              ∑ e ∈ fresh, weight e := by
        omega
      rcases hone with htrue | hfalse
      · refine ⟨cutTrue, ?_⟩
        rw [hsplit cutTrue, htotal, htrue_old]
        omega
      · refine ⟨cutFalse, ?_⟩
        rw [hsplit cutFalse, htotal, hfalse_old]
        omega

/-- Every finite naturally weighted graph admits a cut containing at least half
of its total edge weight. -/
theorem exists_weighted_cut (S : Finset (ℕ × ℕ)) (weight : (ℕ × ℕ) → ℕ)
    (hne : ∀ e ∈ S, e.1 ≠ e.2) :
    ∃ cut : ℕ → Bool,
      2 * ∑ e ∈ S.filter (fun e ↦ cut e.1 ≠ cut e.2), weight e ≥
        ∑ e ∈ S, weight e := by
  let n := S.sup (fun e ↦ max e.1 e.2) + 1
  have hbound : ∀ e ∈ S, e.1 < n ∧ e.2 < n := by
    intro e he
    have hle := S.le_sup (f := fun e ↦ max e.1 e.2) he
    dsimp [n]
    omega
  exact weighted_maxCut_bounded n S weight hne hbound

/-- Weighted half-density in the formulation used for the hypergraph: the
chosen crossing edges are triangle-free. -/
theorem exists_half_weight_triangleFree_subset {N : ℕ} (S : Finset (ℕ × ℕ))
    (hS : S ⊆ vertices N) (weight : (ℕ × ℕ) → ℕ) :
    ∃ C ⊆ S,
      2 * (∑ e ∈ C, weight e) ≥ ∑ e ∈ S, weight e ∧
        ∀ e₀ ∈ C, ∀ e₁ ∈ C, ∀ e₂ ∈ C,
          e₀ ≠ e₁ → e₀ ≠ e₂ → e₁ ≠ e₂ → ¬ IsHyperedge e₀ e₁ e₂ := by
  have hne : ∀ e ∈ S, e.1 ≠ e.2 := by
    intro e he
    exact ne_of_lt (mem_vertices.mp (hS he)).1
  obtain ⟨cut, hcut⟩ := exists_weighted_cut S weight hne
  let C := S.filter (fun e ↦ cut e.1 ≠ cut e.2)
  refine ⟨C, Finset.filter_subset _ _, ?_, ?_⟩
  · exact hcut
  · apply Erdos846.bipartite_is_triangle_free C
        {x | cut x = true} {x | cut x = false}
    · simp [Set.disjoint_left]
    · intro e he
      have hcross : cut e.1 ≠ cut e.2 := (Finset.mem_filter.mp he).2
      cases h₁ : cut e.1 <;> cases h₂ : cut e.2 <;> simp_all

/-- The triangle hypergraph is linear: two hyperedges which share two vertices
have the same third vertex. -/
theorem third_edge_unique {a b c d : ℕ × ℕ} (hab : a ≠ b)
    (habc : IsHyperedge a b c) (habd : IsHyperedge a b d) : c = d := by
  rcases habc with ⟨i, j, k, hij, hjk, hijk⟩
  rcases habd with ⟨p, q, r, hpq, hqr, hpqr⟩
  have hijkSet := hijk
  have hpqrSet := hpqr
  simp only [Set.ext_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hijk hpqr
  have ha₁ : a = (i, j) ∨ a = (j, k) ∨ a = (i, k) := (hijk a).mp (by simp)
  have hb₁ : b = (i, j) ∨ b = (j, k) ∨ b = (i, k) := (hijk b).mp (by simp)
  have ha₂ : a = (p, q) ∨ a = (q, r) ∨ a = (p, r) := (hpqr a).mp (by simp)
  have hb₂ : b = (p, q) ∨ b = (q, r) ∨ b = (p, r) := (hpqr b).mp (by simp)
  have hcanonCard :
      ({(i, j), (j, k), (i, k)} : Set (ℕ × ℕ)).encard = 3 := by
    apply Set.encard_eq_three.mpr
    refine ⟨(i, j), (j, k), (i, k), ?_, ?_, ?_, rfl⟩
    all_goals intro h; simp only [Prod.mk.injEq] at h; omega
  have habcCard : ({a, b, c} : Set (ℕ × ℕ)).encard = 3 := by
    rw [hijkSet]
    exact hcanonCard
  have hca : c ≠ a := by
    intro h
    subst c
    have : ({b, a} : Set (ℕ × ℕ)).encard = 3 := by simpa using habcCard
    rw [Set.encard_pair hab.symm] at this
    norm_num at this
  have hcb : c ≠ b := by
    intro h
    subst c
    have : ({a, b} : Set (ℕ × ℕ)).encard = 3 := by simpa using habcCard
    rw [Set.encard_pair hab] at this
    norm_num at this
  have hcanonEq :
      ({(i, j), (j, k), (i, k)} : Set (ℕ × ℕ)) =
        {(p, q), (q, r), (p, r)} := by
    rcases ha₁ with ha₁ | ha₁ | ha₁ <;>
      rcases hb₁ with hb₁ | hb₁ | hb₁ <;>
      rcases ha₂ with ha₂ | ha₂ | ha₂ <;>
      rcases hb₂ with hb₂ | hb₂ | hb₂ <;>
      simp_all [Prod.ext_iff] <;> omega
  have habcd : ({a, b, c} : Set (ℕ × ℕ)) = {a, b, d} :=
    hijkSet.trans (hcanonEq.trans hpqrSet.symm)
  have hcMem : c ∈ ({a, b, d} : Set (ℕ × ℕ)) := habcd.subset (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcMem
  rcases hcMem with h | h | h
  · exact (hca h).elim
  · exact (hcb h).elim
  · exact h

/-- The hyperedge relation depends only on the underlying three-element set,
not on the order in which the three graph edges are listed. -/
theorem isHyperedge_of_set_eq {a b c x y z : ℕ × ℕ}
    (h : IsHyperedge a b c)
    (hs : ({x, y, z} : Set (ℕ × ℕ)) = {a, b, c}) :
    IsHyperedge x y z := by
  rcases h with ⟨i, j, k, hij, hjk, hset⟩
  exact ⟨i, j, k, hij, hjk, hs.trans hset⟩

/-- Recenter a hyperedge at any two distinct vertices it contains. -/
theorem hyperedge_recenter {a b c x y : ℕ × ℕ}
    (h : IsHyperedge a b c)
    (hx : x ∈ ({a, b, c} : Set (ℕ × ℕ)))
    (hy : y ∈ ({a, b, c} : Set (ℕ × ℕ))) (hxy : x ≠ y) :
    ∃ z, IsHyperedge x y z ∧
      ({a, b, c} : Set (ℕ × ℕ)) = {x, y, z} := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl
  · rcases hy with rfl | rfl | rfl
    · exact (hxy rfl).elim
    · refine ⟨c, isHyperedge_of_set_eq h ?_, ?_⟩ <;>
        ext u <;> simp [or_comm, or_left_comm]
    · refine ⟨b, isHyperedge_of_set_eq h ?_, ?_⟩ <;>
        ext u <;> simp [or_comm, or_left_comm]
  · rcases hy with rfl | rfl | rfl
    · refine ⟨c, isHyperedge_of_set_eq h ?_, ?_⟩ <;>
        ext u <;> simp [or_comm, or_left_comm]
    · exact (hxy rfl).elim
    · refine ⟨a, isHyperedge_of_set_eq h ?_, ?_⟩ <;>
        ext u <;> simp [or_comm, or_left_comm]
  · rcases hy with rfl | rfl | rfl
    · refine ⟨b, isHyperedge_of_set_eq h ?_, ?_⟩ <;>
        ext u <;> simp [or_comm, or_left_comm]
    · refine ⟨a, isHyperedge_of_set_eq h ?_, ?_⟩ <;>
        ext u <;> simp [or_comm, or_left_comm]
    · exact (hxy rfl).elim

/-- A finite set of graph edges is a hyperedge of the triangle hypergraph. -/
def IsHyperedgeSet (E : Finset (ℕ × ℕ)) : Prop :=
  ∃ a b c, IsHyperedge a b c ∧ E = {a, b, c}

/-- `ThreeGraph.Linear`-style formulation: two distinct hyperedge-sets intersect
in at most one vertex. -/
theorem hyperedgeSets_linear {E F : Finset (ℕ × ℕ)}
    (hE : IsHyperedgeSet E) (hF : IsHyperedgeSet F) (hEF : E ≠ F) :
    (E ∩ F).card ≤ 1 := by
  by_contra hcard
  have hone : 1 < (E ∩ F).card := by omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hone
  have hxE : x ∈ E := (Finset.mem_inter.mp hx).1
  have hxF : x ∈ F := (Finset.mem_inter.mp hx).2
  have hyE : y ∈ E := (Finset.mem_inter.mp hy).1
  have hyF : y ∈ F := (Finset.mem_inter.mp hy).2
  rcases hE with ⟨a, b, c, habc, rfl⟩
  rcases hF with ⟨p, q, r, hpqr, rfl⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxE hxF hyE hyF
  have hxESet : x ∈ ({a, b, c} : Set (ℕ × ℕ)) := by simpa using hxE
  have hyESet : y ∈ ({a, b, c} : Set (ℕ × ℕ)) := by simpa using hyE
  have hxFSet : x ∈ ({p, q, r} : Set (ℕ × ℕ)) := by simpa using hxF
  have hyFSet : y ∈ ({p, q, r} : Set (ℕ × ℕ)) := by simpa using hyF
  obtain ⟨z, hxyz, hEset⟩ := hyperedge_recenter habc hxESet hyESet hxy
  obtain ⟨w, hxyw, hFset⟩ := hyperedge_recenter hpqr hxFSet hyFSet hxy
  have hzw : z = w := third_edge_unique hxy hxyz hxyw
  apply hEF
  apply Finset.ext
  intro u
  simp only [Finset.mem_insert, Finset.mem_singleton]
  have hmemE := Set.ext_iff.mp hEset u
  have hmemF := Set.ext_iff.mp hFset u
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmemE hmemF
  rw [hmemE, hmemF, hzw]

/-- In particular, four distinct vertices cannot span three of the four
possible triples, i.e. the hypergraph is `K₄⁽³⁾`-minus-free. -/
theorem k4Three_minus_free {a b c d : ℕ × ℕ}
    (hab : a ≠ b) (hcd : c ≠ d) :
    ¬ (IsHyperedge a b c ∧ IsHyperedge a b d ∧ IsHyperedge a c d) := by
  rintro ⟨habc, habd, _⟩
  exact hcd (third_edge_unique hab habc habd)

end Erdos847TriangleBase
