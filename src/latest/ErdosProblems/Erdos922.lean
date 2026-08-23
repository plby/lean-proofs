/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 922.
https://www.erdosproblems.com/forum/thread/922

Informal authors:
- Jon Folkman

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos922.md
-/
import Mathlib

/-!
# Erdős Problem 922

This file formalizes Folkman's hereditary independence-number bound and
deduces the affirmative answer to Erdős Problem 922.  A detailed mathematical
proof and Leanization guide are in `tex/922.tex`.
-/

open SimpleGraph
open scoped ENat

namespace Erdos922

universe u

/-- The hypothesis in Problem 922, stated literally for every (not
necessarily induced or spanning) subgraph.  The inequality is the integral
form of `|I| ≥ (|V(H)| - k) / 2`. -/
def HasLargeIndependentSets {V : Type u} [Finite V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ H : G.Subgraph, ∃ I : Finset H.verts,
    H.coe.IsIndepSet I ∧ H.verts.ncard ≤ 2 * I.card + k

/-- The equivalent formulation on finite induced vertex sets. -/
def HasLargeIndependentSetsOnFinsets {V : Type u}
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ S : Finset V, ∃ I : Finset V,
    I ⊆ S ∧ G.IsIndepSet I ∧ S.card ≤ 2 * I.card + k

/-- The literal subgraph hypothesis supplies an independent set in every
finite induced vertex set. -/
theorem HasLargeIndependentSets.onFinsets {V : Type u} [Finite V]
    {G : SimpleGraph V} {k : ℕ} (h : HasLargeIndependentSets G k) :
    HasLargeIndependentSetsOnFinsets G k := by
  classical
  intro S
  let H : G.Subgraph := (⊤ : G.Subgraph).induce (↑S : Set V)
  obtain ⟨J, hJ, hcard⟩ := h H
  let I : Finset V := J.map ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨I, ?_, ?_, ?_⟩
  · intro v hv
    simp only [I, Finset.mem_map, Function.Embedding.coeFn_mk] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact w.property
  · have himage : G.IsIndepSet (Subtype.val '' (↑J : Set H.verts)) := by
      exact (SimpleGraph.isIndepSet_induce (G := G)).mp hJ
    simpa only [I, Finset.coe_map, Function.Embedding.coeFn_mk] using himage
  · simpa only [H, SimpleGraph.Subgraph.induce_verts, Set.ncard_coe_finset,
      I, Finset.card_map] using hcard

/-- The induced-finset formulation also implies the literal hypothesis for
arbitrary edge-deleted subgraphs. -/
theorem hasLargeIndependentSets_iff_onFinsets {V : Type u} [Finite V]
    {G : SimpleGraph V} {k : ℕ} :
    HasLargeIndependentSets G k ↔ HasLargeIndependentSetsOnFinsets G k := by
  classical
  refine ⟨HasLargeIndependentSets.onFinsets, ?_⟩
  intro h H
  letI : Fintype H.verts := Fintype.ofFinite H.verts
  let S : Finset V := H.verts.toFinset
  obtain ⟨I, hIS, hI, hcard⟩ := h S
  let J : Finset H.verts := I.subtype (fun v ↦ v ∈ H.verts)
  refine ⟨J, ?_, ?_⟩
  · rw [SimpleGraph.isIndepSet_iff]
    intro a ha b hb hab
    have haI : a.1 ∈ I := by
      change a ∈ J at ha
      simpa only [J, Finset.mem_subtype] using ha
    have hbI : b.1 ∈ I := by
      change b ∈ J at hb
      simpa only [J, Finset.mem_subtype] using hb
    exact fun hAdj ↦ hI haI hbI (Subtype.coe_ne_coe.mpr hab)
      (H.coe_adj_sub a b hAdj)
  · have hIfilter : I.filter (fun v ↦ v ∈ H.verts) = I := by
      exact Finset.filter_eq_self.mpr fun v hv ↦ by
        have : v ∈ S := hIS hv
        simpa only [S, Set.mem_toFinset] using this
    have hJcard : J.card = I.card := by
      simpa only [J, Finset.card_subtype, hIfilter]
    rw [Set.ncard_eq_toFinset_card']
    simpa only [S, hJcard] using hcard

/-- The independence number restricted to the finite vertex set `S`. -/
noncomputable def alphaOn {V : Type u} (G : SimpleGraph V) (S : Finset V) : ℕ := by
  classical
  exact Nat.findGreatest
    (fun n ↦ ∃ I : Finset V, I ⊆ S ∧ G.IsIndepSet I ∧ I.card = n) S.card

/-- A largest independent subset witnessing `alphaOn`. -/
theorem exists_maximum_independent_subset {V : Type u}
    (G : SimpleGraph V) (S : Finset V) :
    ∃ I : Finset V, I ⊆ S ∧ G.IsIndepSet I ∧ I.card = alphaOn G S := by
  classical
  unfold alphaOn
  apply Nat.findGreatest_spec
    (P := fun n ↦ ∃ I : Finset V, I ⊆ S ∧ G.IsIndepSet I ∧ I.card = n)
    (m := 0) (Nat.zero_le _)
  exact ⟨∅, by simp⟩

theorem alphaOn_le_card {V : Type u} (G : SimpleGraph V) (S : Finset V) :
    alphaOn G S ≤ S.card := by
  classical
  unfold alphaOn
  exact Nat.findGreatest_le _

/-- Every independent subset has cardinality at most `alphaOn`. -/
theorem card_le_alphaOn {V : Type u} {G : SimpleGraph V}
    {I S : Finset V} (hIS : I ⊆ S) (hI : G.IsIndepSet I) :
    I.card ≤ alphaOn G S := by
  classical
  unfold alphaOn
  exact Nat.le_findGreatest (Finset.card_le_card hIS) ⟨I, hIS, hI, rfl⟩

@[simp] theorem alphaOn_empty {V : Type u} (G : SimpleGraph V) :
    alphaOn G ∅ = 0 := by
  exact Nat.le_zero.mp (alphaOn_le_card G ∅)

/-- Restricting the ambient finite vertex set cannot increase its independence
number. -/
theorem alphaOn_mono {V : Type u} {G : SimpleGraph V} {S T : Finset V}
    (hST : S ⊆ T) : alphaOn G S ≤ alphaOn G T := by
  obtain ⟨I, hIS, hI, hIa⟩ := exists_maximum_independent_subset G S
  rw [← hIa]
  exact card_le_alphaOn (hIS.trans hST) hI

/-- Restricting an independent set to a smaller finite set preserves
independence. -/
theorem indepSet_inter {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {I S : Finset V} (hI : G.IsIndepSet I) : G.IsIndepSet (I ∩ S) := by
  exact hI.mono (by simp)

/-- Removing vertices outside `T` loses at most that many vertices from an
independent set. -/
theorem alphaOn_le_alphaOn_add_card_sdiff {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (S T : Finset V) :
    alphaOn G S ≤ alphaOn G (S ∩ T) + (S \ T).card := by
  classical
  obtain ⟨I, hIS, hI, hIa⟩ := exists_maximum_independent_subset G S
  have hinter : I ∩ T ⊆ S ∩ T := by
    intro v hv
    simp only [Finset.mem_inter] at hv ⊢
    exact ⟨hIS hv.1, hv.2⟩
  have hdiff : I \ T ⊆ S \ T := by
    intro v hv
    simp only [Finset.mem_sdiff] at hv ⊢
    exact ⟨hIS hv.1, hv.2⟩
  rw [← hIa, ← Finset.card_inter_add_card_sdiff I T]
  exact Nat.add_le_add (card_le_alphaOn hinter (hI.mono (by simp)))
    (Finset.card_le_card hdiff)

/-- Signed deficiency `|S| - 2 α(G[S])`. -/
noncomputable def potential {V : Type u} (G : SimpleGraph V) (S : Finset V) : ℤ :=
  (S.card : ℤ) - 2 * (alphaOn G S : ℤ)

@[simp] theorem potential_empty {V : Type u} (G : SimpleGraph V) :
    potential G ∅ = 0 := by simp [potential]

/-- The maximum signed deficiency of an induced finite vertex set. -/
noncomputable def f {V : Type u} [Fintype V] (G : SimpleGraph V) : ℤ := by
  classical
  exact ((Finset.univ : Finset V).powerset.image (potential G)).max' (by simp)

/-- A vertex set attaining the maximum deficiency. -/
theorem exists_maximum_potential {V : Type u} [Fintype V] (G : SimpleGraph V) :
    ∃ S : Finset V, potential G S = f G := by
  classical
  let P : Finset ℤ := (Finset.univ : Finset V).powerset.image (potential G)
  have hP : P.Nonempty := by simp [P]
  have hm : P.max' hP ∈ P := P.max'_mem hP
  obtain ⟨S, hS, hpot⟩ := Finset.mem_image.mp hm
  refine ⟨S, ?_⟩
  have hfuniv : S ⊆ (Finset.univ : Finset V) := Finset.subset_univ S
  have hmax : f G = P.max' hP := by
    simp only [f, P]
  exact hpot.trans hmax.symm

/-- Every potential is bounded by the maximum deficiency. -/
theorem potential_le_f {V : Type u} [Fintype V] (G : SimpleGraph V)
    (S : Finset V) : potential G S ≤ f G := by
  classical
  let P : Finset ℤ := (Finset.univ : Finset V).powerset.image (potential G)
  have hmem : potential G S ∈ P := by simp [P]
  have hle : potential G S ≤ P.max' ⟨potential G S, hmem⟩ := P.le_max' _ hmem
  simpa only [f, P] using hle

/-- The maximum deficiency is nonnegative because the empty vertex set has
potential zero. -/
theorem f_nonneg {V : Type u} [Fintype V] (G : SimpleGraph V) :
    0 ≤ f G := by
  simpa only [potential_empty] using potential_le_f G (∅ : Finset V)

/-- Bounding the maximum potential is exactly the same as bounding every
finite induced-set deficiency. -/
theorem f_le_iff_forall_potential_le {V : Type u} [Fintype V]
    (G : SimpleGraph V) (z : ℤ) :
    f G ≤ z ↔ ∀ S : Finset V, potential G S ≤ z := by
  constructor
  · intro hf S
    exact (potential_le_f G S).trans hf
  · intro h
    obtain ⟨S, hS⟩ := exists_maximum_potential G
    rw [← hS]
    exact h S

/-- Natural-cardinality form of `f ≤ k`.  This is the endpoint assumption
that is typically fed into Folkman's coloring bound. -/
theorem f_le_natCast_iff_forall_card_le {V : Type u} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) :
    f G ≤ (k : ℤ) ↔
      ∀ S : Finset V, S.card ≤ 2 * alphaOn G S + k := by
  rw [f_le_iff_forall_potential_le]
  constructor
  · intro h S
    have hS := h S
    rw [potential] at hS
    omega
  · intro h S
    have hS := h S
    rw [potential]
    omega

/-- An integral upper bound on the nonnegative maximum deficiency converts
to the corresponding natural-number upper bound. -/
theorem f_toNat_le_of_le_natCast {V : Type u} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (hf : f G ≤ (k : ℤ)) :
    (f G).toNat ≤ k := by
  have hnonneg := f_nonneg G
  omega

/-- Endpoint composition: once the general Folkman bound is known in terms
of the maximum signed deficiency, `f ≤ k` gives the requested `k + 2`
chromatic bound. -/
theorem chromaticNumber_le_add_two_of_f_le {V : Type u} [Fintype V]
    {G : SimpleGraph V} {k : ℕ}
    (hfolkman : G.chromaticNumber ≤ ((f G).toNat + 2 : ℕ∞))
    (hf : f G ≤ (k : ℤ)) :
    G.chromaticNumber ≤ (k + 2 : ℕ∞) := by
  refine hfolkman.trans ?_
  exact_mod_cast Nat.add_le_add_right (f_toNat_le_of_le_natCast hf) 2

/-- The subgraph hypothesis bounds every signed potential by `k`. -/
theorem potential_le_of_hasLargeIndependentSets {V : Type u} [Finite V]
    {G : SimpleGraph V} {k : ℕ} (h : HasLargeIndependentSets G k)
    (S : Finset V) : potential G S ≤ (k : ℤ) := by
  obtain ⟨I, hIS, hI, hcard⟩ := h.onFinsets S
  have hIa : I.card ≤ alphaOn G S := card_le_alphaOn hIS hI
  rw [potential]
  omega

/-- Consequently the maximum potential is bounded by `k`. -/
theorem f_le_of_hasLargeIndependentSets {V : Type u} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (h : HasLargeIndependentSets G k) :
    f G ≤ (k : ℤ) := by
  obtain ⟨S, hS⟩ := exists_maximum_potential G
  rw [← hS]
  exact potential_le_of_hasLargeIndependentSets h S

end Erdos922

open scoped Classical

namespace SimpleGraph

section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Hajnal's union--intersection inequality for a nonempty finite family of
maximum independent sets. -/
theorem hajnal_maximumIndepSet_family
    (G : SimpleGraph V) (F : Finset (Finset V)) (hF : F.Nonempty)
    (hmax : ∀ I ∈ F, G.IsMaximumIndepSet I) :
    2 * G.indepNum ≤ (F.inf id).card + (F.sup id).card := by
  classical
  induction F using Finset.induction with
  | empty => simp at hF
  | @insert I F hIF ih =>
      by_cases hFe : F = ∅
      · subst F
        have hI : G.IsMaximumIndepSet I := hmax I (by simp)
        have hIc := G.maximumIndepSet_card_eq_indepNum I hI
        simp only [Finset.inf_insert, Finset.inf_empty, Finset.sup_insert, Finset.sup_empty,
          inf_top_eq, sup_bot_eq]
        change 2 * G.indepNum ≤ I.card + I.card
        omega
      · have hFn : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hFe
        have hI : G.IsMaximumIndepSet I := hmax I (by simp)
        have hmaxF : ∀ J ∈ F, G.IsMaximumIndepSet J := by
          intro J hJ
          exact hmax J (Finset.mem_insert_of_mem hJ)
        have hIH := ih hFn hmaxF
        let C : Finset V := F.inf id
        let U : Finset V := F.sup id
        by_cases hcard : (C \ I).card ≤ (I \ U).card
        · have hC := Finset.card_sdiff_add_card_inter C I
          have hU := Finset.card_sdiff_add_card I U
          simp only [Finset.inf_insert, Finset.sup_insert]
          change 2 * G.indepNum ≤ (I ∩ C).card + (I ∪ U).card
          change 2 * G.indepNum ≤ C.card + U.card at hIH
          rw [Finset.inter_comm I C]
          omega
        · exfalso
          have hcard' : (I \ U).card < (C \ I).card := Nat.lt_of_not_ge hcard
          have hmemC : ∀ {x : V}, x ∈ C ↔ ∀ J ∈ F, x ∈ J := by
            intro x
            change x ∈ F.inf id ↔ _
            rw [← Finset.inf'_eq_inf hFn]
            simp
          have hmemU : ∀ {x : V}, x ∈ U ↔ ∃ J ∈ F, x ∈ J := by
            intro x
            change x ∈ F.sup id ↔ _
            simp
          let J : Finset V := (I ∩ U) ∪ (C \ I)
          have hJ : G.IsIndepSet J := by
            intro x hx y hy hxy
            change x ∈ J at hx
            change y ∈ J at hy
            simp only [J, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at hx hy
            rcases hx with hx | hx <;> rcases hy with hy | hy
            · exact hI.isIndepSet hx.1 hy.1 hxy
            · obtain ⟨K, hKF, hxK⟩ := hmemU.mp hx.2
              exact (hmaxF K hKF).isIndepSet hxK (hmemC.mp hy.1 K hKF) hxy
            · obtain ⟨K, hKF, hyK⟩ := hmemU.mp hy.2
              exact (hmaxF K hKF).isIndepSet (hmemC.mp hx.1 K hKF) hyK hxy
            · obtain ⟨K, hKF⟩ := hFn
              exact (hmaxF K hKF).isIndepSet (hmemC.mp hx.1 K hKF)
                (hmemC.mp hy.1 K hKF) hxy
          have hdisj : Disjoint (I ∩ U) (C \ I) := by
            rw [Finset.disjoint_left]
            intro x hxI hxC
            change x ∈ I ∩ U at hxI
            change x ∈ C \ I at hxC
            simp only [Finset.mem_inter] at hxI
            simp only [Finset.mem_sdiff] at hxC
            exact hxC.2 hxI.1
          have hJcard : J.card = (I ∩ U).card + (C \ I).card := by
            exact Finset.card_union_of_disjoint hdisj
          have hIcard := Finset.card_inter_add_card_sdiff I U
          have hle := hI.maximum J hJ
          omega

end

variable {V : Type*} [Fintype V]

/-- If the independence number is more than half the vertex count, one vertex
lies in every maximum independent set. -/
theorem exists_mem_all_maximumIndepSet_of_card_lt_two_mul_indepNum
    (G : SimpleGraph V) (hlarge : Fintype.card V < 2 * G.indepNum) :
    ∃ v : V, ∀ I : Finset V, G.IsMaximumIndepSet I → v ∈ I := by
  classical
  let F : Finset (Finset V) := (Finset.univ : Finset (Finset V)).filter G.IsMaximumIndepSet
  have hF : F.Nonempty := by
    obtain ⟨I, hI⟩ := G.maximumIndepSet_exists
    exact ⟨I, by simp [F, hI]⟩
  have hmax : ∀ I ∈ F, G.IsMaximumIndepSet I := by
    intro I hI
    simpa [F] using hI
  have hH := hajnal_maximumIndepSet_family G F hF hmax
  have hU : (F.sup id).card ≤ Fintype.card V := (F.sup id).card_le_univ
  have hinter : (F.inf id).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he] at hH
    simp only [Finset.card_empty, zero_add] at hH
    omega
  obtain ⟨v, hv⟩ := hinter
  refine ⟨v, ?_⟩
  intro I hI
  have hIF : I ∈ F := by simp [F, hI]
  rw [← Finset.inf'_eq_inf hF] at hv
  exact (Finset.mem_inf' hF).mp hv I hIF

end SimpleGraph

open SimpleGraph
open scoped ENat

namespace Erdos922FullB

universe u

/-!
This file develops the numerical core of the minimal-counterexample argument
for Folkman's theorem.  The maximum is localized to an ambient vertex
finset.  This makes the split inequality independent of any equivalences
between nested subtype vertex types.
-/

/-- The maximum size of an independent subset of `S`. -/
noncomputable def alphaOn {V : Type u} (G : SimpleGraph V) (S : Finset V) : ℕ := by
  classical
  exact Nat.findGreatest
    (fun n ↦ ∃ I : Finset V, I ⊆ S ∧ G.IsIndepSet I ∧ I.card = n) S.card

theorem exists_maximum_independent_subset {V : Type u}
    (G : SimpleGraph V) (S : Finset V) :
    ∃ I : Finset V, I ⊆ S ∧ G.IsIndepSet I ∧ I.card = alphaOn G S := by
  classical
  unfold alphaOn
  let P : ℕ → Prop := fun n ↦
    ∃ I : Finset V, I ⊆ S ∧ G.IsIndepSet I ∧ I.card = n
  change P (Nat.findGreatest P S.card)
  apply Nat.findGreatest_spec (m := 0) (Nat.zero_le S.card)
  exact ⟨(∅ : Finset V), by simp⟩

theorem card_le_alphaOn {V : Type u} {G : SimpleGraph V}
    {I S : Finset V} (hIS : I ⊆ S) (hI : G.IsIndepSet I) :
    I.card ≤ alphaOn G S := by
  classical
  unfold alphaOn
  exact Nat.le_findGreatest (Finset.card_le_card hIS) ⟨I, hIS, hI, rfl⟩

theorem alphaOn_le_card {V : Type u} (G : SimpleGraph V) (S : Finset V) :
    alphaOn G S ≤ S.card := by
  classical
  unfold alphaOn
  exact Nat.findGreatest_le _

@[simp] theorem alphaOn_empty {V : Type u} (G : SimpleGraph V) :
    alphaOn G ∅ = 0 := by
  exact Nat.le_zero.mp (by simpa using alphaOn_le_card G ∅)

/-- The signed deficiency `|S| - 2 α(G[S])`. -/
noncomputable def potential {V : Type u} (G : SimpleGraph V) (S : Finset V) : ℤ :=
  (S.card : ℤ) - 2 * (alphaOn G S : ℤ)

@[simp] theorem potential_empty {V : Type u} (G : SimpleGraph V) :
    potential G ∅ = 0 := by
  simp [potential]

/-- The canonical embedding of the vertex type of a finset-induced graph. -/
def subtypeEmbedding {V : Type u} (S : Finset V) : {v : V // v ∈ S} ↪ V :=
  ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem subtypeEmbedding_apply {V : Type u} (S : Finset V)
    (v : {v : V // v ∈ S}) : subtypeEmbedding S v = v.1 := rfl

/-- Independence number transport through the canonical embedding of an
induced vertex finset. -/
theorem alphaOn_induce_eq_alphaOn_map
    {V : Type u} [DecidableEq V] (G : SimpleGraph V) (S : Finset V)
    (A : Finset {v : V // v ∈ S}) :
    alphaOn (G.induce (S : Set V)) A =
      alphaOn G (A.map (subtypeEmbedding S)) := by
  classical
  apply Nat.le_antisymm
  · obtain ⟨I, hIA, hIind, hIcard⟩ :=
      exists_maximum_independent_subset (G.induce (S : Set V)) A
    rw [← hIcard]
    have hmap_ind : G.IsIndepSet (I.map (subtypeEmbedding S)) := by
      intro x hx y hy hxy hadj
      change x ∈ I.map (subtypeEmbedding S) at hx
      change y ∈ I.map (subtypeEmbedding S) at hy
      rw [Finset.mem_map] at hx hy
      obtain ⟨x', hx'I, rfl⟩ := hx
      obtain ⟨y', hy'I, rfl⟩ := hy
      exact hIind hx'I hy'I (fun h ↦ hxy (congrArg Subtype.val h)) hadj
    have hle := card_le_alphaOn
      ((Finset.map_subset_map (f := subtypeEmbedding S)).mpr hIA) hmap_ind
    simpa using hle
  · obtain ⟨J, hJA, hJind, hJcard⟩ :=
      exists_maximum_independent_subset G (A.map (subtypeEmbedding S))
    obtain ⟨I, hIA, rfl⟩ := Finset.subset_map_iff.mp hJA
    rw [← hJcard, Finset.card_map]
    apply card_le_alphaOn hIA
    intro x hx y hy hxy hadj
    apply hJind
    · exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
    · exact Finset.mem_map.mpr ⟨y, hy, rfl⟩
    · exact fun h ↦ hxy (Subtype.ext h)
    · exact hadj

/-- Signed potential is invariant under the canonical embedding of an
induced vertex finset. -/
theorem potential_induce_eq_potential_map
    {V : Type u} [DecidableEq V] (G : SimpleGraph V) (S : Finset V)
    (A : Finset {v : V // v ∈ S}) :
    potential (G.induce (S : Set V)) A =
      potential G (A.map (subtypeEmbedding S)) := by
  rw [potential, potential, alphaOn_induce_eq_alphaOn_map, Finset.card_map]

@[simp] theorem univ_map_subtypeEmbedding
    {V : Type u} [DecidableEq V] (S : Finset V) :
    (Finset.univ : Finset {v : V // v ∈ S}).map (subtypeEmbedding S) = S := by
  ext v
  simp [subtypeEmbedding]

/-- Maximum signed deficiency among vertex subsets of `U`.  The empty set is
among the candidates, so this maximum is always nonnegative. -/
noncomputable def fOn {V : Type u} (G : SimpleGraph V) (U : Finset V) : ℤ := by
  classical
  exact (U.powerset.image (potential G)).max'
    (U.powerset_nonempty.image (potential G))

theorem exists_maximum_potential_on {V : Type u} (G : SimpleGraph V) (U : Finset V) :
    ∃ S : Finset V, S ⊆ U ∧ potential G S = fOn G U := by
  classical
  let P : Finset ℤ := U.powerset.image (potential G)
  have hP : P.Nonempty := U.powerset_nonempty.image (potential G)
  have hm : P.max' hP ∈ P := P.max'_mem hP
  obtain ⟨S, hSU, hpot⟩ := Finset.mem_image.mp hm
  refine ⟨S, by simpa using hSU, ?_⟩
  have hf : fOn G U = P.max' hP := by simp only [fOn, P]
  exact hpot.trans hf.symm

theorem potential_le_fOn {V : Type u} (G : SimpleGraph V)
    {S U : Finset V} (hSU : S ⊆ U) : potential G S ≤ fOn G U := by
  classical
  let P : Finset ℤ := U.powerset.image (potential G)
  have hmem : potential G S ∈ P := by
    apply Finset.mem_image.mpr
    exact ⟨S, Finset.mem_powerset.mpr hSU, rfl⟩
  have hle : potential G S ≤ P.max' ⟨potential G S, hmem⟩ := P.le_max' _ hmem
  simpa only [fOn, P] using hle

/-- The localized maximum on `S` is definitionally the global maximum for
the graph induced on `S`, after transporting subtype finsets. -/
theorem fOn_induce_univ_eq_fOn
    {V : Type u} [DecidableEq V] (G : SimpleGraph V) (S : Finset V) :
    fOn (G.induce (S : Set V))
        (Finset.univ : Finset {v : V // v ∈ S}) = fOn G S := by
  classical
  apply le_antisymm
  · obtain ⟨A, hAuniv, hAf⟩ := exists_maximum_potential_on
      (G.induce (S : Set V)) (Finset.univ : Finset {v : V // v ∈ S})
    rw [← hAf, potential_induce_eq_potential_map]
    apply potential_le_fOn G
    have hmap := (Finset.map_subset_map (f := subtypeEmbedding S)).mpr hAuniv
    simpa only [univ_map_subtypeEmbedding] using hmap
  · obtain ⟨B, hBS, hBf⟩ := exists_maximum_potential_on G S
    have hBmap : B ⊆
        (Finset.univ : Finset {v : V // v ∈ S}).map (subtypeEmbedding S) := by
      simpa only [univ_map_subtypeEmbedding] using hBS
    obtain ⟨A, hAuniv, hBA⟩ := Finset.subset_map_iff.mp hBmap
    rw [← hBf, hBA, ← potential_induce_eq_potential_map]
    exact potential_le_fOn (G.induce (S : Set V)) hAuniv

/-- An independent set in a cycle graph occupies at most half of its
vertices.  The shift by one injects it into its complement. -/
theorem twice_card_le_of_cycleGraph_isIndepSet
    {n : ℕ} (hn : 3 ≤ n) {A : Finset (Fin n)}
    (hA : (SimpleGraph.cycleGraph n).IsIndepSet A) : 2 * A.card ≤ n := by
  classical
  have hnzero : NeZero n := ⟨by omega⟩
  let shift : Fin n ↪ Fin n := (Equiv.addRight (1 : Fin n)).toEmbedding
  have hadj (i : Fin n) : (SimpleGraph.cycleGraph n).Adj i (shift i) := by
    rw [SimpleGraph.cycleGraph_adj']
    right
    simp [shift, Nat.mod_eq_of_lt (by omega : 1 < n)]
  have hsub : A.map shift ⊆ Aᶜ := by
    intro j hj
    rw [Finset.mem_map] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    rw [Finset.mem_compl]
    intro hshift
    exact hA hi hshift (hadj i).ne (hadj i)
  have hc := Finset.card_le_card hsub
  simp only [Finset.card_map, Finset.card_compl, Fintype.card_fin] at hc
  omega

/-- Any embedded odd cycle certifies strictly positive hereditary
deficiency. -/
theorem fOn_pos_of_odd_cycle_copy
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n)
    (c : SimpleGraph.Copy (SimpleGraph.cycleGraph n) G) :
    0 < fOn G Finset.univ := by
  classical
  let e : Fin n ↪ V := c.toEmbedding
  let S : Finset V := (Finset.univ : Finset (Fin n)).map e
  have hScard : S.card = n := by simp [S]
  have halpha : 2 * alphaOn G S ≤ n := by
    obtain ⟨J, hJS, hJind, hJcard⟩ := exists_maximum_independent_subset G S
    have hJmap : J ⊆ (Finset.univ : Finset (Fin n)).map e := by simpa [S] using hJS
    obtain ⟨A, hAuniv, hJA⟩ := Finset.subset_map_iff.mp hJmap
    have hAind : (SimpleGraph.cycleGraph n).IsIndepSet A := by
      intro x hx y hy hxy hadj
      apply hJind
      · rw [hJA]
        exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
      · rw [hJA]
        exact Finset.mem_map.mpr ⟨y, hy, rfl⟩
      · exact fun h ↦ hxy (c.injective h)
      · exact c.toHom.map_rel hadj
    have hcycle := twice_card_le_of_cycleGraph_isIndepSet hn hAind
    rw [← hJcard, hJA, Finset.card_map]
    exact hcycle
  have hpot : 0 < potential G S := by
    rw [potential, hScard]
    obtain ⟨m, hm⟩ := hodd
    omega
  exact hpot.trans_le (potential_le_fOn G (Finset.subset_univ S))

theorem fOn_nonneg {V : Type u} (G : SimpleGraph V) (U : Finset V) :
    0 ≤ fOn G U := by
  simpa using potential_le_fOn G (S := (∅ : Finset V)) (Finset.empty_subset U)

theorem ofNat_toNat_fOn {V : Type u} (G : SimpleGraph V) (U : Finset V) :
    (Int.toNat (fOn G U) : ℤ) = fOn G U := by
  exact Int.toNat_of_nonneg (fOn_nonneg G U)

/-- An independent set in a disjoint union splits into independent sets in
the two sides. -/
theorem alphaOn_union_le_add {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {S T : Finset V} (hST : Disjoint S T) :
    alphaOn G (S ∪ T) ≤ alphaOn G S + alphaOn G T := by
  classical
  obtain ⟨I, hI_sub, hI_ind, hI_card⟩ :=
    exists_maximum_independent_subset G (S ∪ T)
  let IS : Finset V := I ∩ S
  let IT : Finset V := I ∩ T
  have hIS_sub : IS ⊆ S := by
    intro x hx
    exact (Finset.mem_inter.mp hx).2
  have hIT_sub : IT ⊆ T := by
    intro x hx
    exact (Finset.mem_inter.mp hx).2
  have hIS_ind : G.IsIndepSet IS := hI_ind.mono (by
    intro x hx
    exact (Finset.mem_inter.mp hx).1)
  have hIT_ind : G.IsIndepSet IT := hI_ind.mono (by
    intro x hx
    exact (Finset.mem_inter.mp hx).1)
  have hparts : IS ∪ IT = I := by
    ext x
    simp only [IS, IT, Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
    · intro hx
      have hxST := hI_sub hx
      rcases Finset.mem_union.mp hxST with hxS | hxT
      · exact Or.inl ⟨hx, hxS⟩
      · exact Or.inr ⟨hx, hxT⟩
  have hparts_disj : Disjoint IS IT := by
    apply Finset.disjoint_left.mpr
    intro x hxS hxT
    exact Finset.disjoint_left.mp hST
      (Finset.mem_inter.mp hxS).2 (Finset.mem_inter.mp hxT).2
  have hcard_parts : I.card = IS.card + IT.card := by
    rw [← hparts, Finset.card_union_of_disjoint hparts_disj]
  have hIS_le : IS.card ≤ alphaOn G S := card_le_alphaOn hIS_sub hIS_ind
  have hIT_le : IT.card ≤ alphaOn G T := card_le_alphaOn hIT_sub hIT_ind
  omega

/-- Signed deficiencies are superadditive on disjoint vertex sets. -/
theorem potential_add_le_union {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {S T : Finset V} (hST : Disjoint S T) :
    potential G S + potential G T ≤ potential G (S ∪ T) := by
  have ha := alphaOn_union_le_add (G := G) hST
  have hc := Finset.card_union_of_disjoint hST
  simp only [potential]
  omega

/-- The key potential inequality used in Folkman's split argument. -/
theorem fOn_add_le_fOn_union {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    {U W : Finset V} (hUW : Disjoint U W) :
    fOn G U + fOn G W ≤ fOn G (U ∪ W) := by
  classical
  obtain ⟨S, hSU, hSf⟩ := exists_maximum_potential_on G U
  obtain ⟨T, hTW, hTf⟩ := exists_maximum_potential_on G W
  have hST : Disjoint S T := hUW.mono hSU hTW
  have hsub : S ∪ T ⊆ U ∪ W := Finset.union_subset_union hSU hTW
  rw [← hSf, ← hTf]
  exact (potential_add_le_union hST).trans (potential_le_fOn G hsub)

/-- The natural-valued chromatic number of a finite graph.  This agrees with
the finite value of Mathlib's `ℕ∞`-valued chromatic number. -/
noncomputable def chiNat {V : Type u} (G : SimpleGraph V) : ℕ :=
  ENat.toNat G.chromaticNumber

theorem chromaticNumber_eq_natCast_chiNat {V : Type u} [Fintype V]
    (G : SimpleGraph V) : G.chromaticNumber = (chiNat G : ℕ∞) := by
  have hne : G.chromaticNumber ≠ ⊤ := by
    have hlt : G.chromaticNumber < ⊤ :=
      G.colorable_of_fintype.chromaticNumber_le.trans_lt (ENat.natCast_lt_top _)
    exact hlt.ne
  exact (ENat.natCast_toNat hne).symm

theorem colorable_iff_chiNat_le {V : Type u} [Fintype V]
    (G : SimpleGraph V) (q : ℕ) : G.Colorable q ↔ chiNat G ≤ q := by
  rw [← chromaticNumber_le_iff_colorable,
    chromaticNumber_eq_natCast_chiNat G]
  exact ENat.natCast_le_natCast

theorem colorable_chiNat {V : Type u} [Fintype V] (G : SimpleGraph V) :
    G.Colorable (chiNat G) := by
  exact (colorable_iff_chiNat_le G _).mpr le_rfl

/-- The global form of Folkman's bound, with the signed deficiency maximum
`fOn G univ`; the paper's potential maximum is this number plus two. -/
noncomputable def FolkmanBound {V : Type u} [Fintype V]
    (G : SimpleGraph V) : Prop :=
  G.Colorable (Int.toNat (fOn G Finset.univ) + 2)

theorem folkmanBound_iff_chiNat_le {V : Type u} [Fintype V]
    (G : SimpleGraph V) :
    FolkmanBound G ↔ chiNat G ≤ Int.toNat (fOn G Finset.univ) + 2 := by
  exact colorable_iff_chiNat_le G _

theorem not_folkmanBound_iff_lt_chiNat {V : Type u} [Fintype V]
    (G : SimpleGraph V) :
    ¬ FolkmanBound G ↔ Int.toNat (fOn G Finset.univ) + 2 < chiNat G := by
  rw [folkmanBound_iff_chiNat_le]
  omega

theorem counterexample_gap_int {V : Type u} [Fintype V]
    (G : SimpleGraph V) (hG : ¬ FolkmanBound G) :
    fOn G Finset.univ + 2 < (chiNat G : ℤ) := by
  have h := (not_folkmanBound_iff_lt_chiNat G).mp hG
  have hf := ofNat_toNat_fOn G (Finset.univ : Finset V)
  omega

theorem three_le_chiNat_of_not_folkmanBound {V : Type u} [Fintype V]
    (G : SimpleGraph V) (hG : ¬ FolkmanBound G) : 3 ≤ chiNat G := by
  have h := (not_folkmanBound_iff_lt_chiNat G).mp hG
  omega

theorem four_le_chiNat_of_not_folkmanBound_of_fOn_pos
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hG : ¬ FolkmanBound G) (hf : 0 < fOn G Finset.univ) :
    4 ≤ chiNat G := by
  have h := (not_folkmanBound_iff_lt_chiNat G).mp hG
  have hcast := ofNat_toNat_fOn G (Finset.univ : Finset V)
  have : 1 ≤ Int.toNat (fOn G Finset.univ) := by omega
  omega

/-- A counterexample minimal by vertex count.  The second conjunct is the
strong-induction hypothesis on *all* smaller finite graph vertex types, so it
also applies to contractions and apex constructions, not only induced
subgraphs. -/
noncomputable def IsOrderMinimalCounterexample
    {V : Type u} [Fintype V] (G : SimpleGraph V) : Prop :=
  ¬ FolkmanBound G ∧
    ∀ {W : Type u} [Fintype W] [DecidableEq W] (H : SimpleGraph W),
      Fintype.card W < Fintype.card V → FolkmanBound H

theorem IsOrderMinimalCounterexample.counterexample
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : IsOrderMinimalCounterexample G) : ¬ FolkmanBound G := hG.1

theorem IsOrderMinimalCounterexample.smaller
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : IsOrderMinimalCounterexample G)
    {W : Type u} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    (hcard : Fintype.card W < Fintype.card V) : FolkmanBound H :=
  hG.2 H hcard

theorem IsOrderMinimalCounterexample.proper_induce
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : IsOrderMinimalCounterexample G) (S : Finset V)
    (hS : S ⊂ (Finset.univ : Finset V)) :
    FolkmanBound (G.induce (S : Set V)) := by
  apply hG.smaller
  have hcard : S.card < Fintype.card V := by
    simpa using Finset.card_lt_card hS
  simpa using hcard

theorem IsOrderMinimalCounterexample.proper_induce_chiNat_le
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : IsOrderMinimalCounterexample G) (S : Finset V)
    (hS : S ⊂ (Finset.univ : Finset V)) :
    (chiNat (G.induce (S : Set V)) : ℤ) ≤ fOn G S + 2 := by
  have hc := (folkmanBound_iff_chiNat_le (G.induce (S : Set V))).mp
    (hG.proper_induce S hS)
  rw [fOn_induce_univ_eq_fOn] at hc
  have hf := ofNat_toNat_fOn G S
  omega

/-- A counterexample to Folkman's bound cannot be two-colorable.  This is
already true before using order minimality: the target number of colors is
at least two because `fOn` is nonnegative. -/
theorem IsOrderMinimalCounterexample.not_colorable_two
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : IsOrderMinimalCounterexample G) : ¬ G.Colorable 2 := by
  intro htwo
  apply hG.counterexample
  exact htwo.mono (by omega)

/-- Hence a minimal counterexample is not acyclic, since every finite
acyclic simple graph is two-colorable. -/
theorem IsOrderMinimalCounterexample.not_isAcyclic
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : IsOrderMinimalCounterexample G) : ¬ G.IsAcyclic := by
  intro hacyclic
  exact hG.not_colorable_two hacyclic.colorable_two

/-- A minimal counterexample therefore contains a cycle realizing the
girth.  This packages exactly the shortest-cycle data used by the structural
part of Folkman's proof. -/
theorem IsOrderMinimalCounterexample.exists_shortest_cycle
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : IsOrderMinimalCounterexample G) :
    ∃ v, ∃ w : G.Walk v v, w.IsCycle ∧ w.length = G.girth := by
  obtain ⟨v, w, hwcycle, hlength⟩ := G.exists_girth_eq_length.mpr hG.not_isAcyclic
  exact ⟨v, w, hwcycle, hlength.symm⟩

/-- Equivalently, failure of two-colorability directly supplies an odd
closed walk.  Extracting an odd simple cycle from this walk is one possible
route to the base case; the modern proof instead takes a shortest cycle and
uses the previously established absence of even holes. -/
theorem IsOrderMinimalCounterexample.exists_odd_closed_walk
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : IsOrderMinimalCounterexample G) :
    ∃ v, ∃ w : G.Walk v v, Odd w.length := by
  have hnot := hG.not_colorable_two
  rw [SimpleGraph.two_colorable_iff_forall_loop_even] at hnot
  push_neg at hnot
  obtain ⟨v, w, hw⟩ := hnot
  exact ⟨v, w, Nat.not_even_iff_odd.mp hw⟩

/-- Once the girth-realizing cycle is known to be odd (in Folkman's
argument this follows from chordlessness and the exclusion of induced even
cycles), it witnesses positive hereditary deficiency. -/
theorem IsOrderMinimalCounterexample.fOn_pos_of_girth_odd
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : IsOrderMinimalCounterexample G) (hodd : Odd G.girth) :
    0 < fOn G Finset.univ := by
  obtain ⟨v, w, hwcycle, hlength⟩ := hG.exists_shortest_cycle
  have hthree : 3 ≤ G.girth := by
    rw [← hlength]
    exact hwcycle.three_le_length
  have hcopy : SimpleGraph.cycleGraph G.girth ⊑ G := by
    rw [SimpleGraph.cycleGraph_isContained_iff (by omega)]
    exact ⟨v, w, hwcycle, hlength⟩
  obtain ⟨c⟩ := hcopy
  exact fOn_pos_of_odd_cycle_copy G hthree hodd c

/-- The positive deficiency raises the automatic lower bound on the
chromatic number from three to four. -/
theorem IsOrderMinimalCounterexample.four_le_chiNat_of_girth_odd
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : IsOrderMinimalCounterexample G) (hodd : Odd G.girth) :
    4 ≤ chiNat G := by
  exact four_le_chiNat_of_not_folkmanBound_of_fOn_pos G hG.counterexample
    (hG.fOn_pos_of_girth_odd hodd)

/-- Every odd closed walk in a simple graph contains an odd simple cycle.
The proof recursively removes a nontrivial closed subwalk of the tail.  If
that subwalk is odd we recurse into it; if it is even we delete it, preserving
odd parity and strictly decreasing length. -/
theorem exists_odd_cycle_of_odd_closed_walk
    {V : Type u} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (w : G.Walk v v) (hodd : Odd w.length) :
    ∃ x, ∃ c : G.Walk x x, c.IsCycle ∧ Odd c.length := by
  have hwnnil : ¬ w.Nil := by
    rw [Walk.not_nil_iff_lt_length]
    obtain ⟨m, hm⟩ := hodd
    omega
  by_cases hpath : w.tail.IsPath
  · have hnotone : w.length ≠ 1 := by
      intro hone
      exact (G.ne_of_adj (w.adj_of_length_eq_one hone)) rfl
    have hthree : 3 ≤ w.length := by
      obtain ⟨m, hm⟩ := hodd
      omega
    exact ⟨v, w, Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      ⟨hpath, hthree⟩, hodd⟩
  · rw [Walk.isPath_iff_isSubwalk_imp_nil] at hpath
    push_neg at hpath
    obtain ⟨x, q, hqsub, hqnonnil⟩ := hpath
    have hqlt : q.length < w.length := by
      have hle := Walk.length_le_of_isSubwalk hqsub
      have htail : w.tail.length < w.length := by
        have := Walk.length_tail_add_one hwnnil
        omega
      exact hle.trans_lt htail
    by_cases hqeven : Even q.length
    · obtain ⟨ru, rv, hdecomp⟩ := hqsub
      let r : G.Walk v v :=
        Walk.cons (w.adj_snd hwnnil) (ru.append rv)
      have hlen : w.length = r.length + q.length := by
        have htail_len := Walk.length_tail_add_one hwnnil
        rw [hdecomp, Walk.length_append, Walk.length_append] at htail_len
        simp only [r, Walk.length_cons, Walk.length_append]
        omega
      have hrodd : Odd r.length := by
        apply Nat.not_even_iff_odd.mp
        intro hreven
        apply (Nat.not_even_iff_odd.mpr hodd)
        rw [hlen]
        exact hreven.add hqeven
      have hrlt : r.length < w.length := by
        have hqpos : 0 < q.length := by
          rw [← Walk.not_nil_iff_lt_length]
          exact hqnonnil
        omega
      exact exists_odd_cycle_of_odd_closed_walk r hrodd
    · exact exists_odd_cycle_of_odd_closed_walk q
        (Nat.not_even_iff_odd.mp hqeven)
termination_by w.length
decreasing_by
  · simpa only [r, Walk.length_cons, Walk.length_append] using hrlt
  · exact hqlt

/-- The direct odd-cycle consequence of failure of two-colorability. -/
theorem IsOrderMinimalCounterexample.exists_odd_cycle
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : IsOrderMinimalCounterexample G) :
    ∃ x, ∃ c : G.Walk x x, c.IsCycle ∧ Odd c.length := by
  obtain ⟨v, w, hodd⟩ := hG.exists_odd_closed_walk
  exact exists_odd_cycle_of_odd_closed_walk w hodd

/-- Unconditional positivity of the hereditary deficiency maximum for an
order-minimal counterexample. -/
theorem IsOrderMinimalCounterexample.fOn_pos
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : IsOrderMinimalCounterexample G) : 0 < fOn G Finset.univ := by
  obtain ⟨v, c, hcycle, hodd⟩ := hG.exists_odd_cycle
  have hcopy : SimpleGraph.cycleGraph c.length ⊑ G := by
    rw [SimpleGraph.cycleGraph_isContained_iff (by
      exact Nat.lt_of_lt_of_le (by omega) hcycle.three_le_length)]
    exact ⟨v, c, hcycle, rfl⟩
  obtain ⟨copy⟩ := hcopy
  exact fOn_pos_of_odd_cycle_copy G hcycle.three_le_length hodd copy

/-- Every order-minimal counterexample has natural chromatic number at
least four. -/
theorem IsOrderMinimalCounterexample.four_le_chiNat
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : IsOrderMinimalCounterexample G) : 4 ≤ chiNat G := by
  exact four_le_chiNat_of_not_folkmanBound_of_fOn_pos G hG.counterexample hG.fOn_pos


/-- The remaining structural target in a strong-induction proof: there is no
vertex-order-minimal counterexample.  This is a proposition, not a postulate;
the even-hole, diamond, and recoloring development must prove it. -/
noncomputable def NoOrderMinimalCounterexample : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    ¬ IsOrderMinimalCounterexample G

/-- Strong-induction assembly: once the structural argument excludes every
order-minimal counterexample, Folkman's bound holds for every finite graph. -/
theorem folkmanBound_of_noOrderMinimalCounterexample
    (hNo : NoOrderMinimalCounterexample.{u}) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      FolkmanBound G := by
  let P : ℕ → Prop := fun n ↦
    ∀ (V : Type u) [Fintype V] [DecidableEq V], Fintype.card V = n →
      ∀ G : SimpleGraph V, FolkmanBound G
  have hall : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        dsimp only [P]
        intro V _ _ hV G
        by_contra hbad
        apply hNo G
        refine ⟨hbad, ?_⟩
        intro W _ _ H hWV
        apply ih (Fintype.card W)
        · omega
        · rfl
  intro V _ _ G
  exact hall (Fintype.card V) V rfl G

/-- Numerical form of the critical split property `(A)` in the modern proof
of Folkman's theorem.  The two hypotheses are precisely what a least-order
counterexample supplies: the current graph violates the bound, while both
proper induced sides satisfy it.

Using `fOn` keeps all potentials on the ambient vertex type. -/
theorem critical_split_inequality
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hcounter : fOn G Finset.univ + 2 < (chiNat G : ℤ))
    (hminimal : ∀ S : Finset V, S ⊂ (Finset.univ : Finset V) →
      (chiNat (G.induce (S : Set V)) : ℤ) ≤ fOn G S + 2)
    (X : Finset V) (hXnonempty : X.Nonempty) (hXne : X ≠ Finset.univ) :
    chiNat (G.induce (X : Set V)) +
        chiNat (G.induce ((↑(Xᶜ) : Set V))) ≤ chiNat G + 1 := by
  classical
  have hXproper : X ⊂ (Finset.univ : Finset V) :=
    (Finset.subset_univ X).ssubset_of_ne hXne
  have hcomp_ne : (Xᶜ : Finset V) ≠ Finset.univ := by
    exact (Finset.compl_ne_univ_iff_nonempty X).mpr hXnonempty
  have hcompproper : (Xᶜ : Finset V) ⊂ (Finset.univ : Finset V) :=
    (Finset.subset_univ Xᶜ).ssubset_of_ne hcomp_ne
  have hleft := hminimal X hXproper
  have hright := hminimal Xᶜ hcompproper
  have hdisj : Disjoint X Xᶜ := disjoint_compl_right
  have hpot := fOn_add_le_fOn_union G hdisj
  have hunion : X ∪ Xᶜ = (Finset.univ : Finset V) := Finset.union_compl X
  rw [hunion] at hpot
  have hgap : fOn G Finset.univ + 3 ≤ (chiNat G : ℤ) := by omega
  norm_cast
  norm_cast at hleft hright hcounter hpot hgap
  omega

/-- Property `(A)` for an actual vertex-order-minimal counterexample. -/
theorem IsOrderMinimalCounterexample.critical_split
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : IsOrderMinimalCounterexample G)
    (X : Finset V) (hXnonempty : X.Nonempty) (hXne : X ≠ Finset.univ) :
    chiNat (G.induce (X : Set V)) +
        chiNat (G.induce ((↑(Xᶜ) : Set V))) ≤ chiNat G + 1 := by
  apply critical_split_inequality G (counterexample_gap_int G hG.counterexample)
  · intro S hS
    exact hG.proper_induce_chiNat_le S hS
  · exact hXnonempty
  · exact hXne

end Erdos922FullB

open Function

namespace Erdos922EvenHole

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The preliminary contraction map.  Vertices in `A` go to the left new
vertex, vertices in `B` go to the right new vertex, and all other vertices
retain their name. -/
def preContract (A B : Finset V) (v : V) : V ⊕ Bool :=
  if v ∈ A then .inr false else if v ∈ B then .inr true else .inl v

/-- The actual contracted vertex type.  Taking the range is important: it
removes the unused copies `Sum.inl v` for `v ∈ A ∪ B`. -/
abbrev ContractVertex (A B : Finset V) := Set.range (preContract A B)

/-- The surjection from the old vertex type to the contracted vertex type. -/
def contract (A B : Finset V) (v : V) : ContractVertex A B :=
  ⟨preContract A B v, Set.mem_range_self v⟩

/-- Push all old edges through the contraction.  `SimpleGraph.map` deletes
the loops produced inside a contracted fiber. -/
def contractGraph (G : SimpleGraph V) (A B : Finset V) :
    SimpleGraph (ContractVertex A B) :=
  G.map (contract A B)

theorem preContract_eq_inr_false_iff (A B : Finset V) (v : V) :
    preContract A B v = Sum.inr false ↔ v ∈ A := by
  simp only [preContract]
  by_cases hvA : v ∈ A
  · simp [hvA]
  · by_cases hvB : v ∈ B <;> simp [hvA, hvB]

theorem preContract_eq_inr_true_iff (A B : Finset V) (hAB : Disjoint A B) (v : V) :
    preContract A B v = Sum.inr true ↔ v ∈ B := by
  simp only [preContract]
  by_cases hvA : v ∈ A
  · have hvB : v ∉ B := fun hvB ↦ Finset.disjoint_left.mp hAB hvA hvB
    simp [hvA, hvB]
  · by_cases hvB : v ∈ B <;> simp [hvA, hvB]

theorem preContract_eq_inl_iff (A B : Finset V) (v w : V) :
    preContract A B v = Sum.inl w ↔ v = w ∧ w ∉ A ∧ w ∉ B := by
  by_cases hvA : v ∈ A
  · constructor
    · intro h
      simp [preContract, hvA] at h
    · rintro ⟨rfl, hnot, -⟩
      exact (hnot hvA).elim
  · by_cases hvB : v ∈ B
    · constructor
      · intro h
        simp [preContract, hvA, hvB] at h
      · rintro ⟨rfl, -, hnot⟩
        exact (hnot hvB).elim
    · constructor
      · intro h
        have hvw : v = w := by simpa [preContract, hvA, hvB] using h
        subst w
        exact ⟨rfl, hvA, hvB⟩
      · rintro ⟨rfl, -, -⟩
        simp [preContract, hvA, hvB]

theorem contract_injective_outside (A B : Finset V) {v w : V}
    (hvA : v ∉ A) (hvB : v ∉ B) (hwA : w ∉ A) (hwB : w ∉ B)
    (h : contract A B v = contract A B w) : v = w := by
  have hval := congrArg Subtype.val h
  simpa [contract, preContract, hvA, hvB, hwA, hwB] using hval

theorem contract_eq_iff_of_outside (A B : Finset V) {v w : V}
    (hvA : v ∉ A) (hvB : v ∉ B) (hwA : w ∉ A) (hwB : w ∉ B) :
    contract A B v = contract A B w ↔ v = w := by
  constructor
  · exact contract_injective_outside A B hvA hvB hwA hwB
  · exact congrArg _

theorem contract_eq_of_mem_left (A B : Finset V) {v w : V}
    (hv : v ∈ A) (hw : w ∈ A) : contract A B v = contract A B w := by
  apply Subtype.ext
  simp [contract, preContract, hv, hw]

theorem contract_eq_of_mem_right (A B : Finset V) (hAB : Disjoint A B) {v w : V}
    (hv : v ∈ B) (hw : w ∈ B) : contract A B v = contract A B w := by
  have hvA : v ∉ A := fun ha ↦ Finset.disjoint_left.mp hAB ha hv
  have hwA : w ∉ A := fun ha ↦ Finset.disjoint_left.mp hAB ha hw
  apply Subtype.ext
  simp [contract, preContract, hvA, hwA, hv, hw]

theorem contract_ne_left_right (A B : Finset V) (hAB : Disjoint A B)
    {a b : V} (ha : a ∈ A) (hb : b ∈ B) :
    contract A B a ≠ contract A B b := by
  have hbA : b ∉ A := fun hba ↦ Finset.disjoint_left.mp hAB hba hb
  intro h
  have hval := congrArg Subtype.val h
  simpa [contract, preContract, ha, hbA, hb] using hval

section Fibers

variable {W : Type*} [DecidableEq W]

/-- An independent set descends through a possibly noninjective graph map as
soon as it contains the whole fiber above every image vertex retained.  This
is the key fact that makes the contraction proof honest: retaining only one
old representative of a contracted vertex would not suffice. -/
theorem isIndepSet_map_of_fiber_subset (G : SimpleGraph V) (q : V → W)
    {I : Finset V} {J : Finset W} (hI : G.IsIndepSet I)
    (hfiber : ∀ x ∈ J, ∀ v, q v = x → v ∈ I) :
    (G.map q).IsIndepSet J := by
  rw [SimpleGraph.isIndepSet_iff]
  rintro x hx y hy hxy hAdj
  rcases hAdj with ⟨hqne, u, v, huv, hu, hv⟩
  apply hI (hfiber x hx u hu) (hfiber y hy v hv)
  · intro huvEq
    subst v
    exact hqne (hu.symm.trans hv)
  · exact huv

end Fibers

/-- The vertices of `I` outside the two contracted fibers. -/
def outsidePart (A B I : Finset V) : Finset V :=
  I.filter fun v ↦ v ∉ A ∧ v ∉ B

/-- The image of the outside portion of `I` in the contracted graph. -/
def outsideImage (A B I : Finset V) : Finset (ContractVertex A B) :=
  (outsidePart A B I).image (contract A B)

theorem mem_outsidePart_iff (A B I : Finset V) (v : V) :
    v ∈ outsidePart A B I ↔ v ∈ I ∧ v ∉ A ∧ v ∉ B := by
  simp [outsidePart]

theorem outsideImage_fiber_subset (A B I : Finset V) :
    ∀ x ∈ outsideImage A B I, ∀ v, contract A B v = x → v ∈ I := by
  intro x hx v hvx
  simp only [outsideImage, Finset.mem_image] at hx
  rcases hx with ⟨w, hw, rfl⟩
  have hw' := (mem_outsidePart_iff A B I w).mp hw
  have hpw : preContract A B w = Sum.inl w := by
    simp [preContract, hw'.2.1, hw'.2.2]
  have hpv : preContract A B v = Sum.inl w := by
    have := congrArg Subtype.val hvx
    exact this.trans hpw
  have hvw := (preContract_eq_inl_iff A B v w).mp hpv |>.1
  simpa [hvw] using hw'.1

theorem isIndepSet_outsideImage (G : SimpleGraph V) (A B I : Finset V)
    (hI : G.IsIndepSet I) :
    (contractGraph G A B).IsIndepSet (outsideImage A B I) := by
  exact isIndepSet_map_of_fiber_subset G (contract A B) hI
    (outsideImage_fiber_subset A B I)

/-- If `I` contains all of `A`, its outside image together with the left
contracted vertex is independent. -/
theorem isIndepSet_insert_left (G : SimpleGraph V) (A B I : Finset V)
    {a : V} (ha : a ∈ A) (hAI : A ⊆ I) (hI : G.IsIndepSet I) :
    (contractGraph G A B).IsIndepSet
      ((insert (contract A B a) (outsideImage A B I) :
        Finset (ContractVertex A B)) : Set (ContractVertex A B)) := by
  apply isIndepSet_map_of_fiber_subset G (contract A B) hI
  intro x hx v hvx
  simp only [Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · apply hAI
    apply (preContract_eq_inr_false_iff A B v).mp
    have hval := congrArg Subtype.val hvx
    simpa [contract, preContract, ha] using hval
  · exact outsideImage_fiber_subset A B I x hx v hvx

/-- If `I` contains all of `B`, its outside image together with the right
contracted vertex is independent. -/
theorem isIndepSet_insert_right (G : SimpleGraph V) (A B I : Finset V)
    (hAB : Disjoint A B) {b : V} (hb : b ∈ B) (hBI : B ⊆ I)
    (hI : G.IsIndepSet I) :
    (contractGraph G A B).IsIndepSet
      ((insert (contract A B b) (outsideImage A B I) :
        Finset (ContractVertex A B)) : Set (ContractVertex A B)) := by
  apply isIndepSet_map_of_fiber_subset G (contract A B) hI
  intro x hx v hvx
  simp only [Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · apply hBI
    apply (preContract_eq_inr_true_iff A B hAB v).mp
    have hbA : b ∉ A := fun hba ↦ Finset.disjoint_left.mp hAB hba hb
    have hval := congrArg Subtype.val hvx
    simpa [contract, preContract, hbA, hb] using hval
  · exact outsideImage_fiber_subset A B I x hx v hvx

/-- If `I` contains both full fibers, both contracted vertices can be kept. -/
theorem isIndepSet_insert_both (G : SimpleGraph V) (A B I : Finset V)
    (hAB : Disjoint A B) {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (hAI : A ⊆ I) (hBI : B ⊆ I) (hI : G.IsIndepSet I) :
    (contractGraph G A B).IsIndepSet
      ((insert (contract A B a)
        (insert (contract A B b) (outsideImage A B I)) :
          Finset (ContractVertex A B)) : Set (ContractVertex A B)) := by
  apply isIndepSet_map_of_fiber_subset G (contract A B) hI
  intro x hx v hvx
  simp only [Finset.mem_insert] at hx
  rcases hx with rfl | rfl | hx
  · apply hAI
    apply (preContract_eq_inr_false_iff A B v).mp
    have hval := congrArg Subtype.val hvx
    simpa [contract, preContract, ha] using hval
  · apply hBI
    apply (preContract_eq_inr_true_iff A B hAB v).mp
    have hbA : b ∉ A := fun hba ↦ Finset.disjoint_left.mp hAB hba hb
    have hval := congrArg Subtype.val hvx
    simpa [contract, preContract, hbA, hb] using hval
  · exact outsideImage_fiber_subset A B I x hx v hvx

section Cardinalities

theorem outsideImage_card (A B I : Finset V) :
    (outsideImage A B I).card = (outsidePart A B I).card := by
  rw [outsideImage, Finset.card_image_iff]
  intro v hv w hw hvw
  have hv' := (mem_outsidePart_iff A B I v).mp hv
  have hw' := (mem_outsidePart_iff A B I w).mp hw
  exact contract_injective_outside A B hv'.2.1 hv'.2.2 hw'.2.1 hw'.2.2 hvw

theorem contract_left_not_mem_outsideImage (A B I : Finset V) {a : V} (ha : a ∈ A) :
    contract A B a ∉ outsideImage A B I := by
  intro h
  simp only [outsideImage, Finset.mem_image] at h
  rcases h with ⟨v, hv, hva⟩
  have hv' := (mem_outsidePart_iff A B I v).mp hv
  have hval := congrArg Subtype.val hva
  simp [contract, preContract, ha, hv'.2.1, hv'.2.2] at hval

theorem contract_right_not_mem_outsideImage (A B I : Finset V) (hAB : Disjoint A B)
    {b : V} (hb : b ∈ B) : contract A B b ∉ outsideImage A B I := by
  intro h
  simp only [outsideImage, Finset.mem_image] at h
  rcases h with ⟨v, hv, hvb⟩
  have hv' := (mem_outsidePart_iff A B I v).mp hv
  have hbA : b ∉ A := fun hba ↦ Finset.disjoint_left.mp hAB hba hb
  have hval := congrArg Subtype.val hvb
  simp [contract, preContract, hbA, hb, hv'.2.1, hv'.2.2] at hval

theorem insert_left_outsideImage_card (A B I : Finset V) {a : V} (ha : a ∈ A) :
    (insert (contract A B a) (outsideImage A B I)).card =
      (outsidePart A B I).card + 1 := by
  rw [Finset.card_insert_of_notMem (contract_left_not_mem_outsideImage A B I ha)]
  rw [outsideImage_card]

theorem insert_right_outsideImage_card (A B I : Finset V) (hAB : Disjoint A B)
    {b : V} (hb : b ∈ B) :
    (insert (contract A B b) (outsideImage A B I)).card =
      (outsidePart A B I).card + 1 := by
  rw [Finset.card_insert_of_notMem (contract_right_not_mem_outsideImage A B I hAB hb)]
  rw [outsideImage_card]

theorem insert_both_outsideImage_card (A B I : Finset V) (hAB : Disjoint A B)
    {a b : V} (ha : a ∈ A) (hb : b ∈ B) :
    (insert (contract A B a) (insert (contract A B b) (outsideImage A B I))).card =
      (outsidePart A B I).card + 2 := by
  have hright := contract_right_not_mem_outsideImage A B I hAB hb
  have hleft : contract A B a ∉ insert (contract A B b) (outsideImage A B I) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨contract_ne_left_right A B hAB ha hb, contract_left_not_mem_outsideImage A B I ha⟩
  rw [Finset.card_insert_of_notMem hleft, Finset.card_insert_of_notMem hright]
  rw [outsideImage_card]

/-- Portion of an independent set lying on the old even cycle. -/
def cyclePart (A B I : Finset V) : Finset V := I ∩ (A ∪ B)

theorem outsidePart_eq_sdiff (A B I : Finset V) :
    outsidePart A B I = I \ (A ∪ B) := by
  ext v
  simp [outsidePart]

theorem outside_cycle_card_decomposition (A B I : Finset V) :
    (outsidePart A B I).card + (cyclePart A B I).card = I.card := by
  rw [outsidePart_eq_sdiff]
  exact Finset.card_sdiff_add_card_inter I (A ∪ B)

/-- Old vertices outside the contracted fibers whose images lie in `S`. -/
def outsidePreimage (A B : Finset V) (S : Finset (ContractVertex A B)) : Finset V :=
  Finset.univ.filter fun v ↦ contract A B v ∈ S ∧ v ∉ A ∧ v ∉ B

theorem mem_outsidePreimage_iff (A B : Finset V) (S : Finset (ContractVertex A B))
    (v : V) :
    v ∈ outsidePreimage A B S ↔ contract A B v ∈ S ∧ v ∉ A ∧ v ∉ B := by
  simp [outsidePreimage]

theorem outsideImage_outsidePreimage_subset (A B : Finset V)
    (S : Finset (ContractVertex A B)) :
    outsideImage A B (outsidePreimage A B S) ⊆ S := by
  intro x hx
  simp only [outsideImage, Finset.mem_image] at hx
  rcases hx with ⟨v, hv, rfl⟩
  exact ((mem_outsidePreimage_iff A B S v).mp
    ((mem_outsidePart_iff A B (outsidePreimage A B S) v).mp hv).1).1

theorem outsidePart_outsidePreimage (A B : Finset V)
    (S : Finset (ContractVertex A B)) :
    outsidePart A B (outsidePreimage A B S) = outsidePreimage A B S := by
  apply Finset.filter_eq_self.mpr
  intro v hv
  exact ((mem_outsidePreimage_iff A B S v).mp hv).2

theorem outsideImage_outsidePreimage_card (A B : Finset V)
    (S : Finset (ContractVertex A B)) :
    (outsideImage A B (outsidePreimage A B S)).card =
      (outsidePreimage A B S).card := by
  rw [outsideImage_card, outsidePart_outsidePreimage]

theorem mem_eq_left_or_eq_right_or_mem_outsideImage (A B : Finset V)
    (hAB : Disjoint A B) {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (S : Finset (ContractVertex A B)) {x : ContractVertex A B} (hx : x ∈ S) :
    x = contract A B a ∨ x = contract A B b ∨
      x ∈ outsideImage A B (outsidePreimage A B S) := by
  obtain ⟨v, hv⟩ := x.property
  have hcv : contract A B v = x := by
    apply Subtype.ext
    exact hv
  by_cases hvA : v ∈ A
  · left
    exact hcv.symm.trans (contract_eq_of_mem_left A B hvA ha)
  · by_cases hvB : v ∈ B
    · right; left
      exact hcv.symm.trans (contract_eq_of_mem_right A B hAB hvB hb)
    · right; right
      simp only [outsideImage, Finset.mem_image]
      refine ⟨v, ?_, hcv⟩
      apply (mem_outsidePart_iff A B (outsidePreimage A B S) v).mpr
      exact ⟨(mem_outsidePreimage_iff A B S v).mpr ⟨hcv.symm ▸ hx, hvA, hvB⟩, hvA, hvB⟩

theorem contracted_set_eq_outside_of_neither (A B : Finset V)
    (hAB : Disjoint A B) {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (S : Finset (ContractVertex A B))
    (haS : contract A B a ∉ S) (hbS : contract A B b ∉ S) :
    S = outsideImage A B (outsidePreimage A B S) := by
  apply Finset.Subset.antisymm
  · intro x hx
    rcases mem_eq_left_or_eq_right_or_mem_outsideImage A B hAB ha hb S hx with
      rfl | rfl | hx
    · exact (haS hx).elim
    · exact (hbS hx).elim
    · exact hx
  · exact outsideImage_outsidePreimage_subset A B S

theorem contracted_set_eq_insert_left (A B : Finset V)
    (hAB : Disjoint A B) {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (S : Finset (ContractVertex A B))
    (haS : contract A B a ∈ S) (hbS : contract A B b ∉ S) :
    S = insert (contract A B a) (outsideImage A B (outsidePreimage A B S)) := by
  apply Finset.Subset.antisymm
  · intro x hx
    rcases mem_eq_left_or_eq_right_or_mem_outsideImage A B hAB ha hb S hx with
      rfl | rfl | hx
    · simp
    · exact (hbS hx).elim
    · simp [hx]
  · intro x hx
    simp only [Finset.mem_insert] at hx
    exact hx.elim (fun h ↦ h ▸ haS)
      (fun h ↦ outsideImage_outsidePreimage_subset A B S h)

theorem contracted_set_eq_insert_right (A B : Finset V)
    (hAB : Disjoint A B) {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (S : Finset (ContractVertex A B))
    (haS : contract A B a ∉ S) (hbS : contract A B b ∈ S) :
    S = insert (contract A B b) (outsideImage A B (outsidePreimage A B S)) := by
  apply Finset.Subset.antisymm
  · intro x hx
    rcases mem_eq_left_or_eq_right_or_mem_outsideImage A B hAB ha hb S hx with
      rfl | rfl | hx
    · exact (haS hx).elim
    · simp
    · simp [hx]
  · intro x hx
    simp only [Finset.mem_insert] at hx
    exact hx.elim (fun h ↦ h ▸ hbS)
      (fun h ↦ outsideImage_outsidePreimage_subset A B S h)

theorem contracted_set_eq_insert_both (A B : Finset V)
    (hAB : Disjoint A B) {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (S : Finset (ContractVertex A B))
    (haS : contract A B a ∈ S) (hbS : contract A B b ∈ S) :
    S = insert (contract A B a)
      (insert (contract A B b) (outsideImage A B (outsidePreimage A B S))) := by
  apply Finset.Subset.antisymm
  · intro x hx
    rcases mem_eq_left_or_eq_right_or_mem_outsideImage A B hAB ha hb S hx with
      rfl | rfl | hx <;> simp_all
  · intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with h | h | h
    · exact h ▸ haS
    · exact h ▸ hbS
    · exact outsideImage_outsidePreimage_subset A B S h

theorem outsidePreimage_card_eq_of_neither (A B : Finset V)
    (hAB : Disjoint A B) {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (S : Finset (ContractVertex A B))
    (haS : contract A B a ∉ S) (hbS : contract A B b ∉ S) :
    (outsidePreimage A B S).card = S.card := by
  have hset := contracted_set_eq_outside_of_neither A B hAB ha hb S haS hbS
  have hcard := congrArg Finset.card hset
  have hout := outsideImage_outsidePreimage_card A B S
  omega

theorem outsidePreimage_card_add_one_of_left (A B : Finset V)
    (hAB : Disjoint A B) {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (S : Finset (ContractVertex A B))
    (haS : contract A B a ∈ S) (hbS : contract A B b ∉ S) :
    (outsidePreimage A B S).card + 1 = S.card := by
  have hset := contracted_set_eq_insert_left A B hAB ha hb S haS hbS
  have hcard := congrArg Finset.card hset
  have hins := insert_left_outsideImage_card A B (outsidePreimage A B S) ha
  rw [outsidePart_outsidePreimage] at hins
  omega

theorem outsidePreimage_card_add_one_of_right (A B : Finset V)
    (hAB : Disjoint A B) {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (S : Finset (ContractVertex A B))
    (haS : contract A B a ∉ S) (hbS : contract A B b ∈ S) :
    (outsidePreimage A B S).card + 1 = S.card := by
  have hset := contracted_set_eq_insert_right A B hAB ha hb S haS hbS
  have hcard := congrArg Finset.card hset
  have hins := insert_right_outsideImage_card A B (outsidePreimage A B S) hAB hb
  rw [outsidePart_outsidePreimage] at hins
  omega

theorem outsidePreimage_card_add_two_of_both (A B : Finset V)
    (hAB : Disjoint A B) {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (S : Finset (ContractVertex A B))
    (haS : contract A B a ∈ S) (hbS : contract A B b ∈ S) :
    (outsidePreimage A B S).card + 2 = S.card := by
  have hset := contracted_set_eq_insert_both A B hAB ha hb S haS hbS
  have hcard := congrArg Finset.card hset
  have hins := insert_both_outsideImage_card A B (outsidePreimage A B S) hAB ha hb
  rw [outsidePart_outsidePreimage] at hins
  omega

end Cardinalities

section WitnessLift

/-- The common 0/1/2-contracted-vertex witness lift.  The cycle classification
is supplied separately: an independent intersection of size `p` must be one
of the two alternating sides.  When it is smaller, dropping the cycle part
costs at most `p-1`; when it is a full side, its entire fiber can safely be
replaced by the corresponding contracted vertex. -/
theorem exists_contracted_independent_witness
    (G : SimpleGraph V) (A B I : Finset V) (p : ℕ) (hAB : Disjoint A B)
    {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (hp : 1 ≤ p) (hAcard : A.card = p) (hBcard : B.card = p)
    (S : Finset (ContractVertex A B))
    (hI : G.IsIndepSet I)
    (houtside : ∀ v ∈ I, v ∉ A → v ∉ B → contract A B v ∈ S)
    (hcycle : (cyclePart A B I).card ≤ p)
    (hfull : (cyclePart A B I).card = p →
      cyclePart A B I = A ∨ cyclePart A B I = B)
    (hleft : cyclePart A B I = A → contract A B a ∈ S)
    (hright : cyclePart A B I = B → contract A B b ∈ S) :
    ∃ J : Finset (ContractVertex A B), J ⊆ S ∧
      (contractGraph G A B).IsIndepSet J ∧ I.card ≤ J.card + (p - 1) := by
  have houtside_subset : outsideImage A B I ⊆ S := by
    intro x hx
    simp only [outsideImage, Finset.mem_image] at hx
    rcases hx with ⟨v, hv, rfl⟩
    have hv' := (mem_outsidePart_iff A B I v).mp hv
    exact houtside v hv'.1 hv'.2.1 hv'.2.2
  by_cases hsmall : (cyclePart A B I).card < p
  · refine ⟨outsideImage A B I, houtside_subset,
      isIndepSet_outsideImage G A B I hI, ?_⟩
    have hdecomp := outside_cycle_card_decomposition A B I
    have himage := outsideImage_card A B I
    omega
  · have heq : (cyclePart A B I).card = p := by omega
    rcases hfull heq with hKA | hKB
    · let J := insert (contract A B a) (outsideImage A B I)
      have hAI : A ⊆ I := by
        intro v hv
        have hvK : v ∈ cyclePart A B I := by simpa [hKA] using hv
        exact (Finset.mem_inter.mp hvK).1
      refine ⟨J, ?_, isIndepSet_insert_left G A B I ha hAI hI, ?_⟩
      · intro x hx
        simp only [J, Finset.mem_insert] at hx
        exact hx.elim (fun h ↦ h ▸ hleft hKA) (fun h ↦ houtside_subset h)
      · have hdecomp := outside_cycle_card_decomposition A B I
        have hJcard := insert_left_outsideImage_card A B I ha
        dsimp only [J]
        rw [hKA, hAcard] at hdecomp
        omega
    · let J := insert (contract A B b) (outsideImage A B I)
      have hBI : B ⊆ I := by
        intro v hv
        have hvK : v ∈ cyclePart A B I := by simpa [hKB] using hv
        exact (Finset.mem_inter.mp hvK).1
      refine ⟨J, ?_, isIndepSet_insert_right G A B I hAB hb hBI hI, ?_⟩
      · intro x hx
        simp only [J, Finset.mem_insert] at hx
        exact hx.elim (fun h ↦ h ▸ hright hKB) (fun h ↦ houtside_subset h)
      · have hdecomp := outside_cycle_card_decomposition A B I
        have hJcard := insert_right_outsideImage_card A B I hAB hb
        dsimp only [J]
        rw [hKB, hBcard] at hdecomp
        omega

end WitnessLift

end Erdos922EvenHole

open SimpleGraph

namespace Erdos922
namespace EvenHole

open scoped Classical

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

abbrev CV (A B : Finset V) := Erdos922EvenHole.ContractVertex A B
abbrev qmap (A B : Finset V) := Erdos922EvenHole.contract A B
abbrev qgraph (G : SimpleGraph V) (A B : Finset V) :=
  Erdos922EvenHole.contractGraph G A B

open Erdos922EvenHole

/-- The contraction map is a graph homomorphism when its two nontrivial
fibers are independent. -/
def contractionHom (G : SimpleGraph V) (A B : Finset V) (hAB : Disjoint A B)
    (hA : G.IsIndepSet A) (hB : G.IsIndepSet B) : G →g qgraph G A B where
  toFun := qmap A B
  map_rel' := by
    intro u v huv
    apply SimpleGraph.map_adj_apply' huv
    intro heq
    by_cases huA : u ∈ A
    · have hpv : preContract A B v = Sum.inr false := by
        have hval := congrArg Subtype.val heq
        simpa [qmap, contract, preContract, huA] using hval.symm
      have hvA := (preContract_eq_inr_false_iff A B v).mp hpv
      exact hA huA hvA huv.ne huv
    · by_cases huB : u ∈ B
      · have hpv : preContract A B v = Sum.inr true := by
          have hval := congrArg Subtype.val heq
          simpa [qmap, contract, preContract, huA, huB] using hval.symm
        have hvB := (preContract_eq_inr_true_iff A B hAB v).mp hpv
        exact hB huB hvB huv.ne huv
      · have hpv : preContract A B v = Sum.inl u := by
          have hval := congrArg Subtype.val heq
          simpa [qmap, contract, preContract, huA, huB] using hval.symm
        have hvu := (preContract_eq_inl_iff A B v u).mp hpv |>.1
        exact huv.ne hvu.symm

 theorem chromaticNumber_le_contraction (G : SimpleGraph V) (A B : Finset V)
    (hAB : Disjoint A B) (hA : G.IsIndepSet A) (hB : G.IsIndepSet B) :
    G.chromaticNumber ≤ (qgraph G A B).chromaticNumber :=
 SimpleGraph.chromaticNumber_mono_of_hom (contractionHom G A B hAB hA hB)

/-- The exact abstract information about an induced even cycle used by the
contraction argument. -/
structure Configuration (G : SimpleGraph V) (A B : Finset V) (p : ℕ) : Prop where
  disjoint : Disjoint A B
  two_le : 2 ≤ p
  card_left : A.card = p
  card_right : B.card = p
  indep_left : G.IsIndepSet A
  indep_right : G.IsIndepSet B
  cycle_bound : ∀ I : Finset V, I ⊆ A ∪ B → G.IsIndepSet I → I.card ≤ p
  cycle_eq_of_card : ∀ I : Finset V, I ⊆ A ∪ B → G.IsIndepSet I →
    I.card = p → I = A ∨ I = B

theorem potential_le_of_witness_lift
    (G : SimpleGraph V) (A B : Finset V) (p : ℕ)
    (S : Finset (CV A B)) (H : Finset V) (hp : 1 ≤ p)
    (hcard : (H.card : ℤ) = (S.card : ℤ) + 2 * (p : ℤ) - 2)
    (hlift : ∀ I : Finset V, I ⊆ H → G.IsIndepSet I →
      ∃ J : Finset (CV A B), J ⊆ S ∧ (qgraph G A B).IsIndepSet J ∧
        I.card ≤ J.card + (p - 1)) :
    Erdos922.potential (qgraph G A B) S ≤ Erdos922.potential G H := by
  obtain ⟨I, hIH, hIind, hIcard⟩ := Erdos922.exists_maximum_independent_subset G H
  obtain ⟨J, hJS, hJind, hIJ⟩ := hlift I hIH hIind
  have hJalpha : J.card ≤ Erdos922.alphaOn (qgraph G A B) S :=
    Erdos922.card_le_alphaOn hJS hJind
  rw [Erdos922.potential, Erdos922.potential, ← hIcard]
  omega

/-- Every independent set in a proposed lifted vertex set gives the cycle
classification required by the witness lift. -/
theorem cyclePart_data (G : SimpleGraph V) (A B I : Finset V) (p : ℕ)
    (hC : Configuration G A B p) (hI : G.IsIndepSet I) :
    (cyclePart A B I).card ≤ p ∧
      ((cyclePart A B I).card = p → cyclePart A B I = A ∨ cyclePart A B I = B) := by
  have hsub : cyclePart A B I ⊆ A ∪ B := by simp [cyclePart]
  have hind : G.IsIndepSet (cyclePart A B I) := hI.mono (by simp [cyclePart])
  exact ⟨hC.cycle_bound _ hsub hind, hC.cycle_eq_of_card _ hsub hind⟩

/-- The old outside vertices are disjoint from the old cycle. -/
theorem outsidePreimage_disjoint_cycle (A B : Finset V) (S : Finset (CV A B)) :
    Disjoint (outsidePreimage A B S) (A ∪ B) := by
  rw [Finset.disjoint_left]
  intro v hvT hvC
  have hvout := (mem_outsidePreimage_iff A B S v).mp hvT
  rcases Finset.mem_union.mp hvC with hvA | hvB
  · exact hvout.2.1 hvA
  · exact hvout.2.2 hvB

/-- All cycle cardinalities needed in the three lift cases. -/
theorem cycle_card (G : SimpleGraph V) (A B : Finset V) (p : ℕ)
    (hC : Configuration G A B p) : (A ∪ B).card = 2 * p := by
  rw [Finset.card_union_of_disjoint hC.disjoint, hC.card_left, hC.card_right]
  omega

/-- Contracting an abstract even-hole configuration cannot increase Folkman's
maximum signed deficiency. -/
theorem f_contraction_le (G : SimpleGraph V) (A B : Finset V) (p : ℕ)
    (hC : Configuration G A B p) :
    Erdos922.f (qgraph G A B) ≤ Erdos922.f G := by
  have hp : 1 ≤ p := (by omega : 1 ≤ 2).trans hC.two_le
  have hAne : A.Nonempty := Finset.card_pos.mp (by rw [hC.card_left]; exact Nat.zero_lt_of_lt hp)
  have hBne : B.Nonempty := Finset.card_pos.mp (by rw [hC.card_right]; exact Nat.zero_lt_of_lt hp)
  obtain ⟨a, ha⟩ := hAne
  obtain ⟨b, hb⟩ := hBne
  rw [Erdos922.f_le_iff_forall_potential_le]
  intro S
  let T := outsidePreimage A B S
  let C := A ∪ B
  have hTC : Disjoint T C := outsidePreimage_disjoint_cycle A B S
  have hCcard : C.card = 2 * p := cycle_card G A B p hC
  by_cases haS : contract A B a ∈ S
  · by_cases hbS : contract A B b ∈ S
    · -- Both contracted vertices occur: lift all of the old cycle.
      let H := T ∪ C
      have hTcard := outsidePreimage_card_add_two_of_both
        A B hC.disjoint ha hb S haS hbS
      have hHcardNat : H.card = T.card + C.card := by
        exact Finset.card_union_of_disjoint hTC
      have hHcard : (H.card : ℤ) = (S.card : ℤ) + 2 * (p : ℤ) - 2 := by
        have hTcardZ : (T.card : ℤ) + 2 = (S.card : ℤ) := by exact_mod_cast hTcard
        have hCcardZ : (C.card : ℤ) = 2 * (p : ℤ) := by exact_mod_cast hCcard
        have hHcardZ : (H.card : ℤ) = (T.card : ℤ) + C.card := by
          exact_mod_cast hHcardNat
        omega
      have hlift : ∀ I : Finset V, I ⊆ H → G.IsIndepSet I →
          ∃ J : Finset (CV A B), J ⊆ S ∧ (qgraph G A B).IsIndepSet J ∧
            I.card ≤ J.card + (p - 1) := by
        intro I hIH hI
        have hout : ∀ v ∈ I, v ∉ A → v ∉ B → contract A B v ∈ S := by
          intro v hvI hvA hvB
          have hvH := hIH hvI
          simp only [H, Finset.mem_union] at hvH
          rcases hvH with hvT | hvC
          · exact (mem_outsidePreimage_iff A B S v).mp hvT |>.1
          · rcases Finset.mem_union.mp hvC with hv | hv
            · exact (hvA hv).elim
            · exact (hvB hv).elim
        have hd := cyclePart_data G A B I p hC hI
        exact exists_contracted_independent_witness G A B I p hC.disjoint ha hb
          hp hC.card_left hC.card_right S hI hout hd.1 hd.2
          (fun _ ↦ haS) (fun _ ↦ hbS)
      exact (potential_le_of_witness_lift G A B p S H hp hHcard hlift).trans
        (Erdos922.potential_le_f G H)
    · -- Only the left contracted vertex occurs: delete one right vertex.
      let D := C.erase b
      let H := T ∪ D
      have hbC : b ∈ C := Finset.mem_union_right A hb
      have hDcard : D.card = 2 * p - 1 := by
        dsimp only [D]
        rw [Finset.card_erase_of_mem hbC, hCcard]
      have hTD : Disjoint T D := hTC.mono_right (Finset.erase_subset _ _)
      have hTcard := outsidePreimage_card_add_one_of_left
        A B hC.disjoint ha hb S haS hbS
      have hHcardNat : H.card = T.card + D.card := Finset.card_union_of_disjoint hTD
      have hHcard : (H.card : ℤ) = (S.card : ℤ) + 2 * (p : ℤ) - 2 := by
        have hTcardZ : (T.card : ℤ) + 1 = (S.card : ℤ) := by exact_mod_cast hTcard
        have hDcardZ : (D.card : ℤ) = 2 * (p : ℤ) - 1 := by
          rw [hDcard, Nat.cast_sub (by omega : 1 ≤ 2 * p)]
          norm_num
        have hHcardZ : (H.card : ℤ) = (T.card : ℤ) + D.card := by
          exact_mod_cast hHcardNat
        omega
      have hbA : b ∉ A := fun hba ↦ Finset.disjoint_left.mp hC.disjoint hba hb
      have hlift : ∀ I : Finset V, I ⊆ H → G.IsIndepSet I →
          ∃ J : Finset (CV A B), J ⊆ S ∧ (qgraph G A B).IsIndepSet J ∧
            I.card ≤ J.card + (p - 1) := by
        intro I hIH hI
        have hout : ∀ v ∈ I, v ∉ A → v ∉ B → contract A B v ∈ S := by
          intro v hvI hvA hvB
          have hvH := hIH hvI
          simp only [H, Finset.mem_union] at hvH
          rcases hvH with hvT | hvD
          · exact (mem_outsidePreimage_iff A B S v).mp hvT |>.1
          · have hvC : v ∈ C := (Finset.mem_erase.mp hvD).2
            rcases Finset.mem_union.mp hvC with hv | hv
            · exact (hvA hv).elim
            · exact (hvB hv).elim
        have hd := cyclePart_data G A B I p hC hI
        apply exists_contracted_independent_witness G A B I p hC.disjoint ha hb
          hp hC.card_left hC.card_right S hI hout hd.1 hd.2
          (fun _ ↦ haS)
        intro hKB
        exfalso
        have hbK : b ∈ cyclePart A B I := by simpa [hKB] using hb
        have hbI : b ∈ I := (Finset.mem_inter.mp hbK).1
        have hbH := hIH hbI
        rcases Finset.mem_union.mp hbH with hbT | hbD
        · exact ((mem_outsidePreimage_iff A B S b).mp hbT).2.2 hb
        · exact (Finset.mem_erase.mp hbD).1 rfl
      exact (potential_le_of_witness_lift G A B p S H hp hHcard hlift).trans
        (Erdos922.potential_le_f G H)
  · by_cases hbS : contract A B b ∈ S
    · -- Only the right contracted vertex occurs: delete one left vertex.
      let D := C.erase a
      let H := T ∪ D
      have haC : a ∈ C := Finset.mem_union_left B ha
      have hDcard : D.card = 2 * p - 1 := by
        dsimp only [D]
        rw [Finset.card_erase_of_mem haC, hCcard]
      have hTD : Disjoint T D := hTC.mono_right (Finset.erase_subset _ _)
      have hTcard := outsidePreimage_card_add_one_of_right
        A B hC.disjoint ha hb S haS hbS
      have hHcardNat : H.card = T.card + D.card := Finset.card_union_of_disjoint hTD
      have hHcard : (H.card : ℤ) = (S.card : ℤ) + 2 * (p : ℤ) - 2 := by
        have hTcardZ : (T.card : ℤ) + 1 = (S.card : ℤ) := by exact_mod_cast hTcard
        have hDcardZ : (D.card : ℤ) = 2 * (p : ℤ) - 1 := by
          rw [hDcard, Nat.cast_sub (by omega : 1 ≤ 2 * p)]
          norm_num
        have hHcardZ : (H.card : ℤ) = (T.card : ℤ) + D.card := by
          exact_mod_cast hHcardNat
        omega
      have hlift : ∀ I : Finset V, I ⊆ H → G.IsIndepSet I →
          ∃ J : Finset (CV A B), J ⊆ S ∧ (qgraph G A B).IsIndepSet J ∧
            I.card ≤ J.card + (p - 1) := by
        intro I hIH hI
        have hout : ∀ v ∈ I, v ∉ A → v ∉ B → contract A B v ∈ S := by
          intro v hvI hvA hvB
          have hvH := hIH hvI
          simp only [H, Finset.mem_union] at hvH
          rcases hvH with hvT | hvD
          · exact (mem_outsidePreimage_iff A B S v).mp hvT |>.1
          · have hvC : v ∈ C := (Finset.mem_erase.mp hvD).2
            rcases Finset.mem_union.mp hvC with hv | hv
            · exact (hvA hv).elim
            · exact (hvB hv).elim
        have hd := cyclePart_data G A B I p hC hI
        apply exists_contracted_independent_witness G A B I p hC.disjoint ha hb
          hp hC.card_left hC.card_right S hI hout hd.1 hd.2
        · intro hKA
          exfalso
          have haK : a ∈ cyclePart A B I := by simpa [hKA] using ha
          have haI : a ∈ I := (Finset.mem_inter.mp haK).1
          have haH := hIH haI
          rcases Finset.mem_union.mp haH with haT | haD
          · exact ((mem_outsidePreimage_iff A B S a).mp haT).2.1 ha
          · exact (Finset.mem_erase.mp haD).1 rfl
        · exact fun _ ↦ hbS
      exact (potential_le_of_witness_lift G A B p S H hp hHcard hlift).trans
        (Erdos922.potential_le_f G H)
    · -- Neither contracted vertex occurs: no cycle vertices are lifted.
      let H := T
      have hTcard := outsidePreimage_card_eq_of_neither
        A B hC.disjoint ha hb S haS hbS
      have hHcard : (H.card : ℤ) = (S.card : ℤ) + 2 * (1 : ℤ) - 2 := by
        dsimp only [H]
        have hTcardZ : (T.card : ℤ) = (S.card : ℤ) := by exact_mod_cast hTcard
        omega
      have hlift : ∀ I : Finset V, I ⊆ H → G.IsIndepSet I →
          ∃ J : Finset (CV A B), J ⊆ S ∧ (qgraph G A B).IsIndepSet J ∧
            I.card ≤ J.card + (1 - 1) := by
        intro I hIH hI
        have houtpart : outsidePart A B I = I := by
          apply Finset.filter_eq_self.mpr
          intro v hvI
          have hvT : v ∈ T := hIH hvI
          exact ((mem_outsidePreimage_iff A B S v).mp hvT).2
        refine ⟨outsideImage A B I, ?_, isIndepSet_outsideImage G A B I hI, ?_⟩
        · intro x hx
          simp only [outsideImage, Finset.mem_image] at hx
          rcases hx with ⟨v, hv, rfl⟩
          have hvI := (mem_outsidePart_iff A B I v).mp hv |>.1
          exact (mem_outsidePreimage_iff A B S v).mp (hIH hvI) |>.1
        · have hj := outsideImage_card A B I
          rw [houtpart] at hj
          omega
      exact (potential_le_of_witness_lift G A B 1 S H (by omega) hHcard hlift).trans
        (Erdos922.potential_le_f G H)

/-- A genuine contraction is strictly smaller: the left fiber alone contains
at least two vertices. -/
theorem card_contractVertex_lt (G : SimpleGraph V) (A B : Finset V) (p : ℕ)
    (hC : Configuration G A B p) :
    Fintype.card (CV A B) < Fintype.card V := by
  have hle : Fintype.card (CV A B) ≤ Fintype.card V :=
    Fintype.card_range_le (preContract A B)
  apply lt_of_le_of_ne hle
  intro heq
  have hcardEq : Fintype.card V = Fintype.card (CV A B) := heq.symm
  let e : V ≃ CV A B := Fintype.equivOfCardEq hcardEq
  have hsurj : Function.Surjective (contract A B) := by
    intro x
    obtain ⟨v, hv⟩ := x.property
    refine ⟨v, ?_⟩
    apply Subtype.ext
    exact hv
  have hinj : Function.Injective (contract A B) :=
    hsurj.injective_of_finite e
  have hp0 : 0 < p := lt_of_lt_of_le (by omega : 0 < 2) hC.two_le
  have hAne : A.Nonempty := Finset.card_pos.mp (hC.card_left.symm ▸ hp0)
  obtain ⟨a, ha⟩ := hAne
  have hsub : A ⊆ {a} := by
    intro v hv
    simp only [Finset.mem_singleton]
    apply hinj
    exact contract_eq_of_mem_left A B hv ha
  have hcardle := Finset.card_le_card hsub
  rw [hC.card_left] at hcardle
  simpa using hC.two_le.trans hcardle

/-- The promised structural consequence of minimal-counterexample induction:
a minimal counterexample to Folkman's bound has no abstract even-hole
configuration. -/
theorem no_configuration_of_minimal_counterexample
    (G : SimpleGraph V)
    (hminimal : ∀ {W : Type u} [Fintype W] [DecidableEq W]
      (H : SimpleGraph W), Fintype.card W < Fintype.card V →
        H.chromaticNumber ≤ ((Erdos922.f H).toNat + 2 : ℕ∞))
    (hcounter : ¬ G.chromaticNumber ≤ ((Erdos922.f G).toNat + 2 : ℕ∞)) :
    ¬ ∃ (A B : Finset V) (p : ℕ), Configuration G A B p := by
  rintro ⟨A, B, p, hC⟩
  have hsmall := card_contractVertex_lt G A B p hC
  have hmin := hminimal (qgraph G A B) hsmall
  have hchrom := chromaticNumber_le_contraction G A B hC.disjoint hC.indep_left hC.indep_right
  have hf := f_contraction_le G A B p hC
  have hnat : (Erdos922.f (qgraph G A B)).toNat ≤ (Erdos922.f G).toNat :=
    Int.toNat_le_toNat hf
  have henat : (((Erdos922.f (qgraph G A B)).toNat + 2 : ℕ) : ℕ∞) ≤
      ((Erdos922.f G).toNat + 2 : ℕ∞) := by
    exact_mod_cast Nat.add_le_add_right hnat 2
  exact hcounter (hchrom.trans (hmin.trans henat))

/-- The global maximum used by the endpoint/core file is the localized
maximum on the full vertex finset used by the minimal-counterexample file. -/
theorem f_eq_fOn_univ (G : SimpleGraph V) :
    Erdos922.f G = Erdos922FullB.fOn G Finset.univ := by
  rfl

/-- The final form consumed by the repository's strong-induction framework. -/
theorem no_configuration_of_orderMinimalCounterexample
    (G : SimpleGraph V) (hmin : Erdos922FullB.IsOrderMinimalCounterexample G) :
    ¬ ∃ (A B : Finset V) (p : ℕ), Configuration G A B p := by
  apply no_configuration_of_minimal_counterexample G
  · intro W _ _ H hcard
    have hsmall := hmin.smaller H hcard
    have hchrom := hsmall.chromaticNumber_le
    simpa only [Erdos922FullB.FolkmanBound, ← f_eq_fOn_univ,
      Nat.cast_add, Nat.cast_ofNat] using hchrom
  · intro hbound
    apply hmin.counterexample
    rw [Erdos922FullB.FolkmanBound, ← SimpleGraph.chromaticNumber_le_iff_colorable]
    simpa only [← f_eq_fOn_univ, Nat.cast_add, Nat.cast_ofNat] using hbound

end EvenHole
end Erdos922

open SimpleGraph

namespace Erdos922Diamond

universe u v

section MissingColor

variable {V : Type u} {G : SimpleGraph V} {x y : V}

/-- Folkman's missing-color recoloring.  The values of `c` at `x,y` are
irrelevant: the validation theorem asks only that it properly colors the
remaining vertices. -/
noncomputable def missingColorRecolor {α : Type v}
    [DecidableEq V] [DecidableEq α] [DecidableRel G.Adj]
    (c : V → α) (i : α) : V → Option α :=
  fun z ↦
    if z = y then none
    else if z = x then some i
    else if G.Adj x z ∧ c z = i then none
    else some (c z)

theorem missingColorRecolor_valid {α : Type v}
    [DecidableEq V] [DecidableEq α] [DecidableRel G.Adj]
    (hxy : G.Adj x y) (c : V → α) (i : α)
    (hc : ∀ ⦃a b⦄, G.Adj a b → a ≠ x → a ≠ y → b ≠ x → b ≠ y → c a ≠ c b)
    (hmiss : ∀ z, G.Adj x z → G.Adj y z → c z ≠ i) :
    ∀ ⦃a b⦄, G.Adj a b →
      missingColorRecolor (G := G) (x := x) (y := y) c i a ≠
        missingColorRecolor (G := G) (x := x) (y := y) c i b := by
  classical
  intro a b hab
  have habne : a ≠ b := hab.ne
  by_cases haY : a = y
  · subst a
    have hbY : b ≠ y := habne.symm
    by_cases hbX : b = x
    · subst b
      simp [missingColorRecolor, hxy.ne, hxy.ne.symm]
    · by_cases hbR : G.Adj x b ∧ c b = i
      · exact (hmiss b hbR.1 hab hbR.2).elim
      · simp [missingColorRecolor, hbY, hbX, hbR]
  · by_cases hbY : b = y
    · subst b
      by_cases haX : a = x
      · subst a
        simp [missingColorRecolor, hxy.ne, hxy.ne.symm]
      · by_cases haR : G.Adj x a ∧ c a = i
        · exact (hmiss a haR.1 hab.symm haR.2).elim
        · simp [missingColorRecolor, haY, haX, haR]
    · by_cases haX : a = x
      · subst a
        have hbX : b ≠ x := habne.symm
        by_cases hbR : G.Adj x b ∧ c b = i
        · simp [missingColorRecolor, haY, hbY, hbX, hbR]
        · have hci : c b ≠ i := fun h ↦ hbR ⟨hab, h⟩
          simp [missingColorRecolor, haY, hbY, hbX, hbR, hci, hci.symm]
      · by_cases hbX : b = x
        · subst b
          by_cases haR : G.Adj x a ∧ c a = i
          · simp [missingColorRecolor, haY, haX, hbY, haR]
          · have hci : c a ≠ i := fun h ↦ haR ⟨hab.symm, h⟩
            simp [missingColorRecolor, haY, haX, hbY, haR, hci]
        · have hcAB : c a ≠ c b := hc hab haX haY hbX hbY
          by_cases haR : G.Adj x a ∧ c a = i <;>
            by_cases hbR : G.Adj x b ∧ c b = i
          · exact (hcAB (haR.2.trans hbR.2.symm)).elim
          · simp [missingColorRecolor, haY, haX, hbY, hbX, haR, hbR]
          · simp [missingColorRecolor, haY, haX, hbY, hbX, haR, hbR]
          · simpa [missingColorRecolor, haY, haX, hbY, hbX, haR, hbR] using hcAB

noncomputable def coloringOptionOfMissingCommonColor {α : Type v}
    [DecidableEq V] [DecidableEq α] [DecidableRel G.Adj]
    (hxy : G.Adj x y) (c : V → α) (i : α)
    (hc : ∀ ⦃a b⦄, G.Adj a b → a ≠ x → a ≠ y → b ≠ x → b ≠ y → c a ≠ c b)
    (hmiss : ∀ z, G.Adj x z → G.Adj y z → c z ≠ i) :
    G.Coloring (Option α) :=
  Coloring.mk (missingColorRecolor (G := G) (x := x) (y := y) c i)
    (fun {_ _} h ↦
      missingColorRecolor_valid (G := G) (x := x) (y := y) hxy c i hc hmiss h)

end MissingColor

section PairIdentification

variable {V : Type u} (x y : V)

/-- The vertices left after deleting the adjacent pair `x,y`. -/
abbrev DeletedPair := ({x, y}ᶜ : Set V)

/-- The vertex type after deleting `x,y` and using `u` as the representative
of the identified pair `u,v`. -/
abbrev IdentifiedPair (v : V) := {z : DeletedPair x y // z.1 ≠ v}

/-- Identify `v` with `u`, retaining `u` as the representative. -/
noncomputable def pairIdentify (u v : V) (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v) :
    DeletedPair x y → IdentifiedPair x y v := by
  classical
  exact fun z ↦ if hz : z.1 = v then
      ⟨⟨u, by simp [hux, huy]⟩, huv⟩
    else ⟨z, hz⟩

variable {x y : V} {G : SimpleGraph V} {u v : V}

/-- The graph obtained from `G - {x,y}` by identifying the nonadjacent
vertices `u,v`. -/
noncomputable def pairGraph (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v) :
    SimpleGraph (IdentifiedPair x y v) :=
  (G.induce ({x, y}ᶜ : Set V)).map (pairIdentify x y u v hux huy huv)

theorem pairIdentify_ne_of_adj
    (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v)
    (huvNA : ¬ G.Adj u v) {a b : DeletedPair x y}
    (hab : (G.induce ({x, y}ᶜ : Set V)).Adj a b) :
    pairIdentify x y u v hux huy huv a ≠
      pairIdentify x y u v hux huy huv b := by
  intro heq
  have heqv := congrArg (fun z : IdentifiedPair x y v ↦ z.1.1) heq
  by_cases ha : a.1 = v <;> by_cases hb : b.1 = v
  · exact hab.ne (Subtype.ext (ha.trans hb.symm))
  · simp only [pairIdentify, dif_pos ha, dif_neg hb] at heqv
    have hbu : b.1 = u := heqv.symm
    exact huvNA (by simpa [ha, hbu] using hab.symm)
  · simp only [pairIdentify, dif_neg ha, dif_pos hb] at heqv
    have hau : a.1 = u := heqv
    exact huvNA (by simpa [hau, hb] using hab)
  · simp only [pairIdentify, dif_neg ha, dif_neg hb] at heqv
    have habv : a.1 = b.1 := heqv
    exact hab.ne (Subtype.ext habv)

/-- Pull a coloring of the pair-identification graph back to a coloring of
`G - {x,y}`. -/
noncomputable def pairGraphPullColoring {α : Type v}
    (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v)
    (huvNA : ¬ G.Adj u v)
    (C : (pairGraph (G := G) hux huy huv).Coloring α) :
    (G.induce ({x, y}ᶜ : Set V)).Coloring α := by
  refine Coloring.mk (fun z ↦ C (pairIdentify x y u v hux huy huv z)) ?_
  intro a b hab
  exact C.valid (SimpleGraph.map_adj_apply' hab
    (pairIdentify_ne_of_adj hux huy huv huvNA hab))

/-- Extend the pulled-back coloring arbitrarily to `x,y`; these two values
are ignored by `missingColorRecolor_valid`. -/
noncomputable def pairGraphPullFunction {α : Type v}
    [DecidableEq V]
    (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v)
    (huvNA : ¬ G.Adj u v)
    (C : (pairGraph (G := G) hux huy huv).Coloring α) (fallback : α) : V → α :=
  fun z ↦ if hz : z ∈ ({x, y}ᶜ : Set V) then
    pairGraphPullColoring hux huy huv huvNA C ⟨z, hz⟩
  else fallback

theorem pairGraphPullFunction_valid {α : Type v}
    [DecidableEq V]
    (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v)
    (huvNA : ¬ G.Adj u v)
    (C : (pairGraph (G := G) hux huy huv).Coloring α) (fallback : α) :
    ∀ ⦃a b⦄, G.Adj a b → a ≠ x → a ≠ y → b ≠ x → b ≠ y →
      pairGraphPullFunction hux huy huv huvNA C fallback a ≠
        pairGraphPullFunction hux huy huv huvNA C fallback b := by
  intro a b hab hax hay hbx hby
  have hab' : (G.induce ({x, y}ᶜ : Set V)).Adj
      ⟨a, by simp [hax, hay]⟩ ⟨b, by simp [hbx, hby]⟩ := hab
  simpa [pairGraphPullFunction, hax, hay, hbx, hby] using
    (pairGraphPullColoring hux huy huv huvNA C).valid hab'

/-- A coloring in which `u,v` have the same color descends to the graph that
identifies them. -/
noncomputable def pairGraphColoringOfEqual {α : Type v}
    (hux : u ≠ x) (huy : u ≠ y) (hvx : v ≠ x) (hvy : v ≠ y)
    (huv : u ≠ v)
    (c : (G.induce ({x, y}ᶜ : Set V)).Coloring α)
    (heq : c ⟨u, by simp [hux, huy]⟩ = c ⟨v, by simp [hvx, hvy]⟩) :
    (pairGraph (G := G) hux huy huv).Coloring α := by
  classical
  let f := pairIdentify x y u v hux huy huv
  refine Coloring.mk (fun z ↦ c z.1) ?_
  intro a b hab
  rcases (SimpleGraph.map_adj' f (G.induce ({x, y}ᶜ : Set V)) a b).mp hab with
    ⟨-, a', b', hab', ha', hb'⟩
  have color_identify : ∀ z : DeletedPair x y, c z = c (f z).1 := by
    intro z
    by_cases hz : z.1 = v
    · have hzsub : z = ⟨v, by simp [hvx, hvy]⟩ := Subtype.ext hz
      subst z
      simpa [f, pairIdentify] using heq.symm
    · simp [f, pairIdentify, hz]
  rw [← ha', ← hb']
  exact fun h ↦ c.valid hab'
    ((color_identify a').trans (h.trans (color_identify b').symm))

/-- Pulling back a descended coloring recovers the original coloring, provided
the identified vertices had equal colors. -/
theorem pairGraph_roundTrip {α : Type v}
    [DecidableEq V]
    (hux : u ≠ x) (huy : u ≠ y) (hvx : v ≠ x) (hvy : v ≠ y)
    (huv : u ≠ v) (huvNA : ¬ G.Adj u v)
    (c : (G.induce ({x, y}ᶜ : Set V)).Coloring α)
    (heq : c ⟨u, by simp [hux, huy]⟩ = c ⟨v, by simp [hvx, hvy]⟩)
    (fallback : α) (z : V) (hzx : z ≠ x) (hzy : z ≠ y) :
    pairGraphPullFunction hux huy huv huvNA
      (pairGraphColoringOfEqual hux huy hvx hvy huv c heq) fallback z =
      c ⟨z, by simp [hzx, hzy]⟩ := by
  classical
  simp only [pairGraphPullFunction, Set.mem_compl_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, not_or, hzx, hzy, and_self, dif_pos]
  change c (pairIdentify x y u v hux huy huv ⟨z, by simp [hzx, hzy]⟩).1 =
    c ⟨z, by simp [hzx, hzy]⟩
  by_cases hzv : z = v
  · subst z
    simpa [pairIdentify] using heq
  · simp [pairIdentify, hzv]

/-- C1.2 of the diamond argument: if `G` cannot be colored with one fresh
color beyond `α`, then every color of a coloring of the pair-identification
graph occurs on the image of a common neighbor of `x,y`. -/
theorem everyColorOccursOnIdentifiedCommonNeighbors {α : Type v}
    [DecidableEq V] [DecidableEq α] [DecidableRel G.Adj]
    (hxy : G.Adj x y)
    (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v)
    (huvNA : ¬ G.Adj u v)
    (hncol : ¬ Nonempty (G.Coloring (Option α)))
    (C : (pairGraph (G := G) hux huy huv).Coloring α) (i : α) :
    ∃ z, G.Adj x z ∧ G.Adj y z ∧
      pairGraphPullFunction hux huy huv huvNA C i z = i := by
  by_contra! hmiss
  apply hncol
  exact ⟨coloringOptionOfMissingCommonColor hxy
    (pairGraphPullFunction hux huy huv huvNA C i) i
    (pairGraphPullFunction_valid hux huy huv huvNA C i) hmiss⟩

end PairIdentification

section Apex

variable {V : Type u} {G : SimpleGraph V} {x y : V}

/-- `G - {x,y}` with a new apex adjacent precisely to common neighbors of
`x,y`; `none` is the apex and `some z` is an old vertex. -/
def commonNeighborApexGraph : SimpleGraph (Option (DeletedPair x y)) where
  Adj a b := match a, b with
    | none, none => False
    | none, some z => G.Adj x z.1 ∧ G.Adj y z.1
    | some z, none => G.Adj x z.1 ∧ G.Adj y z.1
    | some a, some b => G.Adj a.1 b.1
  symm := ⟨by
    intro a b h
    cases a with
    | none =>
        cases b with
        | none => exact h
        | some b => exact h
    | some a =>
        cases b with
        | none => exact h
        | some b => exact h.symm⟩
  loopless := ⟨by
    intro a h
    cases a with
    | none => exact h
    | some a => exact h.ne rfl⟩

@[simp] theorem commonNeighborApexGraph_adj_apex {z : DeletedPair x y} :
    (commonNeighborApexGraph (G := G)).Adj none (some z) ↔
      G.Adj x z.1 ∧ G.Adj y z.1 := Iff.rfl

@[simp] theorem commonNeighborApexGraph_adj_old {a b : DeletedPair x y} :
    (commonNeighborApexGraph (G := G)).Adj (some a) (some b) ↔
      G.Adj a.1 b.1 := Iff.rfl

/-- Restriction of an apex-graph coloring to the old vertices. -/
noncomputable def apexOldColoring {α : Type v}
    (C : (commonNeighborApexGraph (G := G) (x := x) (y := y)).Coloring α) :
    (G.induce ({x, y}ᶜ : Set V)).Coloring α := by
  refine Coloring.mk (fun z ↦ C (some z)) ?_
  intro a b hab
  exact C.valid hab

/-- The apex color is absent on all common neighbors. -/
theorem apexColor_missing_on_commonNeighbors {α : Type v}
    (C : (commonNeighborApexGraph (G := G) (x := x) (y := y)).Coloring α)
    (z : DeletedPair x y) (hzx : G.Adj x z.1) (hzy : G.Adj y z.1) :
    C (some z) ≠ C none :=
  C.valid ⟨hzx, hzy⟩

/-- Common neighbors, packaged as a finite type for pigeonhole arguments. -/
abbrev CommonNeighbor (G : SimpleGraph V) (x y : V) :=
  {z : V // G.Adj x z ∧ G.Adj y z}

/-- A common neighbor is an old vertex of the apex graph. -/
def CommonNeighbor.toDeletedPair (z : CommonNeighbor G x y) : DeletedPair x y :=
  ⟨z.1, by simp [z.2.1.ne.symm, z.2.2.ne.symm]⟩

/-- If there are more common neighbors than colors, an apex coloring has two
distinct, nonadjacent common neighbors with the same color. -/
theorem exists_nonadjacent_commonNeighbors_sameColor
    [Fintype V] [Fintype α]
    (C : (commonNeighborApexGraph (G := G) (x := x) (y := y)).Coloring α)
    (hcard : Fintype.card α < Nat.card (CommonNeighbor G x y)) :
    ∃ u v : CommonNeighbor G x y, u.1 ≠ v.1 ∧ ¬ G.Adj u.1 v.1 ∧
      C (some u.toDeletedPair) = C (some v.toDeletedPair) := by
  classical
  letI : Fintype (CommonNeighbor G x y) := Fintype.ofFinite _
  let color : CommonNeighbor G x y → α := fun z ↦ C (some z.toDeletedPair)
  have hcard' : Fintype.card α < Fintype.card (CommonNeighbor G x y) := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  obtain ⟨u, v, huv, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt color hcard'
  have huvVal : u.1 ≠ v.1 := fun h ↦ huv (Subtype.ext h)
  refine ⟨u, v, huvVal, ?_, heq⟩
  intro hadj
  exact C.valid (v := some u.toDeletedPair) (w := some v.toDeletedPair) hadj heq

/-- The apex graph is not `α`-colorable once the common-neighbor set is
larger than `α`.  This is the complete pigeonhole + pair-identification +
missing-color portion of Folkman's diamond argument. -/
theorem commonNeighborApexGraph_not_colorable
    [Fintype V] [Fintype α] [DecidableEq V] [DecidableEq α]
    [DecidableRel G.Adj]
    (hxy : G.Adj x y)
    (hncol : ¬ Nonempty (G.Coloring (Option α)))
    (hcard : Fintype.card α < Nat.card (CommonNeighbor G x y)) :
    ¬ Nonempty
      ((commonNeighborApexGraph (G := G) (x := x) (y := y)).Coloring α) := by
  rintro ⟨C0⟩
  obtain ⟨u, v, huv, huvNA, heq⟩ :=
    exists_nonadjacent_commonNeighbors_sameColor C0 hcard
  have hux : u.1 ≠ x := u.2.1.ne.symm
  have huy : u.1 ≠ y := u.2.2.ne.symm
  have hvx : v.1 ≠ x := v.2.1.ne.symm
  have hvy : v.1 ≠ y := v.2.2.ne.symm
  let c := apexOldColoring C0
  have heq' : c ⟨u.1, by simp [hux, huy]⟩ =
      c ⟨v.1, by simp [hvx, hvy]⟩ := by
    change C0 (some ⟨u.1, by simp [hux, huy]⟩) =
      C0 (some ⟨v.1, by simp [hvx, hvy]⟩)
    simpa only [CommonNeighbor.toDeletedPair] using heq
  let CQ := pairGraphColoringOfEqual hux huy hvx hvy huv c heq'
  obtain ⟨z, hzx, hzy, hzcolor⟩ :=
    everyColorOccursOnIdentifiedCommonNeighbors hxy hux huy huv huvNA hncol CQ (C0 none)
  have hzX : z ≠ x := hzx.ne.symm
  have hzY : z ≠ y := hzy.ne.symm
  have hround := pairGraph_roundTrip hux huy hvx hvy huv huvNA c heq'
    (C0 none) z hzX hzY
  have hzEq : C0 (some (⟨z, by simp [hzX, hzY]⟩ : DeletedPair x y)) = C0 none := by
    change c ⟨z, by simp [hzX, hzY]⟩ = C0 none
    rw [← hround]
    exact hzcolor
  exact apexColor_missing_on_commonNeighbors C0
    (⟨z, by simp [hzX, hzY]⟩ : DeletedPair x y) hzx hzy hzEq

end Apex

section HajnalBridge

open Erdos922

variable {V : Type u} [Fintype V]

/-- The finite-set independence number agrees with Mathlib's independence
number on the induced subtype graph. -/
theorem indepNum_induce_finset_eq_alphaOn (G : SimpleGraph V) (S : Finset V) :
    (G.induce (S : Set V)).indepNum = alphaOn G S := by
  classical
  apply Nat.le_antisymm
  · obtain ⟨J, hJ⟩ := (G.induce (S : Set V)).exists_isNIndepSet_indepNum
    let I : Finset V := J.map ⟨Subtype.val, Subtype.val_injective⟩
    have hIS : I ⊆ S := by
      intro z hz
      simp only [I, Finset.mem_map, Function.Embedding.coeFn_mk] at hz
      obtain ⟨w, -, rfl⟩ := hz
      exact w.2
    have hI : G.IsIndepSet I := by
      rw [show (I : Set V) = Subtype.val '' (J : Set S) by
        simp only [I]
        rw [Finset.coe_map]
        rfl]
      rintro a ⟨a', ha', rfl⟩ b ⟨b', hb', rfl⟩ hab
      exact hJ.isIndepSet ha' hb' (Subtype.coe_ne_coe.mp hab)
    have hcard : I.card = (G.induce (S : Set V)).indepNum := by
      simpa [I] using hJ.card_eq
    rw [← hcard]
    exact card_le_alphaOn hIS hI
  · obtain ⟨I, hIS, hI, hcard⟩ := exists_maximum_independent_subset G S
    let J : Finset S := I.subtype (fun z ↦ z ∈ S)
    have hfilter : I.filter (fun z ↦ z ∈ S) = I :=
      Finset.filter_eq_self.mpr hIS
    have hJcard : J.card = alphaOn G S := by
      simpa [J, Finset.card_subtype, hfilter] using hcard
    have hJ : (G.induce (S : Set V)).IsIndepSet J := by
      intro a ha b hb hab
      exact hI (by simpa [J] using ha) (by simpa [J] using hb)
        (Subtype.coe_ne_coe.mpr hab)
    rw [← hJcard]
    exact hJ.card_le_indepNum

/-- Finset form of Hajnal's lemma, ready for the `J \ A` set in the diamond
argument. -/
theorem exists_mem_all_maximum_independent_subset
    (G : SimpleGraph V) (U : Finset V)
    (hlarge : U.card < 2 * alphaOn G U) :
    ∃ q ∈ U, ∀ I : Finset V, I ⊆ U → G.IsIndepSet I →
      I.card = alphaOn G U → q ∈ I := by
  classical
  letI : Fintype U := Fintype.ofFinite U
  have hcardU : Fintype.card U = U.card := Fintype.card_coe U
  have hindep : (G.induce (U : Set V)).indepNum = alphaOn G U :=
    indepNum_induce_finset_eq_alphaOn G U
  obtain ⟨q, hq⟩ :=
    (G.induce (U : Set V)).exists_mem_all_maximumIndepSet_of_card_lt_two_mul_indepNum
      (by simpa [hcardU, hindep] using hlarge)
  refine ⟨q.1, q.2, ?_⟩
  intro I hIU hI hIcard
  let Isub : Finset U := I.subtype (fun z ↦ z ∈ U)
  have hfilter : I.filter (fun z ↦ z ∈ U) = I :=
    Finset.filter_eq_self.mpr hIU
  have hIsubCard : Isub.card = alphaOn G U := by
    simpa [Isub, Finset.card_subtype, hfilter] using hIcard
  have hIsubIndep : (G.induce (U : Set V)).IsIndepSet Isub := by
    intro a ha b hb hab
    exact hI (by simpa [Isub] using ha) (by simpa [Isub] using hb)
      (Subtype.coe_ne_coe.mpr hab)
  have hmax : (G.induce (U : Set V)).IsMaximumIndepSet Isub := by
    refine ⟨hIsubIndep, ?_⟩
    intro T hT
    rw [hIsubCard, ← hindep]
    exact hT.card_le_indepNum
  have hqI : q ∈ Isub := hq Isub hmax
  simpa [Isub] using hqI

/-- Finset of common neighbors of an edge. -/
def commonNeighborFinset (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) : Finset V :=
  Finset.univ.filter fun z ↦ G.Adj x z ∧ G.Adj y z

@[simp] theorem mem_commonNeighborFinset {G : SimpleGraph V}
    [DecidableRel G.Adj] {x y z : V} :
    z ∈ commonNeighborFinset G x y ↔ G.Adj x z ∧ G.Adj y z := by
  simp [commonNeighborFinset]

/-- The final Hajnal contradiction in the no-diamond argument.  The inputs
are exactly the properties established for the old-vertex witness `J` of the
apex graph: it attains `f(G)`, deleting common neighbors does not lower its
independence number, and the remaining set has size less than twice that
number. -/
theorem hajnal_apexWitness_contradiction
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    (x y : V) (J : Finset V)
    (hxy : G.Adj x y) (hxJ : x ∉ J) (hyJ : y ∉ J)
    (halpha : alphaOn G (J \ commonNeighborFinset G x y) = alphaOn G J)
    (hlarge : (J \ commonNeighborFinset G x y).card <
      2 * alphaOn G (J \ commonNeighborFinset G x y))
    (hmax : potential G J = f G) : False := by
  classical
  let A := commonNeighborFinset G x y
  let U := J \ A
  let a := alphaOn G J
  obtain ⟨q, hqU, hqall⟩ :=
    exists_mem_all_maximum_independent_subset G U (by simpa [U, A] using hlarge)
  have hqJ : q ∈ J := (Finset.mem_sdiff.mp hqU).1
  have hqx : q ≠ x := fun h ↦ hxJ (h ▸ hqJ)
  have hqy : q ≠ y := fun h ↦ hyJ (h ▸ hqJ)
  let H : Finset V := insert x (insert y (J.erase q))
  have hHcard : H.card = J.card + 1 := by
    have herase := Finset.card_erase_add_one hqJ
    simp [H, hxJ, hyJ, hqJ, hxy.ne, hxy.ne.symm, hqx, hqy]
    omega
  have hpH := potential_le_f G H
  rw [← hmax] at hpH
  have halphaH : a + 1 ≤ alphaOn G H := by
    rw [potential, potential, hHcard] at hpH
    simp only [a]
    omega
  obtain ⟨I, hIH, hI, hIcard⟩ := exists_maximum_independent_subset G H
  have hIlarge : a + 1 ≤ I.card := by omega
  let P : Finset V := {x, y}
  let Iold : Finset V := I \ P
  have hIold_sub_erase : Iold ⊆ J.erase q := by
    intro z hz
    have hzI : z ∈ I := (Finset.mem_sdiff.mp hz).1
    have hzP : z ∉ P := (Finset.mem_sdiff.mp hz).2
    have hzH : z ∈ H := hIH hzI
    simp only [H, Finset.mem_insert] at hzH
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hzP
    have hzX : z ≠ x := fun h ↦ hzP (Or.inl h)
    have hzY : z ≠ y := fun h ↦ hzP (Or.inr h)
    have hzErase : z ∈ J.erase q := by
      rcases hzH with h | h | h
      · exact (hzX h).elim
      · exact (hzY h).elim
      · exact h
    exact hzErase
  have hIold_indep : G.IsIndepSet Iold := hI.mono (by simp [Iold])
  have hIold_le : Iold.card ≤ a := by
    exact card_le_alphaOn (hIold_sub_erase.trans (Finset.erase_subset q J)) hIold_indep
  have hIP_le : (I ∩ P).card ≤ 1 := by
    rw [Finset.card_le_one_iff]
    intro r s hr hs
    have hrI : r ∈ I := (Finset.mem_inter.mp hr).1
    have hsI : s ∈ I := (Finset.mem_inter.mp hs).1
    have hrP := (Finset.mem_inter.mp hr).2
    have hsP := (Finset.mem_inter.mp hs).2
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hrP hsP
    rcases hrP with rfl | rfl <;> rcases hsP with rfl | rfl
    · rfl
    · exact (hI hrI hsI hxy.ne hxy).elim
    · exact (hI hrI hsI hxy.ne.symm hxy.symm).elim
    · rfl
  have hsplit := Finset.card_sdiff_add_card_inter I P
  have hsplit' : Iold.card + (I ∩ P).card = I.card := by
    simpa [Iold] using hsplit
  have hIold_eq : Iold.card = a := by
    omega
  have hIP_nonempty : (I ∩ P).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he] at hsplit'
    simp only [Finset.card_empty, add_zero] at hsplit'
    omega
  obtain ⟨t, ht⟩ := hIP_nonempty
  obtain ⟨htI, htP⟩ := Finset.mem_inter.mp ht
  have ht : t = x ∨ t = y := by simpa [P] using htP
  have hIold_sub_U : Iold ⊆ U := by
    intro z hz
    have hzErase := hIold_sub_erase hz
    rw [Finset.mem_sdiff]
    refine ⟨(Finset.mem_erase.mp hzErase).2, ?_⟩
    intro hzA
    have hzCommon := mem_commonNeighborFinset.mp hzA
    have hzI : z ∈ I := (Finset.mem_sdiff.mp hz).1
    have htz : t ≠ z := by
      rintro rfl
      exact (Finset.mem_sdiff.mp hz).2 htP
    rcases ht with rfl | rfl
    · exact hI htI hzI htz hzCommon.1
    · exact hI htI hzI htz hzCommon.2
  have hIoldAlpha : Iold.card = alphaOn G U := by
    rw [hIold_eq]
    simpa [U, A, a] using halpha.symm
  have hqIold := hqall Iold hIold_sub_U hIold_indep hIoldAlpha
  exact (Finset.mem_erase.mp (hIold_sub_erase hqIold)).1 rfl

end HajnalBridge

end Erdos922Diamond

namespace Erdos922Diamond

section MinimalCounterexampleDiamond

open Erdos922

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {x y u v : V}

/-- The retained quotient vertices, embedded back into the original vertex type. -/
def identifiedPairEmbedding (x y v : V) : IdentifiedPair x y v ↪ V where
  toFun z := z.1.1
  inj' := fun _ _ h => Subtype.ext (Subtype.ext h)

/-- The old vertices represented by a quotient finset. -/
def pairLiftBase (x y v : V) (S : Finset (IdentifiedPair x y v)) : Finset V :=
  S.map (identifiedPairEmbedding x y v)

@[simp] theorem mem_pairLiftBase {S : Finset (IdentifiedPair x y v)} {z : V} :
    z ∈ pairLiftBase x y v S ↔
      ∃ q ∈ S, q.1.1 = z := by
  rw [pairLiftBase, Finset.mem_map]
  constructor
  · rintro ⟨q, hq, hqz⟩
    exact ⟨q, hq, hqz⟩
  · rintro ⟨q, hq, hqz⟩
    exact ⟨q, hq, hqz⟩

@[simp] theorem pairLiftBase_card (S : Finset (IdentifiedPair x y v)) :
    (pairLiftBase x y v S).card = S.card := by
  simp [pairLiftBase]

/-- The quotient representative corresponding to `u`. -/
def pairRepresentative (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v) :
    IdentifiedPair x y v :=
  ⟨⟨u, by simp [hux, huy]⟩, huv⟩

@[simp] theorem pairRepresentative_val
    (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v) :
    (pairRepresentative hux huy huv).1.1 = u := rfl

theorem pairRepresentative_mem_iff
    (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v)
    (S : Finset (IdentifiedPair x y v)) :
    pairRepresentative hux huy huv ∈ S ↔ u ∈ pairLiftBase x y v S := by
  constructor
  · intro h
    exact mem_pairLiftBase.mpr ⟨_, h, rfl⟩
  · intro h
    obtain ⟨q, hq, hqv⟩ := mem_pairLiftBase.mp h
    have : q = pairRepresentative hux huy huv := by
      exact Subtype.ext (Subtype.ext hqv)
    simpa [this] using hq

/-- The witness lift for a quotient finset.  The quotient representative is
expanded to `u,v`; when absent, `u` is used as the third vertex of the added
triangle. -/
def pairWitnessLift
    (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v)
    (S : Finset (IdentifiedPair x y v)) : Finset V :=
  if pairRepresentative hux huy huv ∈ S then
    insert x (insert y (insert v (pairLiftBase x y v S)))
  else
    insert x (insert y (insert u (pairLiftBase x y v S)))

theorem pairWitnessLift_card
    (hxy : G.Adj x y)
    (hxu : G.Adj x u) (hyu : G.Adj y u)
    (hxv : G.Adj x v) (hyv : G.Adj y v)
    (huv : u ≠ v)
    (S : Finset (IdentifiedPair x y v)) :
    (pairWitnessLift hxu.ne.symm hyu.ne.symm huv S).card = S.card + 3 := by
  classical
  have hux : u ≠ x := hxu.ne.symm
  have huy : u ≠ y := hyu.ne.symm
  have hvx : v ≠ x := hxv.ne.symm
  have hvy : v ≠ y := hyv.ne.symm
  have hxB : x ∉ pairLiftBase x y v S := by
    rintro hx
    obtain ⟨q, -, hq⟩ := mem_pairLiftBase.mp hx
    exact q.1.2 (by simp [hq])
  have hyB : y ∉ pairLiftBase x y v S := by
    rintro hy
    obtain ⟨q, -, hq⟩ := mem_pairLiftBase.mp hy
    exact q.1.2 (by simp [hq])
  have hvB : v ∉ pairLiftBase x y v S := by
    rintro hv
    obtain ⟨q, -, hq⟩ := mem_pairLiftBase.mp hv
    exact q.2 hq
  by_cases hw : pairRepresentative hux huy huv ∈ S
  · have hw' : pairRepresentative hxu.ne.symm hyu.ne.symm huv ∈ S := by
      simpa [pairRepresentative] using hw
    rw [pairWitnessLift, if_pos hw']
    have hvcard : (insert v (pairLiftBase x y v S)).card =
        (pairLiftBase x y v S).card + 1 := Finset.card_insert_of_notMem hvB
    have hycard : (insert y (insert v (pairLiftBase x y v S))).card =
        (insert v (pairLiftBase x y v S)).card + 1 := by
      apply Finset.card_insert_of_notMem
      simp [hyv.ne, hyB]
    have hxcard : (insert x (insert y (insert v (pairLiftBase x y v S)))).card =
        (insert y (insert v (pairLiftBase x y v S))).card + 1 := by
      apply Finset.card_insert_of_notMem
      simp [hxy.ne, hxv.ne, hxB]
    rw [hxcard, hycard, hvcard, pairLiftBase_card]
  · have huB : u ∉ pairLiftBase x y v S := by
      simpa [pairRepresentative_mem_iff hux huy huv S] using hw
    have hw' : pairRepresentative hxu.ne.symm hyu.ne.symm huv ∉ S := by
      simpa [pairRepresentative] using hw
    rw [pairWitnessLift, if_neg hw']
    have hucard : (insert u (pairLiftBase x y v S)).card =
        (pairLiftBase x y v S).card + 1 := Finset.card_insert_of_notMem huB
    have hycard : (insert y (insert u (pairLiftBase x y v S))).card =
        (insert u (pairLiftBase x y v S)).card + 1 := by
      apply Finset.card_insert_of_notMem
      simp [hyu.ne, hyB]
    have hxcard : (insert x (insert y (insert u (pairLiftBase x y v S)))).card =
        (insert y (insert u (pairLiftBase x y v S))).card + 1 := by
      apply Finset.card_insert_of_notMem
      simp [hxy.ne, hxu.ne, hxB]
    rw [hxcard, hycard, hucard, pairLiftBase_card]

/-- Vertices outside the four distinguished vertices of a diamond. -/
abbrev OutsideFour (x y u v : V) :=
  {z : V // z ≠ x ∧ z ≠ y ∧ z ≠ u ∧ z ≠ v}

/-- An outside vertex is unchanged by pair identification. -/
def outsideFourToIdentified
    (x y u v : V) : OutsideFour x y u v ↪ IdentifiedPair x y v where
  toFun z := ⟨⟨z.1, by simp [z.2.1, z.2.2.1]⟩, z.2.2.2.2⟩
  inj' := fun _ _ h => Subtype.ext (congrArg (fun q => q.1.1) h)

/-- Outside members of a finset, bundled with their non-membership proofs. -/
def outsideFourFinset (x y u v : V) (I : Finset V) :
    Finset (OutsideFour x y u v) :=
  I.subtype (fun z => z ≠ x ∧ z ≠ y ∧ z ≠ u ∧ z ≠ v)

/-- The quotient independent-set candidate used in the witness lift. -/
def pairCompressedSet
    (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v)
    (I : Finset V) : Finset (IdentifiedPair x y v) :=
  let O := (outsideFourFinset x y u v I).map
    (outsideFourToIdentified x y u v)
  if u ∈ I ∧ v ∈ I then insert (pairRepresentative hux huy huv) O else O

@[simp] theorem mem_outsideFourFinset {I : Finset V} {z : OutsideFour x y u v} :
    z ∈ outsideFourFinset x y u v I ↔ z.1 ∈ I := by
  simp [outsideFourFinset]

@[simp] theorem outsideFourFinset_card (I : Finset V) :
    (outsideFourFinset x y u v I).card =
      (I \ {x, y, u, v}).card := by
  classical
  simp only [outsideFourFinset, Finset.card_subtype]
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_insert,
    Finset.mem_singleton]
  tauto

theorem pairIdentify_eq_representative_iff
    (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v)
    (z : DeletedPair x y) :
    pairIdentify x y u v hux huy huv z = pairRepresentative hux huy huv ↔
      z.1 = u ∨ z.1 = v := by
  classical
  by_cases hzv : z.1 = v
  · simp [pairIdentify, pairRepresentative, hzv]
  · simp only [pairIdentify, dif_neg hzv, pairRepresentative]
    constructor
    · intro h
      left
      exact congrArg (fun q : IdentifiedPair x y v => q.1.1) h
    · rintro (hzu | hzu)
      · exact Subtype.ext (Subtype.ext hzu)
      · exact (hzv hzu).elim

theorem pairIdentify_eq_outside
    (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v)
    (z : DeletedPair x y) (a : OutsideFour x y u v)
    (h : pairIdentify x y u v hux huy huv z = outsideFourToIdentified x y u v a) :
    z.1 = a.1 := by
  classical
  by_cases hzv : z.1 = v
  · have hvu := congrArg (fun q : IdentifiedPair x y v => q.1.1) h
    simp [pairIdentify, hzv, outsideFourToIdentified] at hvu
    exact (a.2.2.2.1 hvu.symm).elim
  · have hza := congrArg (fun q : IdentifiedPair x y v => q.1.1) h
    simp [pairIdentify, hzv, outsideFourToIdentified] at hza
    exact hza

theorem outside_mem_S_of_mem_pairWitnessLift
    (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v)
    (S : Finset (IdentifiedPair x y v)) (a : OutsideFour x y u v)
    (ha : a.1 ∈ pairWitnessLift hux huy huv S) :
    outsideFourToIdentified x y u v a ∈ S := by
  classical
  by_cases hw : pairRepresentative hux huy huv ∈ S
  · simp only [pairWitnessLift, hw, if_pos] at ha
    have haB : a.1 ∈ pairLiftBase x y v S := by
      simpa [a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2] using ha
    obtain ⟨q, hqS, hq⟩ := mem_pairLiftBase.mp haB
    have hqa : q = outsideFourToIdentified x y u v a := by
      exact Subtype.ext (Subtype.ext hq)
    simpa [hqa] using hqS
  · simp only [pairWitnessLift, hw, if_neg] at ha
    have haB : a.1 ∈ pairLiftBase x y v S := by
      simpa [a.2.1, a.2.2.1, a.2.2.2.1] using ha
    obtain ⟨q, hqS, hq⟩ := mem_pairLiftBase.mp haB
    have hqa : q = outsideFourToIdentified x y u v a := by
      exact Subtype.ext (Subtype.ext hq)
    simpa [hqa] using hqS

theorem pairRepresentative_mem_of_both_mem_pairWitnessLift
    (hxy : G.Adj x y) (hxu : G.Adj x u) (hyu : G.Adj y u)
    (hxv : G.Adj x v) (hyv : G.Adj y v) (huv : u ≠ v)
    (S : Finset (IdentifiedPair x y v))
    (huI : u ∈ pairWitnessLift hxu.ne.symm hyu.ne.symm huv S)
    (hvI : v ∈ pairWitnessLift hxu.ne.symm hyu.ne.symm huv S) :
    pairRepresentative hxu.ne.symm hyu.ne.symm huv ∈ S := by
  classical
  by_contra hw
  have hvB : v ∉ pairLiftBase x y v S := by
    rintro hv
    obtain ⟨q, -, hq⟩ := mem_pairLiftBase.mp hv
    exact q.2 hq
  simp only [pairWitnessLift, hw, if_neg] at hvI
  simp [hxv.ne.symm, hyv.ne.symm, huv.symm, hvB] at hvI

theorem pairCompressedSet_subset
    (hxy : G.Adj x y) (hxu : G.Adj x u) (hyu : G.Adj y u)
    (hxv : G.Adj x v) (hyv : G.Adj y v) (huv : u ≠ v)
    (S : Finset (IdentifiedPair x y v)) (I : Finset V)
    (hIH : I ⊆ pairWitnessLift hxu.ne.symm hyu.ne.symm huv S) :
    pairCompressedSet hxu.ne.symm hyu.ne.symm huv I ⊆ S := by
  classical
  intro q hq
  by_cases hboth : u ∈ I ∧ v ∈ I
  · rw [pairCompressedSet, if_pos hboth] at hq
    simp only [Finset.mem_insert] at hq
    rcases hq with hqrep | hqout
    · subst q
      exact pairRepresentative_mem_of_both_mem_pairWitnessLift hxy hxu hyu hxv hyv huv S
        (hIH hboth.1) (hIH hboth.2)
    · rw [Finset.mem_map] at hqout
      obtain ⟨a, haI, rfl⟩ := hqout
      exact outside_mem_S_of_mem_pairWitnessLift hxu.ne.symm hyu.ne.symm huv S a
        (hIH (mem_outsideFourFinset.mp haI))
  · rw [pairCompressedSet, if_neg hboth] at hq
    rw [Finset.mem_map] at hq
    obtain ⟨a, haI, rfl⟩ := hq
    exact outside_mem_S_of_mem_pairWitnessLift hxu.ne.symm hyu.ne.symm huv S a
      (hIH (mem_outsideFourFinset.mp haI))

theorem source_mem_of_pairIdentify_mem_pairCompressedSet
    (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v)
    (I : Finset V) (z : DeletedPair x y)
    (hz : pairIdentify x y u v hux huy huv z ∈
      pairCompressedSet hux huy huv I) : z.1 ∈ I := by
  classical
  by_cases hboth : u ∈ I ∧ v ∈ I
  · rw [pairCompressedSet, if_pos hboth] at hz
    simp only [Finset.mem_insert] at hz
    rcases hz with hzrep | hzout
    · rcases (pairIdentify_eq_representative_iff hux huy huv z).mp hzrep with hzu | hzv
      · simpa [hzu] using hboth.1
      · simpa [hzv] using hboth.2
    · rw [Finset.mem_map] at hzout
      obtain ⟨a, haI, hza⟩ := hzout
      have hzval := pairIdentify_eq_outside hux huy huv z a hza.symm
      simpa [hzval] using (mem_outsideFourFinset.mp haI)
  · rw [pairCompressedSet, if_neg hboth] at hz
    rw [Finset.mem_map] at hz
    obtain ⟨a, haI, hza⟩ := hz
    have hzval := pairIdentify_eq_outside hux huy huv z a hza.symm
    simpa [hzval] using (mem_outsideFourFinset.mp haI)

theorem pairCompressedSet_indep
    (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v)
    (I : Finset V) (hI : G.IsIndepSet I) :
    (pairGraph (G := G) hux huy huv).IsIndepSet
      (pairCompressedSet hux huy huv I) := by
  classical
  intro a ha b hb hab hAdj
  rcases (SimpleGraph.map_adj' (pairIdentify x y u v hux huy huv)
      (G.induce ({x, y}ᶜ : Set V)) a b).mp hAdj with
    ⟨-, a', b', hab', ha', hb'⟩
  have haI : a'.1 ∈ I := source_mem_of_pairIdentify_mem_pairCompressedSet
    hux huy huv I a' (ha' ▸ ha)
  have hbI : b'.1 ∈ I := source_mem_of_pairIdentify_mem_pairCompressedSet
    hux huy huv I b' (hb' ▸ hb)
  exact hI haI hbI (Subtype.coe_ne_coe.mpr hab'.ne) hab'

theorem pairCompressedSet_card_bound
    (hxy : G.Adj x y) (hxu : G.Adj x u) (hyu : G.Adj y u)
    (hxv : G.Adj x v) (hyv : G.Adj y v) (huv : u ≠ v)
    (I : Finset V) (hI : G.IsIndepSet I) :
    I.card ≤ (pairCompressedSet hxu.ne.symm hyu.ne.symm huv I).card + 1 := by
  classical
  let P : Finset V := {x, y, u, v}
  have hsplit := Finset.card_sdiff_add_card_inter I P
  have hsplit' : (I \ P).card + (I ∩ P).card = I.card := by
    simpa [add_comm] using hsplit
  by_cases hboth : u ∈ I ∧ v ∈ I
  · have hxI : x ∉ I := by
      intro hxI
      exact hI hxI hboth.1 hxu.ne hxu
    have hyI : y ∉ I := by
      intro hyI
      exact hI hyI hboth.1 hyu.ne hyu
    have hinter : I ∩ P = {u, v} := by
      ext z
      simp only [P, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hzI, hz⟩
        rcases hz with rfl | rfl | rfl | rfl
        · exact (hxI hzI).elim
        · exact (hyI hzI).elim
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨hboth.1, Or.inr (Or.inr (Or.inl rfl))⟩
        · exact ⟨hboth.2, Or.inr (Or.inr (Or.inr rfl))⟩
    have hrep_not : pairRepresentative hxu.ne.symm hyu.ne.symm huv ∉
        (outsideFourFinset x y u v I).map (outsideFourToIdentified x y u v) := by
      intro h
      rw [Finset.mem_map] at h
      obtain ⟨a, -, ha⟩ := h
      have hau := congrArg (fun q : IdentifiedPair x y v => q.1.1) ha
      have haVal : (outsideFourToIdentified x y u v a).1.1 = a.1 := rfl
      have hrVal : (pairRepresentative hxu.ne.symm hyu.ne.symm huv).1.1 = u := rfl
      have hau' : a.1 = u := by
        rw [haVal, hrVal] at hau
        exact hau
      exact a.2.2.2.1 hau'
    have hcardC : (pairCompressedSet hxu.ne.symm hyu.ne.symm huv I).card =
        (I \ P).card + 1 := by
      rw [pairCompressedSet, if_pos hboth]
      rw [Finset.card_insert_of_notMem hrep_not, Finset.card_map, outsideFourFinset_card]
    rw [hinter] at hsplit'
    have hPcard : ({u, v} : Finset V).card = 2 := by simp [huv]
    rw [hPcard] at hsplit'
    rw [hcardC]
    omega
  · have hinter_le : (I ∩ P).card ≤ 1 := by
      rw [Finset.card_le_one_iff]
      intro r s hr hs
      obtain ⟨hrI, hrP⟩ := Finset.mem_inter.mp hr
      obtain ⟨hsI, hsP⟩ := Finset.mem_inter.mp hs
      simp only [P, Finset.mem_insert, Finset.mem_singleton] at hrP hsP
      rcases hrP with rfl | rfl | rfl | rfl <;>
        rcases hsP with rfl | rfl | rfl | rfl
      all_goals try rfl
      all_goals first
        | exact (hI hrI hsI hxy.ne hxy).elim
        | exact (hI hrI hsI hxy.ne.symm hxy.symm).elim
        | exact (hI hrI hsI hxu.ne hxu).elim
        | exact (hI hrI hsI hxu.ne.symm hxu.symm).elim
        | exact (hI hrI hsI hyu.ne hyu).elim
        | exact (hI hrI hsI hyu.ne.symm hyu.symm).elim
        | exact (hI hrI hsI hxv.ne hxv).elim
        | exact (hI hrI hsI hxv.ne.symm hxv.symm).elim
        | exact (hI hrI hsI hyv.ne hyv).elim
        | exact (hI hrI hsI hyv.ne.symm hyv.symm).elim
        | exact (hboth ⟨hrI, hsI⟩).elim
        | exact (hboth ⟨hsI, hrI⟩).elim
    have hcardC : (pairCompressedSet hxu.ne.symm hyu.ne.symm huv I).card =
        (I \ P).card := by
      rw [pairCompressedSet, if_neg hboth, Finset.card_map, outsideFourFinset_card]
    rw [hcardC]
    omega

/-- Every independent set in the lifted witness compresses to an independent
set of the quotient while losing at most one vertex. -/
theorem alphaOn_pairWitnessLift_le
    (hxy : G.Adj x y) (hxu : G.Adj x u) (hyu : G.Adj y u)
    (hxv : G.Adj x v) (hyv : G.Adj y v) (huv : u ≠ v)
    (S : Finset (IdentifiedPair x y v)) :
    alphaOn G (pairWitnessLift hxu.ne.symm hyu.ne.symm huv S) ≤
      alphaOn (pairGraph (G := G) hxu.ne.symm hyu.ne.symm huv) S + 1 := by
  classical
  obtain ⟨I, hIH, hI, hIcard⟩ :=
    exists_maximum_independent_subset G
      (pairWitnessLift hxu.ne.symm hyu.ne.symm huv S)
  let J := pairCompressedSet hxu.ne.symm hyu.ne.symm huv I
  have hJS : J ⊆ S := pairCompressedSet_subset hxy hxu hyu hxv hyv huv S I hIH
  have hJind : (pairGraph (G := G) hxu.ne.symm hyu.ne.symm huv).IsIndepSet J :=
    pairCompressedSet_indep hxu.ne.symm hyu.ne.symm huv I hI
  have hJalpha : J.card ≤
      alphaOn (pairGraph (G := G) hxu.ne.symm hyu.ne.symm huv) S :=
    card_le_alphaOn hJS hJind
  have hcard := pairCompressedSet_card_bound hxy hxu hyu hxv hyv huv I hI
  rw [← hIcard]
  exact hcard.trans (Nat.add_le_add_right hJalpha 1)

/-- Each quotient witness gains at least one unit of signed potential when
lifted back to the four diamond vertices. -/
theorem pairGraph_potential_add_one_le
    (hxy : G.Adj x y) (hxu : G.Adj x u) (hyu : G.Adj y u)
    (hxv : G.Adj x v) (hyv : G.Adj y v) (huv : u ≠ v)
    (S : Finset (IdentifiedPair x y v)) :
    potential (pairGraph (G := G) hxu.ne.symm hyu.ne.symm huv) S + 1 ≤
      potential G (pairWitnessLift hxu.ne.symm hyu.ne.symm huv S) := by
  have hcard := pairWitnessLift_card hxy hxu hyu hxv hyv huv S
  have halpha := alphaOn_pairWitnessLift_le hxy hxu hyu hxv hyv huv S
  rw [potential, potential, hcard]
  omega

/-- C1.1's potential estimate: identifying the two nonadjacent common
neighbors after deleting the edge endpoints lowers `f` by at least one. -/
theorem pairGraph_f_le_sub_one
    (hxy : G.Adj x y) (hxu : G.Adj x u) (hyu : G.Adj y u)
    (hxv : G.Adj x v) (hyv : G.Adj y v) (huv : u ≠ v) :
    f (pairGraph (G := G) hxu.ne.symm hyu.ne.symm huv) ≤ f G - 1 := by
  rw [f_le_iff_forall_potential_le]
  intro S
  have hlift := pairGraph_potential_add_one_le hxy hxu hyu hxv hyv huv S
  have hmax := potential_le_f G (pairWitnessLift hxu.ne.symm hyu.ne.symm huv S)
  omega

/-- The pair quotient is strictly smaller than the original graph. -/
theorem pairGraph_card_lt
    (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v) :
    Fintype.card (IdentifiedPair x y v) < Fintype.card V := by
  apply Fintype.card_lt_of_injective_not_surjective
    (identifiedPairEmbedding x y v) (identifiedPairEmbedding x y v).injective
  intro hsurj
  obtain ⟨q, hq⟩ := hsurj x
  have hval : identifiedPairEmbedding x y v q = q.1.1 := rfl
  rw [hval] at hq
  exact q.1.2 (Or.inl hq)

/-- Embed the apex construction into `V`, sending the apex to `x`. -/
def apexIntoOriginal (x y : V) : Option (DeletedPair x y) ↪ V where
  toFun z := match z with
    | none => x
    | some w => w.1
  inj' := by
    intro a b h
    cases a with
    | none =>
        cases b with
        | none => rfl
        | some b => exact (b.2 (Or.inl (by simpa using h.symm))).elim
    | some a =>
        cases b with
        | none => exact (a.2 (Or.inl (by simpa using h))).elim
        | some b => exact congrArg some (Subtype.ext h)

/-- The apex construction is strictly smaller, since `y` is not in the
image of `apexIntoOriginal`. -/
theorem commonNeighborApexGraph_card_lt (hxy : G.Adj x y) :
    Fintype.card (Option (DeletedPair x y)) < Fintype.card V := by
  apply Fintype.card_lt_of_injective_not_surjective
    (apexIntoOriginal x y) (apexIntoOriginal x y).injective
  intro hsurj
  obtain ⟨z, hz⟩ := hsurj y
  cases z with
  | none => exact hxy.ne hz
  | some z =>
      have hval : apexIntoOriginal x y (some z) = z.1 := rfl
      rw [hval] at hz
      exact z.2 (Or.inr hz)

/-- A coloring by an arbitrary finite type is equivalent to colorability by
the cardinality of that type. -/
theorem nonempty_coloring_iff_colorable_card {W : Type u} (H : SimpleGraph W)
    {α : Type v} [Fintype α] :
    Nonempty (H.Coloring α) ↔ H.Colorable (Fintype.card α) := by
  constructor
  · rintro ⟨C⟩
    exact ⟨SimpleGraph.recolorOfEquiv H (Fintype.equivFin α) C⟩
  · rintro ⟨C⟩
    exact ⟨SimpleGraph.recolorOfEquiv H (Fintype.equivFin α).symm C⟩

/-- C1.1 in the form used by C1.2: the pair quotient has an
`(chiNat G - 2)`-coloring. -/
theorem pairGraph_colorable_chi_sub_two
    (hmin : Erdos922FullB.IsOrderMinimalCounterexample G)
    (hxy : G.Adj x y) (hxu : G.Adj x u) (hyu : G.Adj y u)
    (hxv : G.Adj x v) (hyv : G.Adj y v) (huv : u ≠ v) :
    (pairGraph (G := G) hxu.ne.symm hyu.ne.symm huv).Colorable
      (Erdos922FullB.chiNat G - 2) := by
  let Q := pairGraph (G := G) hxu.ne.symm hyu.ne.symm huv
  have hsmall := hmin.smaller Q
    (pairGraph_card_lt hxu.ne.symm hyu.ne.symm huv)
  change Q.Colorable (Int.toNat (f Q) + 2) at hsmall
  have hfQ := pairGraph_f_le_sub_one hxy hxu hyu hxv hyv huv
  have hgap := Erdos922FullB.counterexample_gap_int G hmin.counterexample
  change f G + 2 < (Erdos922FullB.chiNat G : ℤ) at hgap
  have hfQ0 := f_nonneg Q
  have hfG0 := f_nonneg G
  change f Q ≤ f G - 1 at hfQ
  change 0 ≤ f Q at hfQ0
  have hfQcast : (Int.toNat (f Q) : ℤ) = f Q := Int.toNat_of_nonneg hfQ0
  have hchi := Erdos922FullB.three_le_chiNat_of_not_folkmanBound G hmin.counterexample
  apply hsmall.mono
  omega

/-- A minimal counterexample has no coloring using one fewer color than its
chromatic number, with `Option` supplying the fresh color. -/
theorem not_coloring_option_chi_sub_two
    (hmin : Erdos922FullB.IsOrderMinimalCounterexample G) :
    ¬ Nonempty (G.Coloring (Option (Fin (Erdos922FullB.chiNat G - 2)))) := by
  intro hC
  have hc := (nonempty_coloring_iff_colorable_card G).mp hC
  have hchi := Erdos922FullB.three_le_chiNat_of_not_folkmanBound G hmin.counterexample
  have hcard : Fintype.card (Option (Fin (Erdos922FullB.chiNat G - 2))) =
      Erdos922FullB.chiNat G - 1 := by
    simp
    omega
  rw [hcard] at hc
  have hle := (Erdos922FullB.colorable_iff_chiNat_le G _).mp hc
  omega

/-- C1.2 plus the identified pair show that an edge has strictly more common
neighbors than the quotient palette. -/
theorem chi_sub_two_lt_commonNeighbors
    (hmin : Erdos922FullB.IsOrderMinimalCounterexample G)
    (hxy : G.Adj x y) (hxu : G.Adj x u) (hyu : G.Adj y u)
    (hxv : G.Adj x v) (hyv : G.Adj y v) (huv : u ≠ v)
    (huvNA : ¬ G.Adj u v) :
    Erdos922FullB.chiNat G - 2 < Nat.card (CommonNeighbor G x y) := by
  classical
  let α := Fin (Erdos922FullB.chiNat G - 2)
  let Q := pairGraph (G := G) hxu.ne.symm hyu.ne.symm huv
  let C : Q.Coloring α := Classical.choice
    (pairGraph_colorable_chi_sub_two hmin hxy hxu hyu hxv hyv huv)
  let color : CommonNeighbor G x y → α := fun z =>
    C (pairIdentify x y u v hxu.ne.symm hyu.ne.symm huv z.toDeletedPair)
  have hchi := Erdos922FullB.three_le_chiNat_of_not_folkmanBound G hmin.counterexample
  have hsurj : Function.Surjective color := by
    intro i
    obtain ⟨z, hzx, hzy, hzi⟩ := everyColorOccursOnIdentifiedCommonNeighbors
      hxy hxu.ne.symm hyu.ne.symm huv huvNA
      (not_coloring_option_chi_sub_two hmin) C i
    refine ⟨⟨z, hzx, hzy⟩, ?_⟩
    have hzx' : z ≠ x := hzx.ne.symm
    have hzy' : z ≠ y := hzy.ne.symm
    have hzOld : z ∈ ({x, y}ᶜ : Set V) := by simp [hzx', hzy']
    simp only [pairGraphPullFunction, hzOld, dif_pos] at hzi
    change C (pairIdentify x y u v hxu.ne.symm hyu.ne.symm huv
      ⟨z, hzOld⟩) = i at hzi
    simpa [color, CommonNeighbor.toDeletedPair, hzx', hzy'] using hzi
  let cu : CommonNeighbor G x y := ⟨u, hxu, hyu⟩
  let cv : CommonNeighbor G x y := ⟨v, hxv, hyv⟩
  have hcucv : color cu = color cv := by
    dsimp only [color, cu, cv, CommonNeighbor.toDeletedPair]
    simp [pairIdentify, huv]
  have hnotinj : ¬ Function.Injective color := by
    intro hinj
    have := hinj hcucv
    exact huv (congrArg Subtype.val this)
  letI : Fintype (CommonNeighbor G x y) := Fintype.ofFinite _
  have hlt := Fintype.card_lt_of_surjective_not_injective color hsurj hnotinj
  simpa [α, Nat.card_eq_fintype_card] using hlt

/-- The common-neighbor apex graph cannot use `chiNat G - 2` colors. -/
theorem apex_not_colorable_chi_sub_two
    (hmin : Erdos922FullB.IsOrderMinimalCounterexample G)
    (hxy : G.Adj x y) (hxu : G.Adj x u) (hyu : G.Adj y u)
    (hxv : G.Adj x v) (hyv : G.Adj y v) (huv : u ≠ v)
    (huvNA : ¬ G.Adj u v) :
    ¬ (commonNeighborApexGraph (G := G) (x := x) (y := y)).Colorable
      (Erdos922FullB.chiNat G - 2) := by
  intro hc
  apply commonNeighborApexGraph_not_colorable hxy
    (not_coloring_option_chi_sub_two hmin)
    (by simpa using
      chi_sub_two_lt_commonNeighbors hmin hxy hxu hyu hxv hyv huv huvNA)
  apply (nonempty_coloring_iff_colorable_card _).mpr
  simpa using hc

/-- Minimality and apex noncolorability force the apex graph's potential
maximum to be at least that of `G`. -/
theorem f_le_f_apex
    (hmin : Erdos922FullB.IsOrderMinimalCounterexample G)
    (hxy : G.Adj x y) (hxu : G.Adj x u) (hyu : G.Adj y u)
    (hxv : G.Adj x v) (hyv : G.Adj y v) (huv : u ≠ v)
    (huvNA : ¬ G.Adj u v) :
    f G ≤ f (commonNeighborApexGraph (G := G) (x := x) (y := y)) := by
  let G0 := commonNeighborApexGraph (G := G) (x := x) (y := y)
  have hsmall := hmin.smaller G0 (commonNeighborApexGraph_card_lt hxy)
  change G0.Colorable (Int.toNat (f G0) + 2) at hsmall
  have hncol := apex_not_colorable_chi_sub_two hmin hxy hxu hyu hxv hyv huv huvNA
  have hpalette : Erdos922FullB.chiNat G - 2 < Int.toNat (f G0) + 2 := by
    by_contra h
    exact hncol (hsmall.mono (by omega))
  have hgap := Erdos922FullB.counterexample_gap_int G hmin.counterexample
  change f G + 2 < (Erdos922FullB.chiNat G : ℤ) at hgap
  have hf0 := f_nonneg G0
  have hfG := f_nonneg G
  have hf0cast : (Int.toNat (f G0) : ℤ) = f G0 := Int.toNat_of_nonneg hf0
  have hfGcast : (Int.toNat (f G) : ℤ) = f G := Int.toNat_of_nonneg hfG
  have hchi := Erdos922FullB.three_le_chiNat_of_not_folkmanBound G hmin.counterexample
  have hfGle : f G ≤ (Erdos922FullB.chiNat G : ℤ) - 3 := by omega
  have hf0ge : (Erdos922FullB.chiNat G : ℤ) - 3 ≤ f G0 := by omega
  exact hfGle.trans hf0ge

/-- Non-apex vertices, carrying the proof needed to eliminate the `none`
case. -/
abbrev NonApex (x y : V) := {z : Option (DeletedPair x y) // z ≠ none}

/-- Forget `some` and embed a non-apex vertex into `V`. -/
def nonApexIntoOriginal (x y : V) : NonApex x y ↪ V where
  toFun z := match h : z.1 with
    | none => (z.2 h).elim
    | some w => w.1
  inj' := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    cases a with
    | none => exact (ha rfl).elim
    | some a' =>
        cases b with
        | none => exact (hb rfl).elim
        | some b' =>
            apply Subtype.ext
            apply congrArg some
            apply Subtype.ext
            exact hab

/-- Old vertices represented by a finset of the apex graph. -/
def apexOldPart (x y : V) (S : Finset (Option (DeletedPair x y))) : Finset V :=
  (S.subtype (fun z => z ≠ none)).map (nonApexIntoOriginal x y)

@[simp] theorem mem_apexOldPart {S : Finset (Option (DeletedPair x y))} {z : V} :
    z ∈ apexOldPart x y S ↔
      ∃ d : DeletedPair x y, some d ∈ S ∧ d.1 = z := by
  classical
  constructor
  · intro hz
    rw [apexOldPart, Finset.mem_map] at hz
    obtain ⟨q, hq, hqz⟩ := hz
    have hqS : q.1 ∈ S := by simpa using hq
    cases heq : q.1 with
    | none => exact (q.2 heq).elim
    | some d =>
        have qeq : q = (⟨some d, by simp⟩ : NonApex x y) := Subtype.ext heq
        subst q
        have hd : d.1 = z := by
          change d.1 = z at hqz
          exact hqz
        exact ⟨d, by simpa [heq] using hqS, hd⟩
  · rintro ⟨d, hdS, rfl⟩
    rw [apexOldPart, Finset.mem_map]
    let q : NonApex x y := ⟨some d, by simp⟩
    refine ⟨q, ?_, ?_⟩
    · simpa [q] using hdS
    · rfl

theorem apexOldPart_card_add_one_of_mem
    (S : Finset (Option (DeletedPair x y))) (h : none ∈ S) :
    (apexOldPart x y S).card + 1 = S.card := by
  classical
  rw [apexOldPart, Finset.card_map, Finset.card_subtype]
  have herase := Finset.card_erase_add_one h
  have hfilter : S.filter (fun z => z ≠ none) = S.erase none := by
    ext z
    simp [and_comm]
  simpa [hfilter] using herase

theorem apexOldPart_card_of_not_mem
    (S : Finset (Option (DeletedPair x y))) (h : none ∉ S) :
    (apexOldPart x y S).card = S.card := by
  classical
  rw [apexOldPart, Finset.card_map, Finset.card_subtype]
  have hfilter : S.filter (fun z => z ≠ none) = S := by
    apply Finset.filter_eq_self.mpr
    intro z hz
    rintro rfl
    exact h hz
  rw [hfilter]

/-- Old vertices away from `x,y`, bundled for insertion into the apex graph. -/
abbrev AwayPair (x y : V) := {z : V // z ≠ x ∧ z ≠ y}

def awayPairToApex (x y : V) : AwayPair x y ↪ Option (DeletedPair x y) where
  toFun z := some ⟨z.1, by simp [z.2.1, z.2.2]⟩
  inj' := by
    intro a b h
    change some (⟨a.1, _⟩ : DeletedPair x y) =
      some (⟨b.1, _⟩ : DeletedPair x y) at h
    injection h with hd
    exact Subtype.ext (congrArg (fun d : DeletedPair x y => d.1) hd)

def awayPairFinset (x y : V) (I : Finset V) : Finset (AwayPair x y) :=
  I.subtype (fun z => z ≠ x ∧ z ≠ y)

def apexCompression (x y : V) (I : Finset V) :
    Finset (Option (DeletedPair x y)) :=
  let O := (awayPairFinset x y I).map (awayPairToApex x y)
  if x ∈ I ∨ y ∈ I then insert none O else O

@[simp] theorem mem_awayPairFinset {I : Finset V} {z : AwayPair x y} :
    z ∈ awayPairFinset x y I ↔ z.1 ∈ I := by
  simp [awayPairFinset]

theorem apexCompression_card
    (hxy : G.Adj x y) (I : Finset V) (hI : G.IsIndepSet I) :
    (apexCompression x y I).card = I.card := by
  classical
  let P : Finset V := {x, y}
  have hsplit := Finset.card_sdiff_add_card_inter I P
  have hawayCard : (awayPairFinset x y I).card = (I \ P).card := by
    simp only [awayPairFinset, Finset.card_subtype]
    congr 1
    ext z
    simp only [Finset.mem_filter, Finset.mem_sdiff, P, Finset.mem_insert,
      Finset.mem_singleton]
    tauto
  have hnone : none ∉ (awayPairFinset x y I).map (awayPairToApex x y) := by
    intro h
    rw [Finset.mem_map] at h
    obtain ⟨a, -, ha⟩ := h
    change some (⟨a.1, _⟩ : DeletedPair x y) = none at ha
    exact Option.some_ne_none _ ha
  by_cases hspecial : x ∈ I ∨ y ∈ I
  · have hinter : (I ∩ P).card = 1 := by
      have hnotboth : ¬ (x ∈ I ∧ y ∈ I) := by
        rintro ⟨hx, hy⟩
        exact hI hx hy hxy.ne hxy
      rcases hspecial with hx | hy
      · have hy : y ∉ I := fun hy => hnotboth ⟨hx, hy⟩
        have : I ∩ P = {x} := by ext z; simp [P, hx, hy]
        simp [this]
      · have hx : x ∉ I := fun hx => hnotboth ⟨hx, hy⟩
        have : I ∩ P = {y} := by ext z; simp [P, hx, hy]
        simp [this]
    rw [apexCompression, if_pos (by assumption), Finset.card_insert_of_notMem hnone,
      Finset.card_map, hawayCard]
    omega
  · have hx : x ∉ I := fun hx => hspecial (Or.inl hx)
    have hy : y ∉ I := fun hy => hspecial (Or.inr hy)
    have hinter : (I ∩ P).card = 0 := by
      have : I ∩ P = ∅ := by ext z; simp [P, hx, hy]
      simp [this]
    rw [apexCompression, if_neg hspecial, Finset.card_map, hawayCard]
    omega

@[simp] theorem none_mem_apexCompression (I : Finset V) :
    none ∈ apexCompression x y I ↔ x ∈ I ∨ y ∈ I := by
  classical
  have hnone : none ∉ (awayPairFinset x y I).map (awayPairToApex x y) := by
    intro hm
    rw [Finset.mem_map] at hm
    obtain ⟨a, -, ha⟩ := hm
    change some (⟨a.1, _⟩ : DeletedPair x y) = none at ha
    exact Option.some_ne_none _ ha
  by_cases h : x ∈ I ∨ y ∈ I
  · simp [apexCompression, h, hnone]
  · simp [apexCompression, h, hnone]

@[simp] theorem some_mem_apexCompression (I : Finset V) (d : DeletedPair x y) :
    some d ∈ apexCompression x y I ↔ d.1 ∈ I := by
  classical
  by_cases h : x ∈ I ∨ y ∈ I
  · rw [apexCompression, if_pos h]
    simp only [Finset.mem_insert, Option.some_ne_none, false_or, Finset.mem_map]
    constructor
    · rintro ⟨a, ha, had⟩
      have hav : a.1 = d.1 := by
        change some (⟨a.1, _⟩ : DeletedPair x y) = some d at had
        exact congrArg Subtype.val (Option.some.inj had)
      simpa [hav] using (mem_awayPairFinset.mp ha)
    · intro hdI
      let a : AwayPair x y := ⟨d.1, by
        simpa only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
          not_or] using d.2⟩
      exact ⟨a, mem_awayPairFinset.mpr hdI, by rfl⟩
  · rw [apexCompression, if_neg h, Finset.mem_map]
    constructor
    · rintro ⟨a, ha, had⟩
      have hav : a.1 = d.1 := by
        change some (⟨a.1, _⟩ : DeletedPair x y) = some d at had
        exact congrArg Subtype.val (Option.some.inj had)
      simpa [hav] using (mem_awayPairFinset.mp ha)
    · intro hdI
      let a : AwayPair x y := ⟨d.1, by
        simpa only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
          not_or] using d.2⟩
      exact ⟨a, mem_awayPairFinset.mpr hdI, by rfl⟩

theorem apexCompression_subset
    (S : Finset (Option (DeletedPair x y))) (I : Finset V)
    (hIH : I ⊆ insert x (insert y (apexOldPart x y S)))
    (hapex : x ∈ I ∨ y ∈ I → none ∈ S) :
    apexCompression x y I ⊆ S := by
  classical
  intro q hq
  cases q with
  | none => exact hapex ((none_mem_apexCompression I).mp hq)
  | some d =>
      have hdI : d.1 ∈ I := (some_mem_apexCompression I d).mp hq
      have hdH := hIH hdI
      have hdx : d.1 ≠ x := by
        intro h
        exact d.2 (Or.inl h)
      have hdy : d.1 ≠ y := by
        intro h
        exact d.2 (Or.inr h)
      have hdOld : d.1 ∈ apexOldPart x y S := by
        simpa [hdx, hdy] using hdH
      obtain ⟨e, heS, heq⟩ := mem_apexOldPart.mp hdOld
      have hed : e = d := Subtype.ext heq
      simpa [hed] using heS

theorem apexCompression_indep
    (hxy : G.Adj x y) (I : Finset V) (hI : G.IsIndepSet I) :
    (commonNeighborApexGraph (G := G) (x := x) (y := y)).IsIndepSet
      (apexCompression x y I) := by
  classical
  intro a ha b hb hab hAdj
  cases a with
  | none =>
      cases b with
      | none => exact hAdj
      | some b =>
          have hspecial := (none_mem_apexCompression I).mp ha
          have hbI := (some_mem_apexCompression I b).mp hb
          rcases hspecial with hxI | hyI
          · exact hI hxI hbI (fun h => b.2 (Or.inl h.symm)) hAdj.1
          · exact hI hyI hbI (fun h => b.2 (Or.inr h.symm)) hAdj.2
  | some a =>
      cases b with
      | none =>
          have haI := (some_mem_apexCompression I a).mp ha
          have hspecial := (none_mem_apexCompression I).mp hb
          rcases hspecial with hxI | hyI
          · exact hI haI hxI (fun h => a.2 (Or.inl h)) hAdj.1.symm
          · exact hI haI hyI (fun h => a.2 (Or.inr h)) hAdj.2.symm
      | some b =>
          have haI := (some_mem_apexCompression I a).mp ha
          have hbI := (some_mem_apexCompression I b).mp hb
          exact hI haI hbI (fun h => hab (congrArg some (Subtype.ext h))) hAdj

/-- Replacing a present apex by the adjacent pair `x,y` does not increase
the independence number. -/
theorem alphaOn_apexReplacement_le
    (hxy : G.Adj x y) (S : Finset (Option (DeletedPair x y)))
    (hapex : none ∈ S) :
    alphaOn G (insert x (insert y (apexOldPart x y S))) ≤
      alphaOn (commonNeighborApexGraph (G := G) (x := x) (y := y)) S := by
  classical
  obtain ⟨I, hIH, hI, hIcard⟩ := exists_maximum_independent_subset G
    (insert x (insert y (apexOldPart x y S)))
  let K := apexCompression x y I
  have hKS : K ⊆ S := apexCompression_subset S I hIH (fun _ => hapex)
  have hKind : (commonNeighborApexGraph (G := G) (x := x) (y := y)).IsIndepSet K :=
    apexCompression_indep hxy I hI
  have hKalpha := card_le_alphaOn hKS hKind
  rw [← hIcard, ← apexCompression_card hxy I hI]
  exact hKalpha

/-- A maximizing apex witness cannot contain the apex once `f G ≤ f G0`. -/
theorem apex_not_mem_maximumWitness
    (hxy : G.Adj x y) (S : Finset (Option (DeletedPair x y)))
    (hSf : potential (commonNeighborApexGraph (G := G) (x := x) (y := y)) S =
      f (commonNeighborApexGraph (G := G) (x := x) (y := y)))
    (hf : f G ≤ f (commonNeighborApexGraph (G := G) (x := x) (y := y))) :
    none ∉ S := by
  intro hapex
  let H := insert x (insert y (apexOldPart x y S))
  have hxOld : x ∉ apexOldPart x y S := by
    rintro hx
    obtain ⟨d, -, hd⟩ := mem_apexOldPart.mp hx
    exact d.2 (Or.inl hd)
  have hyOld : y ∉ apexOldPart x y S := by
    rintro hy
    obtain ⟨d, -, hd⟩ := mem_apexOldPart.mp hy
    exact d.2 (Or.inr hd)
  have hHcard : H.card = S.card + 1 := by
    have hold := apexOldPart_card_add_one_of_mem S hapex
    simp only [H]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem]
    · omega
    · exact hyOld
    · simp [hxy.ne, hxOld]
  have halpha := alphaOn_apexReplacement_le hxy S hapex
  have hpot := potential_le_f G H
  simp only [Erdos922.potential] at hpot
  rw [hHcard] at hpot
  rw [Erdos922.potential] at hSf
  change alphaOn G H ≤ alphaOn
    (commonNeighborApexGraph (G := G) (x := x) (y := y)) S at halpha
  omega

theorem apexOldPart_mono {S T : Finset (Option (DeletedPair x y))}
    (hST : S ⊆ T) : apexOldPart x y S ⊆ apexOldPart x y T := by
  intro z hz
  obtain ⟨d, hdS, rfl⟩ := mem_apexOldPart.mp hz
  exact mem_apexOldPart.mpr ⟨d, hST hdS, rfl⟩

theorem apexOldPart_indep
    (S : Finset (Option (DeletedPair x y)))
    (hS : (commonNeighborApexGraph (G := G) (x := x) (y := y)).IsIndepSet S) :
    G.IsIndepSet (apexOldPart x y S) := by
  intro a ha b hb hab hAdj
  obtain ⟨da, hda, rfl⟩ := mem_apexOldPart.mp ha
  obtain ⟨db, hdb, rfl⟩ := mem_apexOldPart.mp hb
  exact hS hda hdb (fun h => hab (congrArg Subtype.val (Option.some.inj h))) hAdj

/-- When the apex is absent, the witness and its old-vertex image have equal
independence number. -/
theorem alphaOn_apex_eq_old_of_not_mem
    (hxy : G.Adj x y) (S : Finset (Option (DeletedPair x y)))
    (hno : none ∉ S) :
    alphaOn (commonNeighborApexGraph (G := G) (x := x) (y := y)) S =
      alphaOn G (apexOldPart x y S) := by
  classical
  apply Nat.le_antisymm
  · obtain ⟨K, hKS, hK, hKcard⟩ := exists_maximum_independent_subset
      (commonNeighborApexGraph (G := G) (x := x) (y := y)) S
    have hnoneK : none ∉ K := fun h => hno (hKS h)
    rw [← hKcard, ← apexOldPart_card_of_not_mem K hnoneK]
    exact card_le_alphaOn (apexOldPart_mono hKS) (apexOldPart_indep K hK)
  · obtain ⟨I, hIJ, hI, hIcard⟩ := exists_maximum_independent_subset G
      (apexOldPart x y S)
    have hxJ : x ∉ apexOldPart x y S := by
      rintro hx
      obtain ⟨d, -, hd⟩ := mem_apexOldPart.mp hx
      exact d.2 (Or.inl hd)
    have hyJ : y ∉ apexOldPart x y S := by
      rintro hy
      obtain ⟨d, -, hd⟩ := mem_apexOldPart.mp hy
      exact d.2 (Or.inr hd)
    have hxI : x ∉ I := fun hx => hxJ (hIJ hx)
    have hyI : y ∉ I := fun hy => hyJ (hIJ hy)
    have hsubH : I ⊆ insert x (insert y (apexOldPart x y S)) := by
      intro z hz
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hIJ hz))
    let K := apexCompression x y I
    have hKS : K ⊆ S := apexCompression_subset S I hsubH (by
      rintro (hx | hy)
      · exact (hxI hx).elim
      · exact (hyI hy).elim)
    have hK : (commonNeighborApexGraph (G := G) (x := x) (y := y)).IsIndepSet K :=
      apexCompression_indep hxy I hI
    rw [← hIcard, ← apexCompression_card hxy I hI]
    exact card_le_alphaOn hKS hK

theorem potential_apex_eq_old_of_not_mem
    (hxy : G.Adj x y) (S : Finset (Option (DeletedPair x y)))
    (hno : none ∉ S) :
    potential (commonNeighborApexGraph (G := G) (x := x) (y := y)) S =
      potential G (apexOldPart x y S) := by
  rw [potential, potential, apexOldPart_card_of_not_mem S hno,
    alphaOn_apex_eq_old_of_not_mem hxy S hno]

theorem triangleExtension_card
    (hxy : G.Adj x y) (hxt : G.Adj x u) (hyt : G.Adj y u)
    (J : Finset V) (hxJ : x ∉ J) (hyJ : y ∉ J) (htJ : u ∉ J) :
    (insert x (insert y (insert u J))).card = J.card + 3 := by
  have htcard : (insert u J).card = J.card + 1 := Finset.card_insert_of_notMem htJ
  have hycard : (insert y (insert u J)).card = (insert u J).card + 1 := by
    apply Finset.card_insert_of_notMem
    simp [hyt.ne, hyJ]
  have hxcard : (insert x (insert y (insert u J))).card =
      (insert y (insert u J)).card + 1 := by
    apply Finset.card_insert_of_notMem
    simp [hxy.ne, hxt.ne, hxJ]
  omega

theorem alphaOn_triangleExtension_le
    (hxy : G.Adj x y) (hxt : G.Adj x u) (hyt : G.Adj y u)
    (J : Finset V) :
    alphaOn G (insert x (insert y (insert u J))) ≤ alphaOn G J + 1 := by
  classical
  obtain ⟨I, hIH, hI, hIcard⟩ := exists_maximum_independent_subset G
    (insert x (insert y (insert u J)))
  let P : Finset V := {x, y, u}
  let O := I \ P
  have hOJ : O ⊆ J := by
    intro z hz
    have hzI := (Finset.mem_sdiff.mp hz).1
    have hzP := (Finset.mem_sdiff.mp hz).2
    have hzH := hIH hzI
    simp only [Finset.mem_insert] at hzH
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hzP
    rcases hzH with rfl | rfl | rfl | hz
    · exact (hzP (Or.inl rfl)).elim
    · exact (hzP (Or.inr (Or.inl rfl))).elim
    · exact (hzP (Or.inr (Or.inr rfl))).elim
    · exact hz
  have hOind : G.IsIndepSet O := hI.mono (by simp [O])
  have hOalpha : O.card ≤ alphaOn G J := card_le_alphaOn hOJ hOind
  have hinter : (I ∩ P).card ≤ 1 := by
    rw [Finset.card_le_one_iff]
    intro a b ha hb
    obtain ⟨haI, haP⟩ := Finset.mem_inter.mp ha
    obtain ⟨hbI, hbP⟩ := Finset.mem_inter.mp hb
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at haP hbP
    rcases haP with rfl | rfl | rfl <;> rcases hbP with rfl | rfl | rfl
    all_goals try rfl
    all_goals first
      | exact (hI haI hbI hxy.ne hxy).elim
      | exact (hI haI hbI hxy.ne.symm hxy.symm).elim
      | exact (hI haI hbI hxt.ne hxt).elim
      | exact (hI haI hbI hxt.ne.symm hxt.symm).elim
      | exact (hI haI hbI hyt.ne hyt).elim
      | exact (hI haI hbI hyt.ne.symm hyt.symm).elim
  have hsplit := Finset.card_sdiff_add_card_inter I P
  change O.card + (I ∩ P).card = I.card at hsplit
  rw [← hIcard]
  omega

/-- The no-induced-diamond conclusion for a genuine order-minimal
counterexample: common neighbors of every edge form a clique. -/
theorem commonNeighbors_isClique_of_orderMinimalCounterexample
    (hmin : Erdos922FullB.IsOrderMinimalCounterexample G)
    (x y : V) (hxy : G.Adj x y) :
    G.IsClique {z | G.Adj x z ∧ G.Adj y z} := by
  classical
  intro u hu v hv huv
  by_contra huvNA
  have hxu : G.Adj x u := hu.1
  have hyu : G.Adj y u := hu.2
  have hxv : G.Adj x v := hv.1
  have hyv : G.Adj y v := hv.2
  let G0 := commonNeighborApexGraph (G := G) (x := x) (y := y)
  have hfLower : f G ≤ f G0 :=
    f_le_f_apex hmin hxy hxu hyu hxv hyv huv huvNA
  obtain ⟨S, hSf⟩ := exists_maximum_potential G0
  have hno : none ∉ S := apex_not_mem_maximumWitness hxy S hSf hfLower
  let J := apexOldPart x y S
  have hpotTransport := potential_apex_eq_old_of_not_mem hxy S hno
  change potential G0 S = potential G J at hpotTransport
  have hJle := potential_le_f G J
  have hfEq : f G0 = f G := by
    have heq : f G0 = potential G J := hSf.symm.trans hpotTransport
    omega
  have hJmax : potential G J = f G := by
    rw [← hpotTransport, hSf, hfEq]
  have halphaSJ : alphaOn G0 S = alphaOn G J := by
    exact alphaOn_apex_eq_old_of_not_mem hxy S hno
  have hxJ : x ∉ J := by
    rintro hx
    obtain ⟨d, -, hd⟩ := mem_apexOldPart.mp hx
    exact d.2 (Or.inl hd)
  have hyJ : y ∉ J := by
    rintro hy
    obtain ⟨d, -, hd⟩ := mem_apexOldPart.mp hy
    exact d.2 (Or.inr hd)

  -- Adding the apex to a maximizing old witness forces an independent set
  -- one vertex larger, whose old part avoids every common neighbor.
  let K : Finset (Option (DeletedPair x y)) := insert none S
  have hKcard : K.card = S.card + 1 := Finset.card_insert_of_notMem hno
  have hKpot := potential_le_f G0 K
  rw [← hSf] at hKpot
  have halphaK : alphaOn G0 S + 1 ≤ alphaOn G0 K := by
    simp only [potential, hKcard] at hKpot
    omega
  obtain ⟨L, hLK, hLind, hLcard⟩ := exists_maximum_independent_subset G0 K
  have hnoneL : none ∈ L := by
    by_contra hn
    have hLS : L ⊆ S := by
      intro z hz
      have hzK := hLK hz
      simp only [K, Finset.mem_insert] at hzK
      rcases hzK with rfl | hzS
      · exact (hn hz).elim
      · exact hzS
    have hLle := card_le_alphaOn hLS hLind
    rw [hLcard] at hLle
    omega
  let I := apexOldPart x y L
  have hIcardAdd : I.card + 1 = L.card :=
    apexOldPart_card_add_one_of_mem L hnoneL
  have hIJ : I ⊆ J := by
    intro z hz
    obtain ⟨d, hdL, rfl⟩ := mem_apexOldPart.mp hz
    have hdK := hLK hdL
    simp only [K, Finset.mem_insert] at hdK
    rcases hdK with hnone | hdS
    · exact (Option.some_ne_none d hnone).elim
    · exact mem_apexOldPart.mpr ⟨d, hdS, rfl⟩
  have hIind : G.IsIndepSet I := apexOldPart_indep L hLind
  have hIle : I.card ≤ alphaOn G J := card_le_alphaOn hIJ hIind
  have hIcard : I.card = alphaOn G J := by
    apply Nat.le_antisymm hIle
    rw [← halphaSJ]
    rw [hLcard] at hIcardAdd
    omega
  let A := commonNeighborFinset G x y
  have hIA : Disjoint I A := by
    rw [Finset.disjoint_left]
    intro z hzI hzA
    obtain ⟨d, hdL, rfl⟩ := mem_apexOldPart.mp hzI
    have hdcommon := mem_commonNeighborFinset.mp hzA
    exact hLind hnoneL hdL (by simp) hdcommon
  have hIU : I ⊆ J \ A := by
    intro z hz
    exact Finset.mem_sdiff.mpr ⟨hIJ hz, Finset.disjoint_left.mp hIA hz⟩
  have halphaU : alphaOn G (J \ A) = alphaOn G J := by
    apply Nat.le_antisymm
    · exact alphaOn_mono (Finset.sdiff_subset)
    · rw [← hIcard]
      exact card_le_alphaOn hIU hIind

  -- Every common neighbor must already occur in the maximizing witness.
  have hAJ : A ⊆ J := by
    intro t htA
    by_contra htJ
    have ht := mem_commonNeighborFinset.mp htA
    let H := insert x (insert y (insert t J))
    have hHcard := triangleExtension_card hxy ht.1 ht.2 J hxJ hyJ htJ
    have halphaH := alphaOn_triangleExtension_le hxy ht.1 ht.2 J
    have hpotH := potential_le_f G H
    rw [← hJmax] at hpotH
    simp only [potential] at hpotH
    change H.card = J.card + 3 at hHcard
    change alphaOn G H ≤ alphaOn G J + 1 at halphaH
    omega

  -- The common-neighbor lower bound makes `J \ A` smaller than twice its
  -- independence number, exactly the Hajnal hypothesis.
  have hcommon := chi_sub_two_lt_commonNeighbors
    hmin hxy hxu hyu hxv hyv huv huvNA
  have hAcard : A.card = Nat.card (CommonNeighbor G x y) := by
    letI : Fintype (CommonNeighbor G x y) := Fintype.ofFinite _
    let e : CommonNeighbor G x y ≃ {z : V // z ∈ A} := {
      toFun := fun z => ⟨z.1, (mem_commonNeighborFinset).mpr z.2⟩
      invFun := fun z => ⟨z.1, (mem_commonNeighborFinset).mp z.2⟩
      left_inv := fun z => Subtype.ext rfl
      right_inv := fun z => Subtype.ext rfl }
    rw [Nat.card_eq_fintype_card, Fintype.card_congr e, Fintype.card_coe]
  have hgap := Erdos922FullB.counterexample_gap_int G hmin.counterexample
  change f G + 2 < (Erdos922FullB.chiNat G : ℤ) at hgap
  have hA_le_J : A.card ≤ J.card := Finset.card_le_card hAJ
  have hdiff : (J \ A).card = J.card - A.card := Finset.card_sdiff_of_subset hAJ
  have hlarge : (J \ A).card < 2 * alphaOn G (J \ A) := by
    have hJmaxInt := hJmax
    change (J.card : ℤ) - 2 * (alphaOn G J : ℤ) = f G at hJmaxInt
    rw [halphaU, hdiff, hAcard]
    omega
  exact hajnal_apexWitness_contradiction G x y J hxy hxJ hyJ
    (by simpa [A] using halphaU) (by simpa [A] using hlarge) hJmax

end MinimalCounterexampleDiamond

end Erdos922Diamond

open SimpleGraph

namespace Erdos922Recolor

universe u

variable {V : Type u}

namespace EvenCycleBridge

/-- Identify a cyclic index with a pair number and a parity bit. -/
def pairEquiv (p : ℕ) : Fin p × Fin 2 ≃ Fin (2 * p) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm p 2))

def leftEmbedding (p : ℕ) : Fin p ↪ Fin (2 * p) where
  toFun i := pairEquiv p (i, 0)
  inj' _ _ h := congrArg Prod.fst ((pairEquiv p).injective h)

def rightEmbedding (p : ℕ) : Fin p ↪ Fin (2 * p) where
  toFun i := pairEquiv p (i, 1)
  inj' _ _ h := congrArg Prod.fst ((pairEquiv p).injective h)

def leftIndices (p : ℕ) : Finset (Fin (2 * p)) :=
  Finset.univ.map (leftEmbedding p)

def rightIndices (p : ℕ) : Finset (Fin (2 * p)) :=
  Finset.univ.map (rightEmbedding p)

def nextIndex (p : ℕ) (hp : 1 ≤ p) (i : Fin p) : Fin p :=
  ⟨(i.val + 1) % p, Nat.mod_lt _ (by omega)⟩

@[simp] theorem pairEquiv_val (p : ℕ) (i : Fin p) (b : Fin 2) :
    (pairEquiv p (i, b)).val = b.val + 2 * i.val := rfl

/-- The two vertices in one consecutive pair are adjacent on the cycle. -/
theorem pair_adj (p : ℕ) (hp : 1 ≤ p) (i : Fin p) :
    (SimpleGraph.cycleGraph (2 * p)).Adj
      (pairEquiv p (i, 0)) (pairEquiv p (i, 1)) := by
  rw [SimpleGraph.cycleGraph_adj']
  right
  rw [Fin.coe_sub_iff_le.mpr (by
    rw [Fin.le_iff_val_le_val, pairEquiv_val, pairEquiv_val]
    omega)]
  rw [pairEquiv_val, pairEquiv_val]
  omega

/-- The odd vertex of a pair is adjacent to the even vertex of the next
cyclic pair. -/
theorem pair_next_adj (p : ℕ) (hp : 1 ≤ p) (i : Fin p) :
    (SimpleGraph.cycleGraph (2 * p)).Adj
      (pairEquiv p (i, 1)) (pairEquiv p (nextIndex p hp i, 0)) := by
  rw [SimpleGraph.cycleGraph_adj']
  by_cases hi : i.val + 1 < p
  · right
    have hval : (nextIndex p hp i).val = i.val + 1 := by
      simp [nextIndex, Nat.mod_eq_of_lt hi]
    rw [Fin.coe_sub_iff_le.mpr]
    · rw [pairEquiv_val, pairEquiv_val, hval]
      omega
    · rw [Fin.le_iff_val_le_val, pairEquiv_val, pairEquiv_val, hval]
      omega
  · right
    have hilast : i.val = p - 1 := by omega
    have hnext : (nextIndex p hp i).val = 0 := by
      simp only [nextIndex]
      have hip : i.val + 1 = p := by omega
      simp [hip]
    rw [Fin.coe_sub_iff_lt.mpr]
    · rw [pairEquiv_val, pairEquiv_val, hilast, hnext]
      omega
    · rw [Fin.lt_iff_val_lt_val, pairEquiv_val, pairEquiv_val, hilast, hnext]
      omega

theorem independent_card_le (p : ℕ) (hp : 1 ≤ p)
    (J : Finset (Fin (2 * p)))
    (hJ : (SimpleGraph.cycleGraph (2 * p)).IsIndepSet J) :
    J.card ≤ p := by
  classical
  let f : {x // x ∈ J} → Fin p := fun x ↦ ((pairEquiv p).symm x.1).1
  have hf : Function.Injective f := by
    intro x y hxyfst
    apply Subtype.ext
    by_contra hxy
    let cx := (pairEquiv p).symm x.1
    let cy := (pairEquiv p).symm y.1
    have hfst : cx.1 = cy.1 := hxyfst
    have hsnd : cx.2 ≠ cy.2 := by
      intro hsnd
      have hc : cx = cy := Prod.ext hfst hsnd
      apply hxy
      calc
        x.1 = pairEquiv p cx := ((pairEquiv p).apply_symm_apply x.1).symm
        _ = pairEquiv p cy := congrArg (pairEquiv p) hc
        _ = y.1 := (pairEquiv p).apply_symm_apply y.1
    have hbits : (cx.2 = 0 ∧ cy.2 = 1) ∨ (cx.2 = 1 ∧ cy.2 = 0) := by
      have hcxv : cx.2.val = 0 ∨ cx.2.val = 1 :=
        Nat.le_one_iff_eq_zero_or_eq_one.mp (by omega)
      have hcyv : cy.2.val = 0 ∨ cy.2.val = 1 :=
        Nat.le_one_iff_eq_zero_or_eq_one.mp (by omega)
      rcases hcxv with hcxv | hcxv <;> rcases hcyv with hcyv | hcyv
      · exact (hsnd (Fin.ext (hcxv.trans hcyv.symm))).elim
      · exact Or.inl ⟨Fin.ext hcxv, Fin.ext hcyv⟩
      · exact Or.inr ⟨Fin.ext hcxv, Fin.ext hcyv⟩
      · exact (hsnd (Fin.ext (hcxv.trans hcyv.symm))).elim
    apply hJ x.2 y.2 hxy
    rcases hbits with ⟨hcx, hcy⟩ | ⟨hcx, hcy⟩
    · rw [show x.1 = pairEquiv p cx from ((pairEquiv p).apply_symm_apply x.1).symm,
          show y.1 = pairEquiv p cy from ((pairEquiv p).apply_symm_apply y.1).symm,
          show cx = (cx.1, 0) from Prod.ext rfl hcx,
          show cy = (cx.1, 1) from Prod.ext hfst.symm hcy]
      exact pair_adj p hp cx.1
    · rw [show x.1 = pairEquiv p cx from ((pairEquiv p).apply_symm_apply x.1).symm,
          show y.1 = pairEquiv p cy from ((pairEquiv p).apply_symm_apply y.1).symm,
          show cx = (cx.1, 1) from Prod.ext rfl hcx,
          show cy = (cx.1, 0) from Prod.ext hfst.symm hcy]
      exact (pair_adj p hp cx.1).symm
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_fin] using hcard

theorem iterate_nextIndex (p : ℕ) (hp : 1 ≤ p) (i : Fin p) (m : ℕ) :
    (nextIndex p hp)^[m] i =
      ⟨(i.val + m) % p, Nat.mod_lt _ (by omega)⟩ := by
  induction m with
  | zero =>
      apply Fin.ext
      simp [Nat.mod_eq_of_lt i.isLt]
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih]
      apply Fin.ext
      simp only [nextIndex, Fin.val_mk]
      rw [← Nat.add_assoc]
      exact Nat.ModEq.add_right 1 (Nat.mod_modEq (i.val + m) p)

theorem exists_iterate_nextIndex_eq (p : ℕ) (hp : 1 ≤ p) (i j : Fin p) :
    ∃ m : ℕ, (nextIndex p hp)^[m] i = j := by
  refine ⟨p - i.val + j.val, ?_⟩
  rw [iterate_nextIndex]
  apply Fin.ext
  simp only [Fin.val_mk]
  have hi : i.val ≤ p := i.isLt.le
  rw [← Nat.add_assoc, Nat.add_sub_of_le hi, Nat.add_mod]
  simp [Nat.mod_eq_of_lt j.isLt]

/-- Equality in the even-cycle independence bound is rigid: the independent
set is one of the two alternating parity classes. -/
theorem independent_eq_alternating_of_card
    (p : ℕ) (hp : 1 ≤ p) (J : Finset (Fin (2 * p)))
    (hJ : (SimpleGraph.cycleGraph (2 * p)).IsIndepSet J)
    (hcard : J.card = p) : J = leftIndices p ∨ J = rightIndices p := by
  classical
  let f : {x // x ∈ J} → Fin p := fun x ↦ ((pairEquiv p).symm x.1).1
  have hf : Function.Injective f := by
    intro x y hxyfst
    apply Subtype.ext
    by_contra hxy
    let cx := (pairEquiv p).symm x.1
    let cy := (pairEquiv p).symm y.1
    have hfst : cx.1 = cy.1 := hxyfst
    have hsnd : cx.2 ≠ cy.2 := by
      intro hsnd
      apply hxy
      calc
        x.1 = pairEquiv p cx := ((pairEquiv p).apply_symm_apply x.1).symm
        _ = pairEquiv p cy := congrArg (pairEquiv p) (Prod.ext hfst hsnd)
        _ = y.1 := (pairEquiv p).apply_symm_apply y.1
    have hbits : (cx.2 = 0 ∧ cy.2 = 1) ∨ (cx.2 = 1 ∧ cy.2 = 0) := by
      have hcxv : cx.2.val = 0 ∨ cx.2.val = 1 :=
        Nat.le_one_iff_eq_zero_or_eq_one.mp (by omega)
      have hcyv : cy.2.val = 0 ∨ cy.2.val = 1 :=
        Nat.le_one_iff_eq_zero_or_eq_one.mp (by omega)
      rcases hcxv with hcxv | hcxv <;> rcases hcyv with hcyv | hcyv
      · exact (hsnd (Fin.ext (hcxv.trans hcyv.symm))).elim
      · exact Or.inl ⟨Fin.ext hcxv, Fin.ext hcyv⟩
      · exact Or.inr ⟨Fin.ext hcxv, Fin.ext hcyv⟩
      · exact (hsnd (Fin.ext (hcxv.trans hcyv.symm))).elim
    apply hJ x.2 y.2 hxy
    rcases hbits with ⟨hcx, hcy⟩ | ⟨hcx, hcy⟩
    · rw [show x.1 = pairEquiv p cx from ((pairEquiv p).apply_symm_apply x.1).symm,
          show y.1 = pairEquiv p cy from ((pairEquiv p).apply_symm_apply y.1).symm,
          show cx = (cx.1, 0) from Prod.ext rfl hcx,
          show cy = (cx.1, 1) from Prod.ext hfst.symm hcy]
      exact pair_adj p hp cx.1
    · rw [show x.1 = pairEquiv p cx from ((pairEquiv p).apply_symm_apply x.1).symm,
          show y.1 = pairEquiv p cy from ((pairEquiv p).apply_symm_apply y.1).symm,
          show cx = (cx.1, 1) from Prod.ext rfl hcx,
          show cy = (cx.1, 0) from Prod.ext hfst.symm hcy]
      exact (pair_adj p hp cx.1).symm
  have hcards : Fintype.card {x // x ∈ J} = Fintype.card (Fin p) := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using hcard
  have hsurj : Function.Surjective f :=
    ((Fintype.bijective_iff_injective_and_card f).2 ⟨hf, hcards⟩).2
  have hexact (i : Fin p) :
      pairEquiv p (i, 0) ∈ J ∨ pairEquiv p (i, 1) ∈ J := by
    obtain ⟨x, hx⟩ := hsurj i
    let cx := (pairEquiv p).symm x.1
    have hfst : cx.1 = i := hx
    have hbit : cx.2 = 0 ∨ cx.2 = 1 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (by omega : cx.2.val ≤ 1) with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    rcases hbit with hbit | hbit
    · left
      have heq : x.1 = pairEquiv p (i, 0) := by
        calc
          x.1 = pairEquiv p cx := ((pairEquiv p).apply_symm_apply x.1).symm
          _ = pairEquiv p (i, 0) := congrArg (pairEquiv p) (Prod.ext hfst hbit)
      exact heq ▸ x.2
    · right
      have heq : x.1 = pairEquiv p (i, 1) := by
        calc
          x.1 = pairEquiv p cx := ((pairEquiv p).apply_symm_apply x.1).symm
          _ = pairEquiv p (i, 1) := congrArg (pairEquiv p) (Prod.ext hfst hbit)
      exact heq ▸ x.2
  have hprop {i : Fin p} (hi : pairEquiv p (i, 1) ∈ J) :
      pairEquiv p (nextIndex p hp i, 1) ∈ J := by
    rcases hexact (nextIndex p hp i) with hleft | hright
    · exact (hJ hi hleft (by
          intro heq
          exact (pair_next_adj p hp i).ne heq) (pair_next_adj p hp i)).elim
    · exact hright
  by_cases hnone : ∀ i : Fin p, pairEquiv p (i, 1) ∉ J
  · left
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨i, _hi, rfl⟩
      exact (hexact i).resolve_right (hnone i)
    · simp [leftIndices, hcard]
  · right
    push Not at hnone
    obtain ⟨i, hi⟩ := hnone
    have hiter : ∀ m : ℕ, pairEquiv p ((nextIndex p hp)^[m] i, 1) ∈ J := by
      intro m
      induction m with
      | zero => simpa using hi
      | succ m ih =>
          rw [Function.iterate_succ_apply']
          exact hprop ih
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨j, _hj, rfl⟩
      obtain ⟨m, hm⟩ := exists_iterate_nextIndex_eq p hp i j
      have hmemb := hiter m
      rw [hm] at hmemb
      exact hmemb
    · simp [rightIndices, hcard]

theorem left_right_disjoint (p : ℕ) :
    Disjoint (leftIndices p) (rightIndices p) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxL hxR
  rcases Finset.mem_map.mp hxL with ⟨i, _hi, rfl⟩
  rcases Finset.mem_map.mp hxR with ⟨j, _hj, heq⟩
  change pairEquiv p (j, 1) = pairEquiv p (i, 0) at heq
  have hpairs : (i, (0 : Fin 2)) = (j, (1 : Fin 2)) := by
    rw [← (pairEquiv p).symm_apply_apply (i, (0 : Fin 2)),
      ← (pairEquiv p).symm_apply_apply (j, (1 : Fin 2))]
    exact congrArg (pairEquiv p).symm heq.symm
  have : (0 : Fin 2) = 1 := congrArg Prod.snd hpairs
  exact Fin.zero_ne_one this

theorem leftIndices_card (p : ℕ) : (leftIndices p).card = p := by
  classical
  simp [leftIndices]

theorem rightIndices_card (p : ℕ) : (rightIndices p).card = p := by
  classical
  simp [rightIndices]

theorem leftIndices_independent (p : ℕ) (hp : 1 ≤ p) :
    (SimpleGraph.cycleGraph (2 * p)).IsIndepSet (leftIndices p) := by
  classical
  let c := SimpleGraph.cycleGraph.bicoloring_of_even (2 * p)
    (show Even (2 * p) by refine ⟨p, ?_⟩; omega)
  apply (c.isIndepSet_colorClass true).mono
  intro x hx
  rcases Finset.mem_map.mp hx with ⟨i, _hi, rfl⟩
  dsimp only [c, SimpleGraph.cycleGraph.bicoloring_of_even]
  change c (pairEquiv p (i, 0)) = true
  change decide ((pairEquiv p (i, 0)).val % 2 = 0) = true
  rw [pairEquiv_val]
  simp

theorem rightIndices_independent (p : ℕ) (hp : 1 ≤ p) :
    (SimpleGraph.cycleGraph (2 * p)).IsIndepSet (rightIndices p) := by
  classical
  let c := SimpleGraph.cycleGraph.bicoloring_of_even (2 * p)
    (show Even (2 * p) by refine ⟨p, ?_⟩; omega)
  apply (c.isIndepSet_colorClass false).mono
  intro x hx
  rcases Finset.mem_map.mp hx with ⟨i, _hi, rfl⟩
  dsimp only [c, SimpleGraph.cycleGraph.bicoloring_of_even]
  change c (pairEquiv p (i, 1)) = false
  change decide ((pairEquiv p (i, 1)).val % 2 = 0) = false
  rw [pairEquiv_val]
  simp

/-- The canonical two alternating sides of an even cycle satisfy exactly the
abstract configuration used by the even-hole contraction argument. -/
theorem cycleGraph_configuration (p : ℕ) (hp : 2 ≤ p) :
    Erdos922.EvenHole.Configuration (SimpleGraph.cycleGraph (2 * p))
      (leftIndices p) (rightIndices p) p where
  disjoint := left_right_disjoint p
  two_le := hp
  card_left := leftIndices_card p
  card_right := rightIndices_card p
  indep_left := leftIndices_independent p (by omega)
  indep_right := rightIndices_independent p (by omega)
  cycle_bound := by
    intro I _hsub hI
    exact independent_card_le p (by omega) I hI
  cycle_eq_of_card := by
    intro I _hsub hI hcard
    exact independent_eq_alternating_of_card p (by omega) I hI hcard

/-- An abstract even-hole configuration transports along an induced graph
embedding.  The proof explicitly pulls every independent subset of the image
back through the embedding, so both the extremal bound and its equality case
are preserved. -/
theorem configuration_map_embedding
    {W : Type v} [Fintype W] [DecidableEq W] [DecidableEq V]
    {H : SimpleGraph W} {G : SimpleGraph V} (φ : H ↪g G)
    {A B : Finset W} {p : ℕ}
    (hC : Erdos922.EvenHole.Configuration H A B p) :
    Erdos922.EvenHole.Configuration G
      (A.map φ.toEmbedding) (B.map φ.toEmbedding) p := by
  classical
  let e : W ↪ V := φ.toEmbedding
  have image_independent (S : Finset W) (hS : H.IsIndepSet S) :
      G.IsIndepSet (S.map e) := by
    intro x hx y hy hxy hGxy
    rcases Finset.mem_map.mp hx with ⟨a, ha, rfl⟩
    rcases Finset.mem_map.mp hy with ⟨b, hb, rfl⟩
    apply hS ha hb
    · intro hab
      subst b
      exact hxy rfl
    · exact φ.map_rel_iff.mp hGxy
  have pullback (I : Finset V)
      (hsub : I ⊆ A.map e ∪ B.map e) :
      ∃ J : Finset W, J ⊆ A ∪ B ∧ J.map e = I := by
    let J := (A ∪ B).filter fun a ↦ e a ∈ I
    refine ⟨J, Finset.filter_subset _ _, ?_⟩
    apply Finset.ext
    intro x
    constructor
    · intro hx
      rcases Finset.mem_map.mp hx with ⟨a, ha, rfl⟩
      exact (Finset.mem_filter.mp ha).2
    · intro hx
      have hxAB := hsub hx
      rw [← Finset.map_union] at hxAB
      rcases Finset.mem_map.mp hxAB with ⟨a, haAB, hax⟩
      apply Finset.mem_map.mpr
      refine ⟨a, Finset.mem_filter.mpr ⟨haAB, ?_⟩, hax⟩
      exact hax ▸ hx
  refine {
    disjoint := (Finset.disjoint_map e).2 hC.disjoint
    two_le := hC.two_le
    card_left := by simpa [e] using hC.card_left
    card_right := by simpa [e] using hC.card_right
    indep_left := image_independent A hC.indep_left
    indep_right := image_independent B hC.indep_right
    cycle_bound := ?_
    cycle_eq_of_card := ?_ }
  · intro I hsub hI
    obtain ⟨J, hJsub, hmap⟩ := pullback I hsub
    have hJind : H.IsIndepSet J := by
      intro a ha b hb hab hHab
      apply hI
      · rw [← hmap]
        exact Finset.mem_map.mpr ⟨a, ha, rfl⟩
      · rw [← hmap]
        exact Finset.mem_map.mpr ⟨b, hb, rfl⟩
      · exact fun heq ↦ hab (e.injective heq)
      · exact φ.map_rel_iff.mpr hHab
    have hle := hC.cycle_bound J hJsub hJind
    rwa [← hmap, Finset.card_map] 
  · intro I hsub hI hcard
    obtain ⟨J, hJsub, hmap⟩ := pullback I hsub
    have hJind : H.IsIndepSet J := by
      intro a ha b hb hab hHab
      apply hI
      · rw [← hmap]
        exact Finset.mem_map.mpr ⟨a, ha, rfl⟩
      · rw [← hmap]
        exact Finset.mem_map.mpr ⟨b, hb, rfl⟩
      · exact fun heq ↦ hab (e.injective heq)
      · exact φ.map_rel_iff.mpr hHab
    have hJcard : J.card = p := by
      rw [← hcard, ← hmap, Finset.card_map]
    rcases hC.cycle_eq_of_card J hJsub hJind hJcard with hJA | hJB
    · left
      rw [← hmap, hJA]
    · right
      rw [← hmap, hJB]

/-- An induced copy of an even cycle in an ambient graph gives the exact
configuration needed by the contraction theorem. -/
theorem configuration_of_induced_even_cycle_iso
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) (C : Set V)
    (p : ℕ) (hp : 2 ≤ p)
    (e : G.induce C ≃g SimpleGraph.cycleGraph (2 * p)) :
    ∃ A B : Finset V, Erdos922.EvenHole.Configuration G A B p := by
  let φ : SimpleGraph.cycleGraph (2 * p) ↪g G :=
    (SimpleGraph.Embedding.induce C).comp e.symm.toEmbedding
  refine ⟨(leftIndices p).map φ.toEmbedding,
    (rightIndices p).map φ.toEmbedding, ?_⟩
  exact configuration_map_embedding φ (cycleGraph_configuration p hp)

/-- An order-minimal counterexample contains no induced even cycle (stated
as an isomorphism onto an induced subgraph). -/
theorem no_induced_even_cycle_iso_of_no_configuration
    [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hnone : ¬ ∃ (A B : Finset V) (p : ℕ),
      Erdos922.EvenHole.Configuration G A B p) :
    ¬ ∃ (C : Set V) (p : ℕ), 2 ≤ p ∧
      Nonempty (G.induce C ≃g SimpleGraph.cycleGraph (2 * p)) := by
  rintro ⟨C, p, hp, ⟨e⟩⟩
  obtain ⟨A, B, hC⟩ := configuration_of_induced_even_cycle_iso G C p hp e
  exact hnone ⟨A, B, p, hC⟩


end EvenCycleBridge

/-- A local adjacency-pattern formulation of having no induced diamond
(`K₄` with one edge removed).  The explicit distinctness fields make the
definition robust when used independently of a surrounding vertex set. -/
def NoInducedDiamond (G : SimpleGraph V) : Prop :=
  ∀ {a b c d : V},
    a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    G.Adj a b → G.Adj a c → G.Adj b c →
    G.Adj a d → G.Adj b d → ¬ G.Adj c d → False

/-- A local adjacency-pattern formulation of having no induced four-cycle. -/
def NoInducedFourCycle (G : SimpleGraph V) : Prop :=
  ∀ {a b c d : V},
    a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
    ¬ G.Adj a c → ¬ G.Adj b d → False

/-- A vertex outside a maximal clique misses some vertex of that clique. -/
theorem exists_not_adj_of_maximal_clique
    (G : SimpleGraph V) {K : Set V} (hK : Maximal G.IsClique K)
    {x : V} (hx : x ∉ K) : ∃ y ∈ K, ¬ G.Adj y x := by
  by_contra h
  push Not at h
  have hins : G.IsClique (insert x K) := by
    intro a ha b hb hab
    simp only [Set.mem_insert_iff] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact (hab rfl).elim
    · exact (h b hb).symm
    · exact h a ha
    · exact hK.1 ha hb hab
  have hsub : insert x K ⊆ K := hK.2 hins (Set.subset_insert x K)
  exact hx (hsub (Set.mem_insert x K))

/-- In a diamond-free graph, every outside vertex has at most one neighbor in
a maximal clique. -/
theorem maximalClique_attachment_unique
    (G : SimpleGraph V) {K : Set V} (hK : Maximal G.IsClique K)
    (hdiamond : NoInducedDiamond G) :
    ∀ {r s : K}, r ≠ s → ∀ {x : V}, x ∉ K →
      G.Adj s.1 x → ¬ G.Adj r.1 x := by
  intro r s hrs x hx hsx hrx
  obtain ⟨t, htK, htx⟩ := exists_not_adj_of_maximal_clique G hK hx
  have hrs' : r.1 ≠ s.1 := fun h ↦ hrs (Subtype.ext h)
  have hrt : r.1 ≠ t := fun h ↦ htx (h ▸ hrx)
  have hst : s.1 ≠ t := fun h ↦ htx (h ▸ hsx)
  have hrx' : r.1 ≠ x := fun h ↦ hx (h ▸ r.2)
  have hsx' : s.1 ≠ x := fun h ↦ hx (h ▸ s.2)
  have htx' : t ≠ x := fun h ↦ hx (h ▸ htK)
  exact hdiamond hrs' hrt hrx' hst hsx' htx'
    (hK.1 r.2 s.2 hrs') (hK.1 r.2 htK hrt)
    (hK.1 s.2 htK hst) hrx hsx htx

/-- With induced four-cycles also excluded, attachment sets belonging to
different maximal-clique vertices are anticomplete. -/
theorem maximalClique_attachments_anticomplete
    (G : SimpleGraph V) {K : Set V} (hK : Maximal G.IsClique K)
    (hdiamond : NoInducedDiamond G) (hfour : NoInducedFourCycle G) :
    ∀ {r s : K}, r ≠ s → ∀ {x y : V}, x ∉ K → y ∉ K →
      G.Adj r.1 x → G.Adj s.1 y → ¬ G.Adj x y := by
  intro r s hrs x y hx hy hrx hsy hxy
  have hrs' : r.1 ≠ s.1 := fun h ↦ hrs (Subtype.ext h)
  have hsx : ¬ G.Adj s.1 x :=
    maximalClique_attachment_unique G hK hdiamond (r := s) (s := r) hrs.symm hx hrx
  have hry : ¬ G.Adj r.1 y :=
    maximalClique_attachment_unique G hK hdiamond (r := r) (s := s) hrs hy hsy
  have hrx' : r.1 ≠ x := fun h ↦ hx (h ▸ r.2)
  have hry' : r.1 ≠ y := fun h ↦ hy (h ▸ r.2)
  have hxy' : x ≠ y := hxy.ne
  have hxs : x ≠ s.1 := fun h ↦ hx (h ▸ s.2)
  have hys : y ≠ s.1 := fun h ↦ hy (h ▸ s.2)
  exact hfour hrx' hry' hrs' hxy' hxs hys
    hrx hxy hsy.symm (hK.1 s.2 r.2 hrs'.symm) hry (fun h ↦ hsx h.symm)

/-- A shortest-cycle hypothesis stated directly in terms of all cycle walks. -/
def IsShortestCycleLength (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∀ {v : V} (p : G.Walk v v), p.IsCycle → n ≤ p.length

theorem isChordless_of_path_length_add_one_lt_shortest
    (G : SimpleGraph V) {n : ℕ} (hshort : IsShortestCycleLength G n)
    {a b : V} (P : G.Walk a b) (hP : P.IsPath)
    (hlen : P.length + 1 < n) : P.IsChordless := by
  classical
  rw [Walk.isChordless_iff_forall_mem_edges]
  intro x y hx hy hxy
  by_contra hnotedge
  have close_of_idx_le {x y : V}
      (hx : x ∈ P.support) (hy : y ∈ P.support) (hxy : G.Adj x y)
      (hnotedge : s(x, y) ∉ P.edges)
      (hidx : P.support.idxOf x ≤ P.support.idxOf y) : False := by
    let Q := P.dropUntil x hx
    have hyQ : y ∈ Q.support := by
      dsimp only [Q]
      rw [Walk.dropUntil_eq_drop, Walk.support_copy,
        Walk.drop_support_eq_support_drop_min]
      have hxlt := List.idxOf_lt_length_of_mem hx
      have hylt := List.idxOf_lt_length_of_mem hy
      have hxle : P.support.idxOf x ≤ P.length := by
        rw [Walk.length_support] at hxlt
        omega
      rw [Nat.min_eq_left hxle]
      rw [List.mem_drop_iff_getElem]
      refine ⟨P.support.idxOf y - P.support.idxOf x, ?_, ?_⟩
      · rw [Walk.length_support]
        rw [Nat.sub_add_cancel hidx]
        simpa only [Walk.length_support] using hylt
      · have heq := List.getElem_idxOf hylt
        have hsum : P.support.idxOf x +
            (P.support.idxOf y - P.support.idxOf x) = P.support.idxOf y :=
          Nat.add_sub_of_le hidx
        have hopen : P.support[P.support.idxOf x +
            (P.support.idxOf y - P.support.idxOf x)]? = some y := by
          rw [hsum, List.getElem?_eq_getElem hylt, heq]
        exact (List.getElem?_eq_some_iff.mp hopen).2
    let S := Q.takeUntil y hyQ
    have hQ : Q.IsPath := hP.dropUntil hx
    have hS : S.IsPath := hQ.takeUntil hyQ
    have hedgeS : s(y, x) ∉ S.edges := by
      intro hmem
      apply hnotedge
      rw [Sym2.eq_swap]
      exact P.edges_dropUntil_subset_edges hx
        (Q.edges_takeUntil_subset_edges hyQ hmem)
    let d : G.Walk y y := S.cons hxy.symm
    have hd : d.IsCycle :=
      (Walk.cons_isCycle_iff S hxy.symm).2 ⟨hS, hedgeS⟩
    have hSle : S.length ≤ P.length :=
      (Q.length_takeUntil_le_length hyQ).trans (P.length_dropUntil_le_length hx)
    have hlower := hshort d hd
    change n ≤ S.length + 1 at hlower
    omega
  by_cases hidx : P.support.idxOf x ≤ P.support.idxOf y
  · exact close_of_idx_le hx hy hxy hnotedge hidx
  · have hidx' : P.support.idxOf y ≤ P.support.idxOf x := Nat.le_of_not_ge hidx
    have hswap : s(y, x) ∉ P.edges := by simpa only [Sym2.eq_swap] using hnotedge
    exact close_of_idx_le hy hx hxy.symm hswap hidx'

/-- A path inside an induced core, together with one outside vertex adjacent
to its distinct endpoints, closes up to a cycle two edges longer than the
path. -/
theorem exists_cycle_of_induced_path_and_two_neighbors
    (G : SimpleGraph V) {C : Set V} {r s : C} (hrs : r ≠ s)
    (P : (G.induce C).Walk r s) (hP : P.IsPath)
    {x : V} (hx : x ∉ C) (hrx : G.Adj r.1 x) (hsx : G.Adj s.1 x) :
    ∃ (z : V) (c : G.Walk z z), c.IsCycle ∧ c.length = P.length + 2 := by
  let P' := P.map (SimpleGraph.Embedding.induce (G := G) C).toHom
  have hP' : P'.IsPath :=
    hP.map (SimpleGraph.Embedding.induce (G := G) C).injective
  have hxP' : x ∉ P'.support := by
    intro hmem
    have hmem' : ∃ y ∈ P.support,
        (SimpleGraph.Embedding.induce (G := G) C).toHom y = x := by
      simpa only [P', Walk.support_map, List.mem_map] using hmem
    obtain ⟨y, _hy, hyx⟩ := hmem'
    have hyC : (SimpleGraph.Embedding.induce (G := G) C).toHom y ∈ C := y.2
    exact hx (hyx ▸ hyC)
  let Q : G.Walk x s.1 := P'.cons hrx.symm
  have hQ : Q.IsPath := hP'.cons hxP'
  have hPpos : 0 < P.length := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hrs (P.eq_of_length_eq_zero hzero)
  have hedge : s(s.1, x) ∉ Q.edges := by
    intro hmem
    have hone := hQ.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ hmem)
    have hQlen : Q.length = P.length + 1 := by
      change P'.length + 1 = P.length + 1
      dsimp only [P']
      rw [Walk.length_map]
    omega
  refine ⟨s.1, Q.cons hsx, ?_, ?_⟩
  · exact (Walk.cons_isCycle_iff Q hsx).2 ⟨hQ, hedge⟩
  · change Q.length + 1 = P.length + 2
    have hQlen : Q.length = P.length + 1 := by
      change P'.length + 1 = P.length + 1
      dsimp only [P']
      rw [Walk.length_map]
    omega

theorem exists_cycle_of_induced_path_and_attachment_edge
    (G : SimpleGraph V) {C : Set V} {r s : C} (hrs : r ≠ s)
    (P : (G.induce C).Walk r s) (hP : P.IsPath)
    {x y : V} (hx : x ∉ C) (hy : y ∉ C)
    (hrx : G.Adj r.1 x) (hxy : G.Adj x y) (hys : G.Adj y s.1) :
    ∃ (z : V) (c : G.Walk z z), c.IsCycle ∧ c.length = P.length + 3 := by
  let P' := P.map (SimpleGraph.Embedding.induce (G := G) C).toHom
  have hP' : P'.IsPath :=
    hP.map (SimpleGraph.Embedding.induce (G := G) C).injective
  have hxP' : x ∉ P'.support := by
    intro hmem
    have hmem' : ∃ t ∈ P.support,
        (SimpleGraph.Embedding.induce (G := G) C).toHom t = x := by
      simpa only [P', Walk.support_map, List.mem_map] using hmem
    obtain ⟨t, _ht, htx⟩ := hmem'
    exact hx (htx ▸ t.2)
  have hyP' : y ∉ P'.support := by
    intro hmem
    have hmem' : ∃ t ∈ P.support,
        (SimpleGraph.Embedding.induce (G := G) C).toHom t = y := by
      simpa only [P', Walk.support_map, List.mem_map] using hmem
    obtain ⟨t, _ht, hty⟩ := hmem'
    exact hy (hty ▸ t.2)
  have hyx : y ≠ x := hxy.ne.symm
  let Q : G.Walk x s.1 := P'.cons hrx.symm
  have hQ : Q.IsPath := hP'.cons hxP'
  have hyQ : y ∉ Q.support := by
    change y ∉ x :: P'.support
    intro hmem
    rcases (List.mem_cons.mp hmem) with h | h
    · exact hyx h
    · exact hyP' h
  let R : G.Walk y s.1 := Q.cons hxy.symm
  have hR : R.IsPath := hQ.cons hyQ
  have hPpos : 0 < P.length := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hrs (P.eq_of_length_eq_zero hzero)
  have hedge : s(s.1, y) ∉ R.edges := by
    intro hmem
    have hone := hR.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ hmem)
    have hRlen : R.length = P.length + 2 := by
      change P'.length + 2 = P.length + 2
      dsimp only [P']
      rw [Walk.length_map]
    omega
  refine ⟨s.1, R.cons hys.symm, ?_, ?_⟩
  · exact (Walk.cons_isCycle_iff R hys.symm).2 ⟨hR, hedge⟩
  · change R.length + 1 = P.length + 3
    change P'.length + 3 = P.length + 3
    dsimp only [P']
    rw [Walk.length_map]

/-- If the core path is chordless and each outside vertex has its indicated
endpoint as its unique neighbor in the core, the cycle closed through the
outside edge is chordless in the ambient graph. -/
theorem exists_chordless_cycle_of_induced_path_and_attachment_edge
    (G : SimpleGraph V) {C : Set V} {r s : C} (hrs : r ≠ s)
    (P : (G.induce C).Walk r s) (hP : P.IsPath) (hPchord : P.IsChordless)
    {x y : V} (hx : x ∉ C) (hy : y ∉ C)
    (hrx : G.Adj r.1 x) (hxy : G.Adj x y) (hys : G.Adj y s.1)
    (hxunique : ∀ t : C, t ≠ r → ¬ G.Adj t.1 x)
    (hyunique : ∀ t : C, t ≠ s → ¬ G.Adj t.1 y) :
    ∃ (z : V) (c : G.Walk z z),
      c.IsCycle ∧ c.IsChordless ∧ c.length = P.length + 3 := by
  let ι := (SimpleGraph.Embedding.induce (G := G) C).toHom
  let P' := P.map ι
  have hP' : P'.IsPath :=
    hP.map (SimpleGraph.Embedding.induce (G := G) C).injective
  have hxP' : x ∉ P'.support := by
    intro hmem
    have hmem' : ∃ t ∈ P.support, ι t = x := by
      simpa only [P', Walk.support_map, List.mem_map] using hmem
    obtain ⟨t, _ht, htx⟩ := hmem'
    exact hx (htx ▸ t.2)
  have hyP' : y ∉ P'.support := by
    intro hmem
    have hmem' : ∃ t ∈ P.support, ι t = y := by
      simpa only [P', Walk.support_map, List.mem_map] using hmem
    obtain ⟨t, _ht, hty⟩ := hmem'
    exact hy (hty ▸ t.2)
  let Q : G.Walk x s.1 := P'.cons hrx.symm
  have hQ : Q.IsPath := hP'.cons hxP'
  have hyQ : y ∉ Q.support := by
    change y ∉ x :: P'.support
    intro hmem
    rcases List.mem_cons.mp hmem with h | h
    · exact hxy.ne.symm h
    · exact hyP' h
  let R : G.Walk y s.1 := Q.cons hxy.symm
  have hR : R.IsPath := hQ.cons hyQ
  have hPpos : 0 < P.length := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hrs (P.eq_of_length_eq_zero hzero)
  have hedge : s(s.1, y) ∉ R.edges := by
    intro hmem
    have hone := hR.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ hmem)
    have hRlen : R.length = P.length + 2 := by
      change P'.length + 2 = P.length + 2
      dsimp only [P']
      rw [Walk.length_map]
    omega
  let d : G.Walk s.1 s.1 := R.cons hys.symm
  have hdcycle : d.IsCycle :=
    (Walk.cons_isCycle_iff R hys.symm).2 ⟨hR, hedge⟩
  have hsP' : s.1 ∈ P'.support := P'.end_mem_support
  have normalize_support {a : V} (ha : a ∈ d.support) :
      a = y ∨ a = x ∨ a ∈ P'.support := by
    change a ∈ s.1 :: y :: x :: P'.support at ha
    simp only [List.mem_cons] at ha
    rcases ha with ha | ha | ha | ha
    · exact Or.inr (Or.inr (ha ▸ hsP'))
    · exact Or.inl ha
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr ha)
  have core_preimage {a : V} (ha : a ∈ P'.support) :
      ∃ t : C, t ∈ P.support ∧ t.1 = a := by
    simp only [P', Walk.support_map, List.mem_map] at ha
    obtain ⟨t, ht, hta⟩ := ha
    exact ⟨t, ht, hta⟩
  have core_edge_mem {a b : V} (ha : a ∈ P'.support) (hb : b ∈ P'.support)
      (hab : G.Adj a b) : s(a, b) ∈ P'.edges := by
    obtain ⟨ta, hta, rfl⟩ := core_preimage ha
    obtain ⟨tb, htb, rfl⟩ := core_preimage hb
    have habC : (G.induce C).Adj ta tb := hab
    have hedgeP := hPchord.mem_edges hta htb habC
    change s(ι ta, ι tb) ∈ (P.map ι).edges
    rw [Walk.edges_map, List.mem_map]
    exact ⟨s(ta, tb), hedgeP, rfl⟩
  have hdchord : d.IsChordless := by
    rw [Walk.isChordless_iff_forall_mem_edges]
    intro a b ha hb hab
    have ha' := normalize_support ha
    have hb' := normalize_support hb
    change s(a, b) ∈ s(s.1, y) :: s(y, x) :: s(x, r.1) :: P'.edges
    simp only [List.mem_cons]
    rcases ha' with rfl | rfl | haC <;> rcases hb' with rfl | rfl | hbC
    · exact (hab.ne rfl).elim
    · exact Or.inr (Or.inl rfl)
    · obtain ⟨tb, htb, htbval⟩ := core_preimage hbC
      have htbs : tb = s := by
        by_contra hne
        exact hyunique tb hne (htbval ▸ hab.symm)
      subst tb
      have hby : b = s.1 := htbval.symm
      subst b
      exact Or.inl Sym2.eq_swap
    · exact Or.inr (Or.inl Sym2.eq_swap)
    · exact (hab.ne rfl).elim
    · obtain ⟨tb, htb, htbval⟩ := core_preimage hbC
      have htbr : tb = r := by
        by_contra hne
        exact hxunique tb hne (htbval ▸ hab.symm)
      subst tb
      have hbx : b = r.1 := htbval.symm
      subst b
      exact Or.inr (Or.inr (Or.inl rfl))
    · obtain ⟨ta, hta, htaval⟩ := core_preimage haC
      have htas : ta = s := by
        by_contra hne
        exact hyunique ta hne (htaval ▸ hab)
      subst ta
      have hay : a = s.1 := htaval.symm
      subst a
      exact Or.inl rfl
    · obtain ⟨ta, hta, htaval⟩ := core_preimage haC
      have htar : ta = r := by
        by_contra hne
        exact hxunique ta hne (htaval ▸ hab)
      subst ta
      have hax : a = r.1 := htaval.symm
      subst a
      exact Or.inr (Or.inr (Or.inl Sym2.eq_swap))
    · exact Or.inr (Or.inr (Or.inr (core_edge_mem haC hbC hab)))
  refine ⟨s.1, d, hdcycle, hdchord, ?_⟩
  change P'.length + 3 = P.length + 3
  dsimp only [P']
  rw [Walk.length_map]

/-- On a Hamiltonian cycle of length at least five, either of the two arcs
between distinct vertices can be chosen so that adding two edges still gives
a strictly shorter cycle. -/
theorem exists_short_arc_of_hamiltonian_cycle
    (G : SimpleGraph V) {C : Set V} {v : C}
    (c : (G.induce C).Walk v v) (hc : c.IsCycle)
    (hall : ∀ w : C, w ∈ c.support)
    {n : ℕ} (hcn : c.length = n) (hn : 5 ≤ n)
    (r s : C) (hrs : r ≠ s) :
    ∃ P : (G.induce C).Walk r s, P.IsPath ∧ P.length + 2 < n := by
  classical
  have hrmem : r ∈ c.support := hall r
  let cr : (G.induce C).Walk r r := c.rotate r hrmem
  have hcr : cr.IsCycle := hc.rotate hrmem
  have hsmem : s ∈ cr.support :=
    (Walk.mem_support_rotate_iff c r hrmem).2 (hall s)
  let P : (G.induce C).Walk r s := cr.takeUntil s hsmem
  let Q : (G.induce C).Walk s r := cr.dropUntil s hsmem
  have hP : P.IsPath := hcr.isPath_takeUntil hsmem
  have hPnot : ¬ P.Nil := by
    intro hnil
    exact hrs ((Walk.nil_takeUntil cr hsmem).mp hnil)
  have hpq : P.append Q = cr := Walk.take_spec cr hsmem
  have happ : (P.append Q).IsCycle := hpq ▸ hcr
  have hQ : Q.IsPath := happ.isPath_of_append_right hPnot
  have hsum : P.length + Q.length = n := by
    rw [← Walk.length_append, hpq]
    simpa [cr] using hcn
  by_cases hle : P.length ≤ Q.length
  · exact ⟨P, hP, by omega⟩
  · refine ⟨Q.reverse, hQ.reverse, ?_⟩
    simp only [Walk.length_reverse]
    omega

/-- An induced copy of the cycle graph supplies a spanning cycle walk in the
induced core. -/
theorem exists_spanning_cycle_of_induced_cycle_iso
    (G : SimpleGraph V) {C : Set V} {n : ℕ} (hn : 3 ≤ n)
    (e : G.induce C ≃g SimpleGraph.cycleGraph n) :
    ∃ (v : C) (c : (G.induce C).Walk v v),
      c.IsCycle ∧ c.length = n ∧ ∀ w : C, w ∈ c.support := by
  classical
  letI : Fintype C := Fintype.ofEquiv (Fin n) e.symm.toEquiv
  have hcopy : SimpleGraph.cycleGraph n ⊑ G.induce C := ⟨e.symm.toCopy⟩
  obtain ⟨v, c, hc, hcn⟩ :=
    (SimpleGraph.cycleGraph_isContained_iff (by omega)).mp hcopy
  have hcard : Fintype.card C = n := by
    simpa using e.card_eq
  have hham : c.IsHamiltonianCycle :=
    Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr
      ⟨hc, by simpa [hcard] using hcn⟩
  exact ⟨v, c, hc, hcn, hham.mem_support⟩

/-- A vertex outside a shortest induced cycle of length at least five has at
most one neighbor on the cycle. -/
theorem shortestCycle_attachment_unique
    (G : SimpleGraph V) {C : Set V} {n : ℕ} (hn : 5 ≤ n)
    (e : G.induce C ≃g SimpleGraph.cycleGraph n)
    (hshort : IsShortestCycleLength G n) :
    ∀ {r s : C}, r ≠ s → ∀ {x : V}, x ∉ C →
      G.Adj s.1 x → ¬ G.Adj r.1 x := by
  intro r s hrs x hx hsx hrx
  obtain ⟨v, c, hc, hcn, hall⟩ :=
    exists_spanning_cycle_of_induced_cycle_iso G (by omega) e
  obtain ⟨P, hP, hPlt⟩ :=
    exists_short_arc_of_hamiltonian_cycle G c hc hall hcn hn r s hrs
  obtain ⟨z, d, hd, hdlen⟩ :=
    exists_cycle_of_induced_path_and_two_neighbors G hrs P hP hx hrx hsx
  have hlower := hshort d hd
  omega

/-- Reading a cycle walk at indices `0, ..., length - 1` maps every edge of
the standard cycle graph to an edge of the walk. -/
theorem adj_getVert_of_cycleGraph_adj
    {u : V} {G : SimpleGraph V} {p : G.Walk u u}
    (hp : p.IsCycle) {i j : Fin p.length}
    (hij : (SimpleGraph.cycleGraph p.length).Adj i j) :
    G.Adj (p.getVert i.val) (p.getVert j.val) := by
  have hn : 3 ≤ p.length := hp.three_le_length
  rw [SimpleGraph.cycleGraph_adj'] at hij
  rcases hij with hij | hij
  · by_cases hji : j ≤ i
    · have hval := Fin.coe_sub_iff_le.mpr hji
      rw [hval] at hij
      have heq : i.val = j.val + 1 := by omega
      rw [heq]
      exact (p.adj_getVert_succ (i := j.val) (by omega)).symm
    · have hijlt : i < j := lt_of_not_ge hji
      have hval := Fin.coe_sub_iff_lt.mpr hijlt
      rw [hval] at hij
      have hi : i.val = 0 := by omega
      have hj : j.val = p.length - 1 := by omega
      rw [hi, hj]
      have hadj := p.adj_getVert_succ (i := p.length - 1) (by omega)
      have hsum : p.length - 1 + 1 = p.length := by omega
      rw [hsum] at hadj
      simpa using hadj.symm
  · by_cases hijle : i ≤ j
    · have hval := Fin.coe_sub_iff_le.mpr hijle
      rw [hval] at hij
      have heq : j.val = i.val + 1 := by omega
      rw [heq]
      exact p.adj_getVert_succ (i := i.val) (by omega)
    · have hjilt : j < i := lt_of_not_ge hijle
      have hval := Fin.coe_sub_iff_lt.mpr hjilt
      rw [hval] at hij
      have hj : j.val = 0 := by omega
      have hi : i.val = p.length - 1 := by omega
      rw [hi, hj]
      have hadj := p.adj_getVert_succ (i := p.length - 1) (by omega)
      have hsum : p.length - 1 + 1 = p.length := by omega
      rw [hsum] at hadj
      simpa using hadj

/-- A chordless cycle walk is exactly an induced copy of the corresponding
standard cycle graph on the range of its non-repeated vertices. -/
theorem inducedCycleIso_of_chordless_cycle
    {u : V} {G : SimpleGraph V} (p : G.Walk u u)
    (hp : p.IsCycle) (hchord : p.IsChordless) :
    ∃ D : Set V, Nonempty
      (G.induce D ≃g SimpleGraph.cycleGraph p.length) := by
  let f0 : Fin p.length ↪ V := {
    toFun := fun i ↦ p.getVert i.val
    inj' := by
      intro i j hij
      apply Fin.ext
      exact hp.getVert_injOn'
        (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega) hij }
  let f : SimpleGraph.cycleGraph p.length ↪g G := {
    __ := f0
    map_rel_iff' := by
      intro i j
      constructor
      · intro hG
        have hiS : p.getVert i.val ∈ p.support := p.getVert_mem_support _
        have hjS : p.getVert j.val ∈ p.support := p.getVert_mem_support _
        have hedge : s(p.getVert i.val, p.getVert j.val) ∈ p.edges :=
          hchord.mem_edges hiS hjS hG
        obtain ⟨k, hk, heq⟩ := (p.mk_mem_edges_iff_exists).mp hedge
        rcases Sym2.eq_iff.mp heq with hdir | hrev
        · have hik : i.val = k := by
            symm
            exact hp.getVert_injOn'
              (by simp only [Set.mem_setOf_eq]; omega)
              (by simp only [Set.mem_setOf_eq]; omega) hdir.1
          by_cases hks : k + 1 < p.length
          · have hjk : j.val = k + 1 := by
              symm
              exact hp.getVert_injOn'
                (by simp only [Set.mem_setOf_eq]; omega)
                (by simp only [Set.mem_setOf_eq]; omega) hdir.2
            rw [SimpleGraph.cycleGraph_adj']
            right
            rw [Fin.coe_sub_iff_le.mpr (by omega : i ≤ j)]
            omega
          · have hklen : k + 1 = p.length := by omega
            have hj0 : j.val = 0 := by
              have hv : p.getVert j.val = p.getVert 0 := by
                calc
                  p.getVert j.val = p.getVert (k + 1) := hdir.2.symm
                  _ = p.getVert p.length := congrArg p.getVert hklen
                  _ = p.getVert 0 := p.getVert_length.trans p.getVert_zero.symm
              exact hp.getVert_injOn'
                (by simp only [Set.mem_setOf_eq]; omega)
                (by simp only [Set.mem_setOf_eq]; omega) hv
            rw [SimpleGraph.cycleGraph_adj']
            right
            have hji : j < i := by
              rw [Fin.lt_def, hj0, hik]
              have hn := hp.three_le_length
              omega
            rw [Fin.coe_sub_iff_lt.mpr hji]
            rw [hj0, hik]
            have hn := hp.three_le_length
            omega
        · have hjk : j.val = k := by
            symm
            exact hp.getVert_injOn'
              (by simp only [Set.mem_setOf_eq]; omega)
              (by simp only [Set.mem_setOf_eq]; omega) hrev.1
          by_cases hks : k + 1 < p.length
          · have hik : i.val = k + 1 := by
              symm
              exact hp.getVert_injOn'
                (by simp only [Set.mem_setOf_eq]; omega)
                (by simp only [Set.mem_setOf_eq]; omega) hrev.2
            rw [SimpleGraph.cycleGraph_adj']
            left
            rw [Fin.coe_sub_iff_le.mpr (by omega : j ≤ i)]
            omega
          · have hklen : k + 1 = p.length := by omega
            have hi0 : i.val = 0 := by
              have hv : p.getVert i.val = p.getVert 0 := by
                calc
                  p.getVert i.val = p.getVert (k + 1) := hrev.2.symm
                  _ = p.getVert p.length := congrArg p.getVert hklen
                  _ = p.getVert 0 := p.getVert_length.trans p.getVert_zero.symm
              exact hp.getVert_injOn'
                (by simp only [Set.mem_setOf_eq]; omega)
                (by simp only [Set.mem_setOf_eq]; omega) hv
            rw [SimpleGraph.cycleGraph_adj']
            left
            have hij : i < j := by
              rw [Fin.lt_def, hi0, hjk]
              have hn := hp.three_le_length
              omega
            rw [Fin.coe_sub_iff_lt.mpr hij]
            rw [hi0, hjk]
            have hn := hp.three_le_length
            omega
      · exact adj_getVert_of_cycleGraph_adj hp }
  exact ⟨Set.range f, ⟨f.isoInduceRange.symm⟩⟩


def NoInducedEvenCycleIso (G : SimpleGraph V) : Prop :=
  ¬ ∃ (D : Set V) (p : ℕ), 2 ≤ p ∧
    Nonempty (G.induce D ≃g SimpleGraph.cycleGraph (2 * p))

/-- Under induced-even-cycle exclusion, no chordless cycle walk can have
even length. -/
theorem not_even_length_of_chordless_cycle
    (G : SimpleGraph V) (hno : NoInducedEvenCycleIso G)
    {u : V} (c : G.Walk u u) (hc : c.IsCycle) (hchord : c.IsChordless) :
    ¬ Even c.length := by
  rintro ⟨p, hpLen⟩
  have hlen : c.length = 2 * p := by omega
  have hp : 2 ≤ p := by
    have := hc.three_le_length
    omega
  obtain ⟨D, ⟨e⟩⟩ := inducedCycleIso_of_chordless_cycle c hc hchord
  apply hno
  refine ⟨D, p, hp, ?_⟩
  rw [hlen] at e
  exact ⟨e⟩

/-- The final local anticompleteness argument, isolated from the construction
of the odd arc: an odd chordless core path between two attachment vertices,
together with an edge between their outside neighbors, closes to a forbidden
even chordless cycle. -/
theorem attachments_anticomplete_of_odd_chordless_connectors
    (G : SimpleGraph V) (C : Set V)
    (hno : NoInducedEvenCycleIso G)
    (hunique : ∀ {r s : C}, r ≠ s → ∀ {x : V}, x ∉ C →
      G.Adj s.1 x → ¬ G.Adj r.1 x)
    (hconnector : ∀ (r s : C), r ≠ s →
      ∃ P : (G.induce C).Walk r s,
        P.IsPath ∧ P.IsChordless ∧ Odd P.length) :
    ∀ {r s : C}, r ≠ s → ∀ {x y : V}, x ∉ C → y ∉ C →
      G.Adj r.1 x → G.Adj s.1 y → ¬ G.Adj x y := by
  intro r s hrs x y hx hy hrx hsy hxy
  obtain ⟨P, hP, hPchord, hPodd⟩ := hconnector r s hrs
  have hxunique : ∀ t : C, t ≠ r → ¬ G.Adj t.1 x := by
    intro t htr
    exact hunique htr hx hrx
  have hyunique : ∀ t : C, t ≠ s → ¬ G.Adj t.1 y := by
    intro t hts
    exact hunique hts hy hsy
  obtain ⟨z, d, hdcycle, hdchord, hdlen⟩ :=
    exists_chordless_cycle_of_induced_path_and_attachment_edge
      G hrs P hP hPchord hx hy hrx hxy hsy.symm hxunique hyunique
  apply not_even_length_of_chordless_cycle G hno d hdcycle hdchord
  obtain ⟨m, hm⟩ := hPodd
  refine ⟨m + 2, ?_⟩
  omega

/-- Attachment sets at distinct vertices of a shortest induced odd cycle are
anticomplete when induced even cycles are excluded. -/
theorem shortestOddCycle_attachments_anticomplete
    (G : SimpleGraph V) {C : Set V} {n : ℕ}
    (hn : 5 ≤ n) (hnOdd : Odd n)
    (e : G.induce C ≃g SimpleGraph.cycleGraph n)
    (hshort : IsShortestCycleLength G n)
    (hno : NoInducedEvenCycleIso G)
    (hunique : ∀ {r s : C}, r ≠ s → ∀ {x : V}, x ∉ C →
      G.Adj s.1 x → ¬ G.Adj r.1 x) :
    ∀ {r s : C}, r ≠ s → ∀ {x y : V}, x ∉ C → y ∉ C →
      G.Adj r.1 x → G.Adj s.1 y → ¬ G.Adj x y := by
  classical
  intro r s hrs x y hx hy hrx hsy hxy
  obtain ⟨v, c, hc, hcn, hall⟩ :=
    exists_spanning_cycle_of_induced_cycle_iso G (by omega) e
  have hrmem : r ∈ c.support := hall r
  let cr : (G.induce C).Walk r r := c.rotate r hrmem
  have hcr : cr.IsCycle := hc.rotate hrmem
  have hsmem : s ∈ cr.support :=
    (Walk.mem_support_rotate_iff c r hrmem).2 (hall s)
  let P : (G.induce C).Walk r s := cr.takeUntil s hsmem
  let Q : (G.induce C).Walk s r := cr.dropUntil s hsmem
  let QR : (G.induce C).Walk r s := Q.reverse
  have hP : P.IsPath := hcr.isPath_takeUntil hsmem
  have hPnot : ¬ P.Nil := by
    intro hnil
    exact hrs ((Walk.nil_takeUntil cr hsmem).mp hnil)
  have hpq : P.append Q = cr := Walk.take_spec cr hsmem
  have happ : (P.append Q).IsCycle := hpq ▸ hcr
  have hQ : Q.IsPath := happ.isPath_of_append_right hPnot
  have hQR : QR.IsPath := hQ.reverse
  have hsum : P.length + QR.length = n := by
    simp only [QR, Walk.length_reverse]
    rw [← Walk.length_append, hpq]
    simpa [cr] using hcn
  have hPpos : 0 < P.length := by
    rw [Walk.not_nil_iff_lt_length] at hPnot
    exact hPnot
  have hQRpos : 0 < QR.length := by
    apply Nat.pos_of_ne_zero
    intro hz
    have heq : r = s := QR.eq_of_length_eq_zero hz
    exact hrs heq
  obtain ⟨zP, dP, hdP, hdPlen⟩ :=
    exists_cycle_of_induced_path_and_attachment_edge
      G hrs P hP hx hy hrx hxy hsy.symm
  obtain ⟨zQ, dQ, hdQ, hdQlen⟩ :=
    exists_cycle_of_induced_path_and_attachment_edge
      G hrs QR hQR hx hy hrx hxy hsy.symm
  have hlowerP := hshort dP hdP
  have hlowerQ := hshort dQ hdQ
  have hn5 : n = 5 := by
    obtain ⟨t, ht⟩ := hnOdd
    omega
  have hlengths :
      (P.length = 3 ∧ QR.length = 2) ∨
      (P.length = 2 ∧ QR.length = 3) := by
    omega
  have hshortC : IsShortestCycleLength (G.induce C) n := by
    intro w d hd
    let dm := d.map (SimpleGraph.Embedding.induce (G := G) C).toHom
    have hdm : dm.IsCycle :=
      hd.map (SimpleGraph.Embedding.induce (G := G) C).injective
    have hlower := hshort dm hdm
    simpa only [dm, Walk.length_map] using hlower
  have hxunique : ∀ t : C, t ≠ r → ¬ G.Adj t.1 x := by
    intro t htr
    exact hunique htr hx hrx
  have hyunique : ∀ t : C, t ≠ s → ¬ G.Adj t.1 y := by
    intro t hts
    exact hunique hts hy hsy
  rcases hlengths with ⟨hP3, _hQR2⟩ | ⟨_hP2, hQR3⟩
  · have hPchord : P.IsChordless :=
      isChordless_of_path_length_add_one_lt_shortest
        (G.induce C) hshortC P hP (by omega)
    obtain ⟨z, d, hd, hdchord, hdlen⟩ :=
      exists_chordless_cycle_of_induced_path_and_attachment_edge
        G hrs P hP hPchord hx hy hrx hxy hsy.symm hxunique hyunique
    exact not_even_length_of_chordless_cycle G hno d hd hdchord ⟨3, by omega⟩
  · have hQRchord : QR.IsChordless :=
      isChordless_of_path_length_add_one_lt_shortest
        (G.induce C) hshortC QR hQR (by omega)
    obtain ⟨z, d, hd, hdchord, hdlen⟩ :=
      exists_chordless_cycle_of_induced_path_and_attachment_edge
        G hrs QR hQR hQRchord hx hy hrx hxy hsy.symm hxunique hyunique
    exact not_even_length_of_chordless_cycle G hno d hd hdchord ⟨3, by omega⟩

/-- Recolor an independent set with one fresh color.  The tentative coloring
only has to be proper away from the recolored set, and every unrecolored
vertex has to avoid the fresh color. -/
theorem colorable_add_one_of_recolor_set
    (G : SimpleGraph V) (q : ℕ) (base : V → Fin (q + 1)) (R : Set V)
    (hR : G.IsIndepSet R)
    (hbase : ∀ {v w : V}, G.Adj v w → v ∉ R → w ∉ R → base v ≠ base w)
    (hfresh : ∀ v : V, v ∉ R → base v ≠ Fin.last q) :
    G.Colorable (q + 1) := by
  classical
  refine ⟨SimpleGraph.Coloring.mk
    (fun v ↦ if v ∈ R then Fin.last q else base v) ?_⟩
  intro v w hvw
  by_cases hv : v ∈ R
  · by_cases hw : w ∈ R
    · exact (hR hv hw hvw.ne hvw).elim
    · simp only [if_pos hv, if_neg hw]
      exact (hfresh w hw).symm
  · by_cases hw : w ∈ R
    · simp only [if_neg hv, if_pos hw]
      exact hfresh v hv
    · simp only [if_neg hv, if_neg hw]
      exact hbase hvw hv hw

/-- The set of old vertices which conflict with a proposed coloring of a
distinguished core. -/
def conflictSet (G : SimpleGraph V) (S : Set V)
    (coreColor : S → Fin (q + 1))
    (outsideColor : (G.induce Sᶜ).Coloring (Fin q)) : Set V :=
  {x | ∃ hx : x ∈ Sᶜ, ∃ s : S, G.Adj s.1 x ∧
    coreColor s = Fin.castSucc (outsideColor ⟨x, hx⟩)}

/-- Vertices which receive the fresh color in the standard core recoloring:
the fresh-colored vertices of the core, together with all old vertices whose
old color conflicts with an adjacent core vertex. -/
def freshSet (G : SimpleGraph V) (S : Set V)
    (coreColor : S → Fin (q + 1))
    (outsideColor : (G.induce Sᶜ).Coloring (Fin q)) : Set V :=
  {v | ∃ h : v ∈ S, coreColor ⟨v, h⟩ = Fin.last q} ∪
    conflictSet G S coreColor outsideColor

/-- The structural fact used in both final applications.  Outside vertices
attached to different core vertices are anticomplete, and an outside vertex
attached to one core vertex has no other core neighbor.  These two separation
properties make the automatically defined fresh set independent. -/
theorem freshSet_independent_of_separated_attachments
    (G : SimpleGraph V) (q : ℕ) (S : Set V)
    (coreColor : (G.induce S).Coloring (Fin (q + 1)))
    (outsideColor : (G.induce Sᶜ).Coloring (Fin q))
    (hunique : ∀ {r s : S}, r ≠ s → ∀ {x : V}, x ∉ S →
      G.Adj s.1 x → ¬ G.Adj r.1 x)
    (hanti : ∀ {r s : S}, r ≠ s → ∀ {x y : V}, x ∉ S → y ∉ S →
      G.Adj r.1 x → G.Adj s.1 y → ¬ G.Adj x y) :
    G.IsIndepSet (freshSet G S coreColor outsideColor) := by
  classical
  intro v hv w hw hvw hadj
  change
    (∃ hvS : v ∈ S, coreColor ⟨v, hvS⟩ = Fin.last q) ∨
      ∃ hvO : v ∈ Sᶜ, ∃ s : S, G.Adj s.1 v ∧
        coreColor s = Fin.castSucc (outsideColor ⟨v, hvO⟩) at hv
  change
    (∃ hwS : w ∈ S, coreColor ⟨w, hwS⟩ = Fin.last q) ∨
      ∃ hwO : w ∈ Sᶜ, ∃ s : S, G.Adj s.1 w ∧
        coreColor s = Fin.castSucc (outsideColor ⟨w, hwO⟩) at hw
  rcases hv with ⟨hvS, hvc⟩ | ⟨hvO, s, hsv, hsc⟩
  · rcases hw with ⟨hwS, hwc⟩ | ⟨hwO, s, hsw, hsc⟩
    · exact coreColor.valid
        (show (G.induce S).Adj ⟨v, hvS⟩ ⟨w, hwS⟩ from hadj)
        (hvc.trans hwc.symm)
    · let r : S := ⟨v, hvS⟩
      by_cases hrs : r = s
      · subst s
        exact Fin.castSucc_ne_last (outsideColor ⟨w, hwO⟩) (hsc.symm.trans hvc)
      · exact hunique hrs (by simpa using hwO) hsw hadj
  · rcases hw with ⟨hwS, hwc⟩ | ⟨hwO, t, htw, htc⟩
    · let r : S := ⟨w, hwS⟩
      by_cases hrs : r = s
      · subst s
        exact Fin.castSucc_ne_last (outsideColor ⟨v, hvO⟩) (hsc.symm.trans hwc)
      · exact hunique hrs (by simpa using hvO) hsv hadj.symm
    · by_cases hst : s = t
      · subst t
        apply outsideColor.valid
          (show (G.induce Sᶜ).Adj ⟨v, hvO⟩ ⟨w, hwO⟩ from hadj)
        apply Fin.castSucc_injective q
        exact hsc.symm.trans htc
      · exact hanti hst (by simpa using hvO) (by simpa using hwO) hsv htw hadj

/-- The reusable one-fresh-color extension lemma.  In applications `S` is a
maximum clique or a shortest odd cycle.  All graph-specific work is isolated
in proving that `freshSet` is independent. -/
theorem colorable_of_core_and_independent_conflicts
    (G : SimpleGraph V) (q : ℕ) (S : Set V)
    (coreColor : (G.induce S).Coloring (Fin (q + 1)))
    (outsideColor : (G.induce Sᶜ).Coloring (Fin q))
    (hfresh : G.IsIndepSet (freshSet G S coreColor outsideColor)) :
    G.Colorable (q + 1) := by
  classical
  let base : V → Fin (q + 1) := fun v ↦
    if hv : v ∈ S then coreColor ⟨v, hv⟩
    else Fin.castSucc (outsideColor ⟨v, hv⟩)
  apply colorable_add_one_of_recolor_set G q base
    (freshSet G S coreColor outsideColor) hfresh
  · intro v w hvw hv hw
    by_cases hvS : v ∈ S
    · by_cases hwS : w ∈ S
      · simpa only [base, dif_pos hvS, dif_pos hwS] using
          coreColor.valid (show (G.induce S).Adj ⟨v, hvS⟩ ⟨w, hwS⟩ from hvw)
      · simp only [base, dif_pos hvS, dif_neg hwS]
        intro heq
        apply hw
        right
        exact ⟨hwS, ⟨v, hvS⟩, hvw, heq⟩
    · by_cases hwS : w ∈ S
      · simp only [base, dif_neg hvS, dif_pos hwS]
        intro heq
        apply hv
        right
        exact ⟨hvS, ⟨w, hwS⟩, hvw.symm, heq.symm⟩
      · simp only [base, dif_neg hvS, dif_neg hwS]
        intro heq
        exact outsideColor.valid
          (show (G.induce Sᶜ).Adj ⟨v, hvS⟩ ⟨w, hwS⟩ from hvw)
          (Fin.castSucc_injective _ heq)
  · intro v hv
    by_cases hvS : v ∈ S
    · simp only [base, dif_pos hvS]
      intro heq
      apply hv
      left
      exact ⟨hvS, heq⟩
    · simp only [base, dif_neg hvS]
      exact Fin.castSucc_ne_last _

/-- Prototype of the maximum-clique final recoloring.  The clique hypothesis
is retained to match that application; a proper injective palette on the
clique and independence of the resulting conflict set are the exact facts
needed by the recoloring itself. -/
theorem maximumClique_final_recoloring
    (G : SimpleGraph V) (q : ℕ) (K : Set V)
    (_hK : G.IsClique K)
    (cliqueColor : (G.induce K).Coloring (Fin (q + 1)))
    (outsideColor : (G.induce Kᶜ).Coloring (Fin q))
    (hstruct : G.IsIndepSet (freshSet G K cliqueColor outsideColor)) :
    G.Colorable (q + 1) :=
  colorable_of_core_and_independent_conflicts G q K cliqueColor outsideColor hstruct

/-- Maximum-clique recoloring directly from the two structural neighborhood
properties proved in the mathematical argument. -/
theorem maximumClique_final_recoloring_of_separated_attachments
    (G : SimpleGraph V) (q : ℕ) (K : Set V)
    (_hK : G.IsClique K)
    (cliqueColor : (G.induce K).Coloring (Fin (q + 1)))
    (outsideColor : (G.induce Kᶜ).Coloring (Fin q))
    (hunique : ∀ {r s : K}, r ≠ s → ∀ {x : V}, x ∉ K →
      G.Adj s.1 x → ¬ G.Adj r.1 x)
    (hanti : ∀ {r s : K}, r ≠ s → ∀ {x y : V}, x ∉ K → y ∉ K →
      G.Adj r.1 x → G.Adj s.1 y → ¬ G.Adj x y) :
    G.Colorable (q + 1) :=
  colorable_of_core_and_independent_conflicts G q K cliqueColor outsideColor
    (freshSet_independent_of_separated_attachments G q K cliqueColor outsideColor
      hunique hanti)

/-- Give a finite core pairwise distinct colors whenever it fits in the
target palette.  This is the coloring used on a maximum clique. -/
noncomputable def injectiveCoreColor
    (G : SimpleGraph V) (q : ℕ) (K : Finset V) (hcard : K.card ≤ q + 1) :
    (G.induce (↑K : Set V)).Coloring (Fin (q + 1)) := by
  let e : (↑K : Set V) ↪ Fin (q + 1) := Classical.choice
    (Function.Embedding.nonempty_of_card_le (by simpa using hcard))
  exact SimpleGraph.Coloring.mk e fun {v w} hadj heq ↦
    hadj.ne (e.injective heq)

/-- Fully packaged maximum-clique prototype: the clique's cardinality bound
constructs its injective palette, and the two neighborhood-separation facts
then feed the common fresh-color lemma. -/
theorem maximumClique_final_recoloring_of_card_le
    (G : SimpleGraph V) (q : ℕ) (K : Finset V)
    (_hK : G.IsClique (↑K : Set V)) (hcard : K.card ≤ q + 1)
    (outsideColor : (G.induce ((↑K : Set V)ᶜ)).Coloring (Fin q))
    (hunique : ∀ {r s : (↑K : Set V)}, r ≠ s → ∀ {x : V}, x ∉ K →
      G.Adj s.1 x → ¬ G.Adj r.1 x)
    (hanti : ∀ {r s : (↑K : Set V)}, r ≠ s → ∀ {x y : V}, x ∉ K → y ∉ K →
      G.Adj r.1 x → G.Adj s.1 y → ¬ G.Adj x y) :
    G.Colorable (q + 1) :=
  maximumClique_final_recoloring_of_separated_attachments G q (↑K : Set V) _hK
    (injectiveCoreColor G q K hcard) outsideColor
    hunique hanti

/-- Prototype of the shortest-cycle final recoloring.  Here `C` is the
shortest-cycle vertex set and `cycleColor` is its displayed three-coloring,
embedded in the target palette.  Chordlessness, unique attachment, and
anticompleteness of attachment sets are used upstream precisely to prove
`hstruct`. -/
theorem shortestCycle_final_recoloring
    (G : SimpleGraph V) (q : ℕ) (C : Set V)
    (cycleColor : (G.induce C).Coloring (Fin (q + 1)))
    (outsideColor : (G.induce Cᶜ).Coloring (Fin q))
    (hstruct : G.IsIndepSet (freshSet G C cycleColor outsideColor)) :
    G.Colorable (q + 1) :=
  colorable_of_core_and_independent_conflicts G q C cycleColor outsideColor hstruct

/-- Shortest-cycle recoloring directly from unique attachment to the cycle
and anticompleteness of different attachment sets. -/
theorem shortestCycle_final_recoloring_of_separated_attachments
    (G : SimpleGraph V) (q : ℕ) (C : Set V)
    (cycleColor : (G.induce C).Coloring (Fin (q + 1)))
    (outsideColor : (G.induce Cᶜ).Coloring (Fin q))
    (hunique : ∀ {r s : C}, r ≠ s → ∀ {x : V}, x ∉ C →
      G.Adj s.1 x → ¬ G.Adj r.1 x)
    (hanti : ∀ {r s : C}, r ≠ s → ∀ {x y : V}, x ∉ C → y ∉ C →
      G.Adj r.1 x → G.Adj s.1 y → ¬ G.Adj x y) :
    G.Colorable (q + 1) :=
  colorable_of_core_and_independent_conflicts G q C cycleColor outsideColor
    (freshSet_independent_of_separated_attachments G q C cycleColor outsideColor
      hunique hanti)

/-- Pull the standard tricoloring of a cycle across a graph isomorphism and
embed its three colors in the target palette. -/
noncomputable def cycleCoreColor
    (G : SimpleGraph V) (q n : ℕ) (C : Set V) (hn : 2 ≤ n) (hq : 2 ≤ q)
    (e : G.induce C ≃g SimpleGraph.cycleGraph n) :
    (G.induce C).Coloring (Fin (q + 1)) :=
  (G.induce C).recolorOfCardLE (by simp; omega)
    ((SimpleGraph.cycleGraph.tricoloring n hn).comap e.toHom)

/-- Fully packaged shortest-cycle prototype.  An isomorphism identifies the
induced core with a cycle; the standard three-coloring and the two attachment
separation facts yield the final coloring. -/
theorem shortestCycle_final_recoloring_of_iso
    (G : SimpleGraph V) (q n : ℕ) (C : Set V) (hn : 2 ≤ n) (hq : 2 ≤ q)
    (e : G.induce C ≃g SimpleGraph.cycleGraph n)
    (outsideColor : (G.induce Cᶜ).Coloring (Fin q))
    (hunique : ∀ {r s : C}, r ≠ s → ∀ {x : V}, x ∉ C →
      G.Adj s.1 x → ¬ G.Adj r.1 x)
    (hanti : ∀ {r s : C}, r ≠ s → ∀ {x y : V}, x ∉ C → y ∉ C →
      G.Adj r.1 x → G.Adj s.1 y → ¬ G.Adj x y) :
    G.Colorable (q + 1) :=
  shortestCycle_final_recoloring_of_separated_attachments G q C
    (cycleCoreColor G q n C hn hq e) outsideColor hunique hanti

end Erdos922Recolor


namespace Erdos922Assembly

open SimpleGraph
open scoped ENat

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem exists_shorter_cycle_of_chord [DecidableEq V]
    {v : V} {c : G.Walk v v} (hc : c.IsCycle)
    {x y : V} (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hxy : G.Adj x y) (hnot : ¬ c.toSubgraph.Adj x y) :
    ∃ a : V, ∃ c' : G.Walk a a, c'.IsCycle ∧ c'.length < c.length := by
  let r := c.rotate x hx
  have hr_cycle : r.IsCycle := hc.rotate hx
  have hlen_rot : r.length = c.length := by
    have hlen1 :
        (c.takeUntil x hx).length + (c.dropUntil x hx).length = c.length := by
      have hlen1' := congrArg SimpleGraph.Walk.length
        (SimpleGraph.Walk.take_spec c hx)
      rw [SimpleGraph.Walk.length_append] at hlen1'
      exact hlen1'
    calc
      r.length = (c.dropUntil x hx).length + (c.takeUntil x hx).length := by
        simp [r, SimpleGraph.Walk.rotate, SimpleGraph.Walk.length_append]
      _ = (c.takeUntil x hx).length + (c.dropUntil x hx).length := by omega
      _ = c.length := hlen1
  have hy' : y ∈ r.support := by
    have hyv : y ∈ c.toSubgraph.verts := by
      simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using hy
    have : y ∈ r.toSubgraph.verts := by
      simpa [r, SimpleGraph.Walk.toSubgraph_rotate] using hyv
    simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using this
  let p := r.takeUntil y hy'
  have hp_path : p.IsPath := hr_cycle.isPath_takeUntil hy'
  have hnot_adj_r : ¬ r.toSubgraph.Adj x y := by
    simpa [r, SimpleGraph.Walk.toSubgraph_rotate] using hnot
  have hnot_edge_r : s(x, y) ∉ r.edges := by
    intro hmem
    have : r.toSubgraph.Adj x y := by
      have : s(x, y) ∈ r.toSubgraph.edgeSet :=
        (r.mem_edges_toSubgraph).2 hmem
      exact (SimpleGraph.Subgraph.mem_edgeSet
        (G' := r.toSubgraph) (v := x) (w := y)).1 this
    exact hnot_adj_r this
  have hnot_edge_p : s(x, y) ∉ p.edges := by
    intro hmem
    exact hnot_edge_r ((r.edges_takeUntil_subset_edges hy') hmem)
  have hp_len_lt : p.length < r.length := by
    exact r.length_takeUntil_lt_length hy' (G.ne_of_adj hxy).symm
  have hlen_ne : p.length + 1 ≠ r.length := by
    intro hlen
    have hlen' : p.length = r.length - 1 := by omega
    have hget : r.getVert p.length = y := by
      have hpl : p.getVert p.length = y := by simp
      have hpr : p.getVert p.length = r.getVert p.length := by
        dsimp [p]
        exact r.getVert_takeUntil hy' (by rfl)
      exact hpr.symm.trans hpl
    have hpend : r.penultimate = y := by
      simpa [SimpleGraph.Walk.penultimate, hlen'] using hget
    have hadj_pen : r.toSubgraph.Adj r.penultimate x :=
      r.toSubgraph_adj_penultimate hr_cycle.not_nil
    have : r.toSubgraph.Adj x y := by
      have hsymm : r.toSubgraph.Adj x r.penultimate := hadj_pen.symm
      simpa [hpend] using hsymm
    exact hnot_adj_r this
  have hlen_short : p.length + 1 < r.length := by omega
  have hcyc' : (SimpleGraph.Walk.cons hxy.symm p).IsCycle := by
    have hnot_edge_p' : s(y, x) ∉ p.edges := by
      simpa [Sym2.eq_swap] using hnot_edge_p
    let pp : SimpleGraph.Path (G := G) x y := ⟨p, hp_path⟩
    exact SimpleGraph.Path.cons_isCycle (p := pp) (h := hxy.symm) hnot_edge_p'
  refine ⟨y, SimpleGraph.Walk.cons hxy.symm p, hcyc', ?_⟩
  simpa [SimpleGraph.Walk.length_cons, hlen_rot] using hlen_short

/-- A cycle attaining the girth has no chord. -/
theorem isChordless_of_isCycle_length_eq_girth [DecidableEq V]
    {v : V} {w : G.Walk v v} (hw : w.IsCycle)
    (hlen : w.length = G.girth) : w.IsChordless := by
  rw [SimpleGraph.Walk.isChordless_iff_forall_mem_edges]
  intro x y hx hy hxy
  by_contra hedge
  have hnot : ¬ w.toSubgraph.Adj x y := by
    simpa only [SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges] using hedge
  obtain ⟨a, w', hw', hshort⟩ :=
    exists_shorter_cycle_of_chord hw hx hy hxy hnot
  have hle := SimpleGraph.girth_le_length (G := G) hw'
  omega

theorem fOn_le_of_large_independent_sets
    {V : Type u} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (hG : Erdos922.HasLargeIndependentSets G k) :
    Erdos922FullB.fOn G Finset.univ ≤ (k : ℤ) := by
  classical
  obtain ⟨S, -, hSf⟩ :=
    Erdos922FullB.exists_maximum_potential_on G (Finset.univ : Finset V)
  rw [← hSf]
  obtain ⟨I, hIS, hI, hcard⟩ := hG.onFinsets S
  have hIa : I.card ≤ Erdos922FullB.alphaOn G S :=
    Erdos922FullB.card_le_alphaOn hIS hI
  simp only [Erdos922FullB.potential]
  omega

theorem erdos_922_of_noOrderMinimalCounterexample
    {V : Type u} [Fintype V] [DecidableEq V]
    (hNo : Erdos922FullB.NoOrderMinimalCounterexample.{u})
    (G : SimpleGraph V) (k : ℕ)
    (hG : Erdos922.HasLargeIndependentSets G k) :
    G.chromaticNumber ≤ ((k + 2 : ℕ) : ℕ∞) := by
  have hfolk : Erdos922FullB.FolkmanBound G :=
    Erdos922FullB.folkmanBound_of_noOrderMinimalCounterexample hNo G
  have hf : Erdos922FullB.fOn G Finset.univ ≤ (k : ℤ) :=
    fOn_le_of_large_independent_sets hG
  have hnonneg := Erdos922FullB.fOn_nonneg G (Finset.univ : Finset V)
  have hnat : Int.toNat (Erdos922FullB.fOn G Finset.univ) ≤ k := by omega
  rw [SimpleGraph.chromaticNumber_le_iff_colorable]
  exact SimpleGraph.Colorable.mono (Nat.add_le_add_right hnat 2) hfolk

end Erdos922Assembly

namespace Erdos922Assembly

open SimpleGraph

universe u

/-- On a nonempty clique, the largest independent subset has exactly one
vertex.  This tiny estimate is the numerical input used at the maximum
clique in the final recoloring argument. -/
theorem alphaOn_eq_one_of_nonempty_clique
    {V : Type u} [DecidableEq V] {G : SimpleGraph V} {K : Finset V}
    (hK : G.IsClique (K : Set V)) (hKne : K.Nonempty) :
    Erdos922FullB.alphaOn G K = 1 := by
  apply Nat.le_antisymm
  · obtain ⟨I, hIK, hI, hIcard⟩ :=
      Erdos922FullB.exists_maximum_independent_subset G K
    rw [← hIcard]
    apply Finset.card_le_one.mpr
    intro a ha b hb
    by_contra hab
    exact hI ha hb hab (hK (hIK ha) (hIK hb) hab)
  · obtain ⟨v, hv⟩ := hKne
    have hsind : G.IsIndepSet ({v} : Finset V) := by simp
    simpa using Erdos922FullB.card_le_alphaOn
      (G := G) (I := ({v} : Finset V)) (S := K)
      (by simpa using hv) hsind

/-- The two bipartition classes of an induced four-cycle satisfy the exact
abstract configuration consumed by the even-hole contraction argument. -/
theorem evenHoleConfiguration_of_inducedFourCycle
    {V : Type u} [DecidableEq V] {G : SimpleGraph V} {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hAB : G.Adj a b) (hBC : G.Adj b c)
    (hCD : G.Adj c d) (hDA : G.Adj d a)
    (hAC : ¬ G.Adj a c) (hBD : ¬ G.Adj b d) :
    Erdos922.EvenHole.Configuration G ({a, c} : Finset V)
      ({b, d} : Finset V) 2 := by
  classical
  refine ⟨?_, by omega, by simp [hac], by simp [hbd], ?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro x hxA hxB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxA hxB
    rcases hxA with rfl | rfl <;> rcases hxB with rfl | rfl <;> contradiction
  · intro x hx y hy hxy
    change x ∈ ({a, c} : Finset V) at hx
    change y ∈ ({a, c} : Finset V) at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    all_goals first | exact (hxy rfl).elim | exact hAC | exact fun h ↦ hAC h.symm
  · intro x hx y hy hxy
    change x ∈ ({b, d} : Finset V) at hx
    change y ∈ ({b, d} : Finset V) at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    all_goals first | exact (hxy rfl).elim | exact hBD | exact fun h ↦ hBD h.symm
  · intro I hsub hI
    by_contra hnot
    have hlt : 2 < I.card := by omega
    obtain ⟨x, y, z, hxI, hyI, hzI, hxy, hxz, hyz⟩ :=
      Finset.two_lt_card_iff.mp hlt
    have hnxy : ¬ G.Adj x y := hI hxI hyI hxy
    have hnxz : ¬ G.Adj x z := hI hxI hzI hxz
    have hnyz : ¬ G.Adj y z := hI hyI hzI hyz
    have hnyx : ¬ G.Adj y x := fun h ↦ hnxy h.symm
    have hnzx : ¬ G.Adj z x := fun h ↦ hnxz h.symm
    have hnzy : ¬ G.Adj z y := fun h ↦ hnyz h.symm
    have hxC := hsub hxI
    have hyC := hsub hyI
    have hzC := hsub hzI
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hxC hyC hzC
    rcases hxC with (rfl | rfl) | (rfl | rfl) <;>
      rcases hyC with (rfl | rfl) | (rfl | rfl) <;>
      rcases hzC with (rfl | rfl) | (rfl | rfl)
    all_goals simp_all
  · intro I hsub hI hcard
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
    have hxC := hsub (Finset.mem_insert_self x {y})
    have hyMem : y ∈ ({x, y} : Finset V) := by simp
    have hyC := hsub hyMem
    have hnxy : ¬ G.Adj x y := hI (by simp) (by simp) hxy
    have hnyx : ¬ G.Adj y x := fun h ↦ hnxy h.symm
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hxC hyC
    rcases hxC with (rfl | rfl) | (rfl | rfl) <;>
      rcases hyC with (rfl | rfl) | (rfl | rfl)
    all_goals simp_all [Finset.pair_comm]

/-- The abstract even-hole exclusion specializes to the local induced-C4
predicate used by the maximum-clique recoloring. -/
theorem noInducedFourCycle_of_orderMinimal
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hmin : Erdos922FullB.IsOrderMinimalCounterexample G) :
    Erdos922Recolor.NoInducedFourCycle G := by
  intro a b c d hab hac had hbc hbd hcd hAB hBC hCD hDA hAC hBD
  apply Erdos922.EvenHole.no_configuration_of_orderMinimalCounterexample G hmin
  exact ⟨{a, c}, {b, d}, 2,
    evenHoleConfiguration_of_inducedFourCycle hab hac had hbc hbd hcd
      hAB hBC hCD hDA hAC hBD⟩

/-- Common-neighbor cliquehood is exactly the local no-induced-diamond
predicate used by the recoloring layer. -/
theorem noInducedDiamond_of_orderMinimal
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hmin : Erdos922FullB.IsOrderMinimalCounterexample G) :
    Erdos922Recolor.NoInducedDiamond G := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  intro a b c d hab hac had hbc hbd hcd hAB hAC hBC hAD hBD hCD
  have hclique := Erdos922Diamond.commonNeighbors_isClique_of_orderMinimalCounterexample
    hmin a b hAB
  exact hCD (hclique ⟨hAC, hBC⟩ ⟨hAD, hBD⟩ hcd)

/-- The maximum-clique recoloring rules out a triangle in an order-minimal
counterexample once diamonds and induced four-cycles have been excluded. -/
theorem triangle_free_of_orderMinimal
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hmin : Erdos922FullB.IsOrderMinimalCounterexample G)
    (hdiamond : Erdos922Recolor.NoInducedDiamond G)
    (hfour : Erdos922Recolor.NoInducedFourCycle G) :
    G.CliqueFree 3 := by
  classical
  intro T hT
  obtain ⟨K, hK⟩ := G.maximumClique_exists
  have hKcard : 3 ≤ K.card := by
    have hle := hK.maximum T hT.isClique
    simpa [hT.card_eq] using hle
  have hKne : K.Nonempty := Finset.card_pos.mp (by omega)
  have hKalpha : Erdos922FullB.alphaOn G K = 1 :=
    alphaOn_eq_one_of_nonempty_clique hK.isClique hKne
  have hKpot : Erdos922FullB.potential G K = (K.card : ℤ) - 2 := by
    simp [Erdos922FullB.potential, hKalpha]
  have hKf : (K.card : ℤ) - 2 ≤
      Erdos922FullB.fOn G (Finset.univ : Finset V) := by
    rw [← hKpot]
    exact Erdos922FullB.potential_le_fOn G (Finset.subset_univ K)
  have hgap := Erdos922FullB.counterexample_gap_int G hmin.counterexample
  have hKltchi : K.card < Erdos922FullB.chiNat G := by omega
  have hKnotuniv : K ≠ (Finset.univ : Finset V) := by
    intro hKuniv
    have hc : G.Colorable K.card := by
      simpa [hKuniv] using G.colorable_of_fintype
    have hchi : Erdos922FullB.chiNat G ≤ K.card :=
      (Erdos922FullB.colorable_iff_chiNat_le G K.card).mp hc
    omega
  let q : ℕ := Erdos922FullB.chiNat G - 2
  have hq : q + 1 = Erdos922FullB.chiNat G - 1 := by
    dsimp only [q]
    omega
  have hKfit : K.card ≤ q + 1 := by
    rw [hq]
    omega
  have hsplit := hmin.critical_split K hKne hKnotuniv
  have hKchi : K.card ≤
      Erdos922FullB.chiNat (G.induce (K : Set V)) := by
    let KU : Finset (K : Set V) := Finset.univ
    have hKU : (G.induce (K : Set V)).IsClique (KU : Set (K : Set V)) := by
      intro a _ha b _hb hab
      exact hK.isClique a.2 b.2 (fun e ↦ hab (Subtype.ext e))
    have hc := hKU.card_le_of_colorable
      (Erdos922FullB.colorable_chiNat (G.induce (K : Set V)))
    simpa [KU] using hc
  have houtchi : Erdos922FullB.chiNat
      (G.induce ((K : Set V)ᶜ)) ≤ q := by
    rw [show ((↑(Kᶜ) : Set V)) = ((K : Set V)ᶜ) by ext v; simp] at hsplit
    dsimp only [q]
    omega
  obtain ⟨outsideColor⟩ : (G.induce ((K : Set V)ᶜ)).Colorable q :=
    (Erdos922FullB.colorable_iff_chiNat_le _ q).mpr houtchi
  have hcolor : G.Colorable (q + 1) :=
    Erdos922Recolor.maximumClique_final_recoloring_of_card_le G q K
      hK.isClique hKfit outsideColor
      (Erdos922Recolor.maximalClique_attachment_unique G
        (hK.isMaximalClique K) hdiamond)
      (Erdos922Recolor.maximalClique_attachments_anticomplete G
        (hK.isMaximalClique K) hdiamond hfour)
  have hchi : Erdos922FullB.chiNat G ≤ q + 1 :=
    (Erdos922FullB.colorable_iff_chiNat_le G (q + 1)).mp hcolor
  rw [hq] at hchi
  omega

/-- With the four-cycle part discharged by the even-hole contraction, only
the diamond exclusion is needed to obtain triangle-freeness. -/
theorem triangle_free_of_orderMinimal_of_noInducedDiamond
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hmin : Erdos922FullB.IsOrderMinimalCounterexample G)
    (hdiamond : Erdos922Recolor.NoInducedDiamond G) :
    G.CliqueFree 3 :=
  triangle_free_of_orderMinimal G hmin hdiamond
    (noInducedFourCycle_of_orderMinimal G hmin)

/-- Every order-minimal counterexample is triangle-free. -/
theorem triangle_free_of_orderMinimalCounterexample
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hmin : Erdos922FullB.IsOrderMinimalCounterexample G) :
    G.CliqueFree 3 :=
  triangle_free_of_orderMinimal G hmin
    (noInducedDiamond_of_orderMinimal G hmin)
    (noInducedFourCycle_of_orderMinimal G hmin)

/-- The structural heart of Folkman's argument: a counterexample minimal in
vertex order cannot exist. -/
theorem not_orderMinimalCounterexample
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    ¬ Erdos922FullB.IsOrderMinimalCounterexample G := by
  classical
  intro hmin
  obtain ⟨v, w, hw, hlen⟩ := hmin.exists_shortest_cycle
  have hchord : w.IsChordless :=
    isChordless_of_isCycle_length_eq_girth hw hlen
  have hnoConfig : ¬ ∃ (A B : Finset V) (p : ℕ),
      Erdos922.EvenHole.Configuration G A B p :=
    Erdos922.EvenHole.no_configuration_of_orderMinimalCounterexample G hmin
  have hnoEven : Erdos922Recolor.NoInducedEvenCycleIso G :=
    Erdos922Recolor.EvenCycleBridge.no_induced_even_cycle_iso_of_no_configuration
      G hnoConfig
  have hnNotEven : ¬ Even w.length :=
    Erdos922Recolor.not_even_length_of_chordless_cycle G hnoEven w hw hchord
  have hnOdd : Odd w.length := Nat.not_even_iff_odd.mp hnNotEven
  have hn3 : w.length ≠ 3 := by
    intro hw3
    have hex : ∃ T, G.IsNClique 3 T :=
      SimpleGraph.is3Clique_iff_exists_cycle_length_three.mpr
        ⟨v, w, hw, hw3⟩
    obtain ⟨T, hT⟩ := hex
    exact triangle_free_of_orderMinimalCounterexample G hmin T hT
  have hn5 : 5 ≤ w.length := by
    obtain ⟨m, hm⟩ := hnOdd
    have := hw.three_le_length
    omega
  have hshort : Erdos922Recolor.IsShortestCycleLength G w.length := by
    intro z c hc
    rw [hlen]
    exact SimpleGraph.girth_le_length (G := G) hc
  obtain ⟨C, ⟨e⟩⟩ :=
    Erdos922Recolor.inducedCycleIso_of_chordless_cycle w hw hchord
  let X : Finset V := Finset.univ.filter fun x ↦ x ∈ C
  have hXset : (X : Set V) = C := by
    ext x
    simp [X]
  have hXnonempty : X.Nonempty := by
    let i : Fin w.length := ⟨0, by omega⟩
    let x : C := e.symm i
    refine ⟨x.1, ?_⟩
    simp [X, x.2]
  have hcoreChromatic : (G.induce C).chromaticNumber = 3 := by
    rw [SimpleGraph.chromaticNumber_congr e,
      SimpleGraph.chromaticNumber_cycleGraph_of_odd w.length (by omega) hnOdd]
  have hcoreChi : Erdos922FullB.chiNat (G.induce C) = 3 := by
    unfold Erdos922FullB.chiNat
    rw [hcoreChromatic]
    simp
  have hXproper : X ≠ (Finset.univ : Finset V) := by
    intro hXu
    have hCuniv : C = Set.univ := by
      rw [← hXset]
      ext x
      simp [hXu]
    have hinduceChi : Erdos922FullB.chiNat (G.induce Set.univ) =
        Erdos922FullB.chiNat G := by
      unfold Erdos922FullB.chiNat
      rw [SimpleGraph.chromaticNumber_congr (SimpleGraph.induceUnivIso G)]
    rw [hCuniv, hinduceChi] at hcoreChi
    have hfour := hmin.four_le_chiNat
    omega
  have hsplit := hmin.critical_split X hXnonempty hXproper
  rw [show ((↑(Xᶜ) : Set V)) = ((X : Set V)ᶜ) by ext x; simp] at hsplit
  rw [hXset] at hsplit
  let q : ℕ := Erdos922FullB.chiNat G - 2
  have hq : 2 ≤ q := by
    dsimp only [q]
    have hfour := hmin.four_le_chiNat
    omega
  have houtChi : Erdos922FullB.chiNat (G.induce Cᶜ) ≤ q := by
    dsimp only [q]
    omega
  obtain ⟨outsideColor⟩ : (G.induce Cᶜ).Colorable q :=
    (Erdos922FullB.colorable_iff_chiNat_le _ q).mpr houtChi
  have hunique : ∀ {r s : C}, r ≠ s → ∀ {x : V}, x ∉ C →
      G.Adj s.1 x → ¬ G.Adj r.1 x :=
    Erdos922Recolor.shortestCycle_attachment_unique G hn5 e hshort
  have hanti : ∀ {r s : C}, r ≠ s → ∀ {x y : V}, x ∉ C → y ∉ C →
      G.Adj r.1 x → G.Adj s.1 y → ¬ G.Adj x y :=
    Erdos922Recolor.shortestOddCycle_attachments_anticomplete
      G hn5 hnOdd e hshort hnoEven hunique
  have hcolor : G.Colorable (q + 1) :=
    Erdos922Recolor.shortestCycle_final_recoloring_of_iso
      G q w.length C (by omega) hq e outsideColor hunique hanti
  have hchi : Erdos922FullB.chiNat G ≤ q + 1 :=
    (Erdos922FullB.colorable_iff_chiNat_le G (q + 1)).mp hcolor
  dsimp only [q] at hchi
  have hfour := hmin.four_le_chiNat
  omega

/-- There is no order-minimal counterexample. -/
theorem noOrderMinimalCounterexample :
    Erdos922FullB.NoOrderMinimalCounterexample.{u} := by
  intro V _ _ G
  exact not_orderMinimalCounterexample G

end Erdos922Assembly

namespace Erdos922

universe u

/-- Erdős Problem 922 (Folkman's theorem): the hereditary independent-set
hypothesis forces chromatic number at most `k + 2`. -/
theorem erdos_922 {V : Type u} [Finite V] (G : SimpleGraph V) (k : ℕ)
    (hG : HasLargeIndependentSets G k) :
    G.chromaticNumber ≤ ((k + 2 : ℕ) : ℕ∞) := by
  classical
  letI := Fintype.ofFinite V
  exact Erdos922Assembly.erdos_922_of_noOrderMinimalCounterexample
    Erdos922Assembly.noOrderMinimalCounterexample G k hG

end Erdos922

#print axioms Erdos922.erdos_922
