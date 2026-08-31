/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 737.
https://www.erdosproblems.com/forum/thread/737

Informal authors:
- Carsten Thomassen

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos737.md
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos594
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Erdős Problem 737

Every graph of chromatic number `ℵ₁` has one edge that belongs to a cycle of
every sufficiently large finite length.  The mathematical proof and a detailed
Leanization plan are in `tex/737.tex`.
-/

open Function Set SimpleGraph
open scoped Ordinal Sym2

namespace Erdos737

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u}

/-- Exact chromatic number `ℵ₁`: there is an `ω₁`-coloring but no countable
coloring.  The theorem below proves a stronger result and uses only the second
conjunct. -/
def ChromaticNumberAlephOne (G : SimpleGraph V) : Prop :=
  Nonempty (G.Coloring (Set.Iio (Ordinal.omega.{0} 1))) ∧ IsEmpty (G.Coloring ℕ)

lemma ChromaticNumberAlephOne.isUncountablyChromatic {G : SimpleGraph V}
    (hG : ChromaticNumberAlephOne G) : Erdos594.IsUncountablyChromatic G :=
  hG.2

/-- A spanning forest together with its canonical two-coloring. -/
structure SpanningForestData (G : SimpleGraph V) where
  forest : SimpleGraph V
  forest_le : forest ≤ G
  acyclic : forest.IsAcyclic
  reachable_eq : forest.Reachable = G.Reachable

/-- Every graph admits a spanning forest. -/
noncomputable def spanningForestData (G : SimpleGraph V) : SpanningForestData G := by
  classical
  let F : SimpleGraph V := Classical.choose G.exists_isAcyclic_reachable_eq_le
  have hF := Classical.choose_spec G.exists_isAcyclic_reachable_eq_le
  exact ⟨F, hF.1, hF.2.1, hF.2.2⟩

/-- The canonical two-coloring of the selected spanning forest, transported
from `Fin 2` to `Bool` so that Mathlib's walk-parity lemma applies directly. -/
noncomputable def forestColoring (G : SimpleGraph V) :
    (spanningForestData G).forest.Coloring Bool :=
  (spanningForestData G).forest.recolorOfEquiv finTwoEquiv
    (spanningForestData G).acyclic.coloringTwo

noncomputable def forestColor (G : SimpleGraph V) : V → Bool :=
  forestColoring G

/-- Edges whose endpoints have the same color in a selected spanning forest.
Such an edge has an even alternate path in the forest. -/
def evenPathCore (G : SimpleGraph V) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ forestColor G v = forestColor G w
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h ↦ h.1.ne rfl⟩

lemma evenPathCore_le (G : SimpleGraph V) : evenPathCore G ≤ G :=
  fun _ _ h ↦ h.1

/-- Combining a countable coloring of the same-forest-color edges with the
forest two-coloring gives a countable coloring of the original graph. -/
lemma nonempty_coloring_of_evenPathCore
    (G : SimpleGraph V) (h : Nonempty ((evenPathCore G).Coloring ℕ)) :
    Nonempty (G.Coloring ℕ) := by
  classical
  let c : (evenPathCore G).Coloring ℕ := Classical.choice h
  let d : V → Bool := forestColor G
  let color : V → ℕ := fun v ↦ Nat.pairEquiv (c v, Bool.toNat (d v))
  refine ⟨SimpleGraph.Coloring.mk color ?_⟩
  intro v w hvw heq
  have hp := Nat.pairEquiv.injective heq
  by_cases hd : d v = d w
  · exact c.valid ⟨hvw, hd⟩ (congrArg Prod.fst hp)
  · apply hd
    have hnat := congrArg Prod.snd hp
    cases hv : d v <;> cases hw : d w <;> simp_all [Bool.toNat]

/-- The same-forest-color edge graph remains uncountably chromatic. -/
lemma isUncountablyChromatic_evenPathCore {G : SimpleGraph V}
    (hG : Erdos594.IsUncountablyChromatic G) :
    Erdos594.IsUncountablyChromatic (evenPathCore G) := by
  rw [Erdos594.isUncountablyChromatic_iff_not_nonempty] at hG ⊢
  exact fun h ↦ hG (nonempty_coloring_of_evenPathCore G h)

/-- An even simple path between the endpoints that avoids their edge. -/
def HasEvenAlternatePath (G : SimpleGraph V) (u v : V) : Prop :=
  ∃ p : G.Walk u v, p.IsPath ∧ Even p.length ∧ s(u, v) ∉ p.edges

/-- Every edge of `evenPathCore G` has an even alternate path in `G`, supplied
by the selected spanning forest. -/
lemma hasEvenAlternatePath_of_evenPathCore {G : SimpleGraph V} {u v : V}
    (h : (evenPathCore G).Adj u v) : HasEvenAlternatePath G u v := by
  classical
  let D := spanningForestData G
  let F := D.forest
  let c : F.Coloring Bool := forestColoring G
  have hGreach : G.Reachable u v := h.1.reachable
  have hFreach : F.Reachable u v := by
    rw [D.reachable_eq]
    exact hGreach
  obtain ⟨p, hp, _⟩ := hFreach.exists_path_of_dist
  let f : F →g G := Hom.ofLE D.forest_le
  have hcolor : c u = c v := by
    simpa [c, forestColor, F, D] using h.2
  refine ⟨p.map f, hp.map Function.injective_id, ?_, ?_⟩
  · simpa [f] using (c.even_length_iff_congr p).mpr (by simp [hcolor])
  · intro he
    have heF : s(u, v) ∈ p.edges := by
      simpa [f] using he
    exact c.valid (p.adj_of_mem_edges heF) hcolor

/-! ## The universal countable half graph -/

/-- Vertex labels for the countable half graph used by Hajnal--Komjáth. -/
inductive HalfVertex where
  | center
  | left (i : ℕ)
  | right (i : ℕ)
  deriving DecidableEq

/-- A concrete copy of the countable half graph: the center is adjacent to
every left vertex, and right vertex `i` is adjacent to left vertex `j` for
every `j < i`.  The embedding field makes all named vertices distinct. -/
structure HalfGraphCopy (G : SimpleGraph V) where
  vertex : HalfVertex ↪ V
  adj_center_left : ∀ i, G.Adj (vertex .center) (vertex (.left i))
  adj_right_left : ∀ {i j}, j < i → G.Adj (vertex (.right i)) (vertex (.left j))

/-- The optional singleton containing a chosen vertex outside `t` adjacent to
every vertex of `s`. -/
def witnessSet (G : SimpleGraph V) (s t : Finset V) : Set V :=
  if h : ∃ v : V, v ∉ t ∧ ∀ x ∈ s, G.Adj x v then
    {Classical.choose h}
  else ∅

lemma mem_witnessSet_iff {G : SimpleGraph V} {s t : Finset V} {v : V} :
    v ∈ witnessSet G s t ↔
      ∃ h : ∃ z : V, z ∉ t ∧ ∀ x ∈ s, G.Adj x z, v = Classical.choose h := by
  simp only [witnessSet]
  split_ifs with h
  · simp [h]
  · simp [h]

lemma witnessSet_spec {G : SimpleGraph V} {s t : Finset V}
    (h : ∃ v : V, v ∉ t ∧ ∀ x ∈ s, G.Adj x v) :
    ∃ z ∈ witnessSet G s t, z ∉ t ∧ ∀ x ∈ s, G.Adj x z := by
  refine ⟨Classical.choose h, ?_, (Classical.choose_spec h).1,
    (Classical.choose_spec h).2⟩
  simp [witnessSet, h]

lemma witnessSet_subsingleton (G : SimpleGraph V) (s t : Finset V) :
    (witnessSet G s t).Subsingleton := by
  simp only [witnessSet]
  split_ifs <;> simp

/-- One closure step: adjoin a selected common neighbor for every pair of
finite sets already supported in `A`, with the second finite set serving as a
finite avoidance set. -/
def witnessStep (G : SimpleGraph V) (A : Set V) : Set V :=
  A ∪ {v | ∃ s t : Finset V, s.Nonempty ∧
    (s : Set V) ⊆ A ∧ (t : Set V) ⊆ A ∧
    v ∈ witnessSet G s t}

lemma subset_witnessStep (G : SimpleGraph V) (A : Set V) :
    A ⊆ witnessStep G A :=
  subset_union_left

lemma witnessStep_mono (G : SimpleGraph V) : Monotone (witnessStep G) := by
  intro A B hAB v hv
  rcases hv with hv | ⟨s, t, hne, hs, ht, hv⟩
  · exact Or.inl (hAB hv)
  · exact Or.inr ⟨s, t, hne, hs.trans hAB, ht.trans hAB, hv⟩

/-- Finsets over a type have cardinal at most the maximum of the type's
cardinality and `ℵ₀`. -/
lemma mk_finset_le_max (A : Type u) :
    Cardinal.mk (Finset A) ≤ max (Cardinal.mk A) Cardinal.aleph0 := by
  cases finite_or_infinite A with
  | inl hfin =>
      let _ := hfin
      exact (Cardinal.lt_aleph0_iff_finite.mpr inferInstance).le.trans (le_max_right _ _)
  | inr hinf =>
      let _ := hinf
      rw [Cardinal.mk_finset_of_infinite]
      exact le_max_left _ _

/-- Forget the subtype proof in a finite set over `A`. -/
def liftFinset (A : Set V) (s : Finset A) : Finset V :=
  s.map (Function.Embedding.subtype _)

@[simp]
lemma mem_liftFinset {A : Set V} {s : Finset A} {v : V} :
    v ∈ liftFinset A s ↔ ∃ h : v ∈ A, (⟨v, h⟩ : A) ∈ s := by
  simp [liftFinset]

/-- Regard a finite set contained in `A` as a finite set of the subtype `A`. -/
def restrictFinset (A : Set V) (s : Finset V) (hs : (s : Set V) ⊆ A) : Finset A :=
  s.attach.map
    { toFun := fun x : {v // v ∈ s} ↦ ⟨x.1, hs x.2⟩
      inj' := by
        intro x y h
        apply Subtype.ext
        exact congrArg (fun z : A ↦ (z : V)) h }

lemma liftFinset_restrictFinset (A : Set V) (s : Finset V)
    (hs : (s : Set V) ⊆ A) :
    liftFinset A (restrictFinset A s hs) = s := by
  ext v
  rw [mem_liftFinset]
  constructor
  · rintro ⟨hvA, hv⟩
    rw [restrictFinset, Finset.mem_map] at hv
    obtain ⟨x, hx, hxeq⟩ := hv
    have hval : (x.1 : V) = v :=
      congrArg (fun z : A ↦ (z : V)) hxeq
    simpa [hval] using x.2
  · intro hv
    refine ⟨hs hv, ?_⟩
    rw [restrictFinset, Finset.mem_map]
    refine ⟨⟨v, hv⟩, by simp, ?_⟩
    exact Subtype.ext rfl

@[simp]
lemma mem_restrictFinset (A : Set V) (s : Finset V)
    (hs : (s : Set V) ⊆ A) (x : A) :
    x ∈ restrictFinset A s hs ↔ (x : V) ∈ s := by
  constructor
  · intro hx
    have hx' : (x : V) ∈ liftFinset A (restrictFinset A s hs) :=
      mem_liftFinset.mpr ⟨x.property, hx⟩
    simpa only [liftFinset_restrictFinset] using hx'
  · intro hx
    have hx' : (x : V) ∈ liftFinset A (restrictFinset A s hs) := by
      simpa only [liftFinset_restrictFinset] using hx
    obtain ⟨hA, hmem⟩ := mem_liftFinset.mp hx'
    have heq : (⟨(x : V), hA⟩ : A) = x := Subtype.ext rfl
    simpa only [heq] using hmem

lemma witnessStep_new_subset_iUnion (G : SimpleGraph V) (A : Set V) :
    {v | ∃ s t : Finset V, s.Nonempty ∧
      (s : Set V) ⊆ A ∧ (t : Set V) ⊆ A ∧
      v ∈ witnessSet G s t} ⊆
      ⋃ st : Finset A × Finset A,
        witnessSet G (liftFinset A st.1) (liftFinset A st.2) := by
  rintro v ⟨s, t, -, hs, ht, hv⟩
  rw [mem_iUnion]
  refine ⟨(restrictFinset A s hs, restrictFinset A t ht), ?_⟩
  simpa [liftFinset_restrictFinset] using hv

lemma mk_witnessStep_le (G : SimpleGraph V) (A : Set V) :
    Cardinal.mk (witnessStep G A) ≤ max (Cardinal.mk A) Cardinal.aleph0 := by
  let K : Cardinal := max (Cardinal.mk A) Cardinal.aleph0
  have hK : Cardinal.aleph0 ≤ K := le_max_right _ _
  have hfin : Cardinal.mk (Finset A) ≤ K := mk_finset_le_max A
  have hindex : Cardinal.mk (Finset A × Finset A) ≤ K := by
    rw [Cardinal.mk_prod]
    have hfin' : Cardinal.lift.{u} (Cardinal.mk (Finset A)) ≤
        Cardinal.lift.{u} K := Cardinal.lift_le.mpr hfin
    have hKid : Cardinal.lift.{u, u} K = K := Cardinal.lift_id'.{u, u} K
    rw [hKid] at hfin'
    exact (mul_le_mul' hfin' hfin').trans (Cardinal.mul_eq_self hK).le
  have hfiber : ∀ st : Finset A × Finset A,
      Cardinal.mk (witnessSet G (liftFinset A st.1) (liftFinset A st.2)) ≤ K := by
    intro st
    exact (witnessSet_subsingleton G _ _).cardinalMk_le_one.trans
      (Cardinal.one_le_aleph0.trans hK)
  have hunion : Cardinal.mk
      (⋃ st : Finset A × Finset A,
        witnessSet G (liftFinset A st.1) (liftFinset A st.2)) ≤ K := by
    refine (Cardinal.mk_iUnion_le _).trans ?_
    refine (mul_le_mul' hindex (ciSup_le' hfiber)).trans ?_
    exact (Cardinal.mul_eq_self hK).le
  have hnew : Cardinal.mk
      {v | ∃ s t : Finset V, s.Nonempty ∧
        (s : Set V) ⊆ A ∧ (t : Set V) ⊆ A ∧
        v ∈ witnessSet G s t} ≤ K :=
    (Cardinal.mk_subtype_mono (witnessStep_new_subset_iUnion G A)).trans hunion
  unfold witnessStep
  refine (Cardinal.mk_union_le _ _).trans ?_
  exact (add_le_add (le_max_left _ _) hnew).trans (Cardinal.add_eq_self hK).le

/-- The closure obtained by countably iterating `witnessStep`. -/
def witnessClosure (G : SimpleGraph V) (A : Set V) : Set V :=
  ⋃ k : ℕ, (witnessStep G)^[k] A

lemma subset_witnessClosure (G : SimpleGraph V) (A : Set V) :
    A ⊆ witnessClosure G A := by
  intro x hx
  rw [witnessClosure, mem_iUnion]
  exact ⟨0, hx⟩

lemma witnessStep_iterates_mono (G : SimpleGraph V) (A : Set V) :
    Monotone (fun k ↦ (witnessStep G)^[k] A) :=
  (witnessStep_mono G).monotone_iterate_of_le_map (subset_witnessStep G A)

lemma mk_witnessStep_iterate_le (G : SimpleGraph V) (A : Set V) (k : ℕ) :
    Cardinal.mk ((witnessStep G)^[k] A) ≤
      max (Cardinal.mk A) Cardinal.aleph0 := by
  let K : Cardinal := max (Cardinal.mk A) Cardinal.aleph0
  have hK : Cardinal.aleph0 ≤ K := le_max_right _ _
  induction k with
  | zero => exact le_max_left _ _
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact (mk_witnessStep_le G _).trans (max_le ih hK)

lemma mk_witnessClosure_le (G : SimpleGraph V) (A : Set V) :
    Cardinal.mk (witnessClosure G A) ≤
      max (Cardinal.mk A) Cardinal.aleph0 := by
  let K : Cardinal := max (Cardinal.mk A) Cardinal.aleph0
  have hK : Cardinal.aleph0 ≤ K := le_max_right _ _
  unfold witnessClosure
  have hUnion := Cardinal.mk_iUnion_le_lift
    (fun k : ℕ ↦ (witnessStep G)^[k] A)
  rw [Cardinal.lift_id'.{0, u}] at hUnion
  simp only [Cardinal.lift_id'.{0, u}] at hUnion
  have hNat : Cardinal.lift.{u} (Cardinal.mk ℕ) ≤ K := by simpa using hK
  have hiter : (⨆ k : ℕ, Cardinal.mk ((witnessStep G)^[k] A)) ≤ K :=
    ciSup_le' (mk_witnessStep_iterate_le G A)
  exact hUnion.trans (Cardinal.mul_le_of_le hK hNat hiter)

lemma witnessClosure_mono (G : SimpleGraph V) :
    Monotone (witnessClosure G) := by
  intro A B hAB x hx
  rw [witnessClosure, mem_iUnion] at hx ⊢
  obtain ⟨k, hx⟩ := hx
  exact ⟨k, ((witnessStep_mono G).iterate k hAB) hx⟩

/-- Every selected witness whose finite parameters lie in a closed set already
lies in that closed set. -/
lemma witnessSet_subset_witnessClosure (G : SimpleGraph V) (A : Set V)
    (s t : Finset V) (hsne : s.Nonempty)
    (hs : (s : Set V) ⊆ witnessClosure G A)
    (ht : (t : Set V) ⊆ witnessClosure G A) :
    witnessSet G s t ⊆ witnessClosure G A := by
  classical
  let S : Type u := {x : V // x ∈ s ∪ t}
  have hstage : ∀ x : S, ∃ k : ℕ, (x : V) ∈ (witnessStep G)^[k] A := by
    intro x
    rcases Finset.mem_union.mp x.property with hx | hx
    · simpa only [witnessClosure, mem_iUnion] using hs hx
    · simpa only [witnessClosure, mem_iUnion] using ht hx
  choose k hk using hstage
  let K : ℕ := Finset.univ.sup k
  have hkK (x : S) : k x ≤ K :=
    Finset.le_sup (f := k) (Finset.mem_univ x)
  have hsK : (s : Set V) ⊆ (witnessStep G)^[K] A := by
    intro x hx
    let xS : S := ⟨x, Finset.mem_union_left t hx⟩
    exact (witnessStep_iterates_mono G A (hkK xS)) (hk xS)
  have htK : (t : Set V) ⊆ (witnessStep G)^[K] A := by
    intro x hx
    let xS : S := ⟨x, Finset.mem_union_right s hx⟩
    exact (witnessStep_iterates_mono G A (hkK xS)) (hk xS)
  intro z hz
  rw [witnessClosure, mem_iUnion]
  refine ⟨K + 1, ?_⟩
  rw [Function.iterate_succ_apply']
  exact Or.inr ⟨s, t, hsne, hsK, htK, hz⟩

/-- Closure under the finite common-neighbor selection operation, including
arbitrary finite avoidance. -/
lemma witnessClosure_has_witness (G : SimpleGraph V) (A : Set V)
    (s t : Finset V) (hsne : s.Nonempty)
    (hs : (s : Set V) ⊆ witnessClosure G A)
    (ht : (t : Set V) ⊆ witnessClosure G A)
    (h : ∃ v : V, v ∉ t ∧ ∀ x ∈ s, G.Adj x v) :
  ∃ z ∈ witnessClosure G A, z ∉ t ∧ ∀ x ∈ s, G.Adj x z := by
  obtain ⟨z, hz, hzt, hzs⟩ := witnessSet_spec h
  exact ⟨z, witnessSet_subset_witnessClosure G A s t hsne hs ht hz, hzt, hzs⟩

/-- Finitarity at a strict initial segment: every generated element already
comes from a closed initial segment below one member of its finite support. -/
lemma mem_witnessClosure_Iio_exists_Iic [LinearOrder V] {G : SimpleGraph V}
    {a x : V} (hx : x ∈ witnessClosure G (Iio a)) :
    ∃ b < a, x ∈ witnessClosure G (Iic b) := by
  classical
  rw [witnessClosure, mem_iUnion] at hx
  obtain ⟨k, hx⟩ := hx
  induction k generalizing x with
  | zero =>
      refine ⟨x, hx, subset_witnessClosure G (Iic x) ?_⟩
      exact le_rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply'] at hx
      rcases hx with hx | hx
      · exact ih hx
      · obtain ⟨s, t, hsne, hs, ht, hxw⟩ := hx
        let S : Type u := {z : V // z ∈ s ∪ t}
        have hSne : Nonempty S := by
          obtain ⟨z, hz⟩ := hsne
          exact ⟨⟨z, Finset.mem_union_left t hz⟩⟩
        let _ : Fintype S := Fintype.ofFinite S
        have hgen : ∀ z : S, ∃ b < a,
            (z : V) ∈ witnessClosure G (Iic b) := by
          intro z
          rcases Finset.mem_union.mp z.property with hz | hz
          · exact ih (hs hz)
          · exact ih (ht hz)
        choose b hb_lt hb_mem using hgen
        let bmax : V := Finset.univ.sup' Finset.univ_nonempty b
        have hb_le (z : S) : b z ≤ bmax :=
          Finset.le_sup' b (Finset.mem_univ z)
        have hbmax_lt : bmax < a := by
          rw [Finset.sup'_lt_iff]
          intro z hz
          exact hb_lt z
        have hsub (z : S) :
            (z : V) ∈ witnessClosure G (Iic bmax) :=
          (witnessClosure_mono G
            (show Iic (b z) ⊆ Iic bmax by
              intro y hy
              exact hy.trans (hb_le z))) (hb_mem z)
        have hsmax : (s : Set V) ⊆ witnessClosure G (Iic bmax) := by
          intro z hz
          exact hsub ⟨z, Finset.mem_union_left t hz⟩
        have htmax : (t : Set V) ⊆ witnessClosure G (Iic bmax) := by
          intro z hz
          exact hsub ⟨z, Finset.mem_union_right s hz⟩
        exact ⟨bmax, hbmax_lt,
          witnessSet_subset_witnessClosure G (Iic bmax) s t hsne hsmax htmax hxw⟩

/-- The least closed initial segment which generates a vertex. -/
noncomputable def closureRank [LinearOrder V] [WellFoundedLT V]
    (G : SimpleGraph V) (v : V) : V :=
  wellFounded_lt.min {a | v ∈ witnessClosure G (Iic a)}
    ⟨v, subset_witnessClosure G (Iic v) le_rfl⟩

lemma closureRank_mem [LinearOrder V] [WellFoundedLT V]
    (G : SimpleGraph V) (v : V) :
    v ∈ witnessClosure G (Iic (closureRank G v)) := by
  unfold closureRank
  exact wellFounded_lt.min_mem {a | v ∈ witnessClosure G (Iic a)}
    ⟨v, subset_witnessClosure G (Iic v) le_rfl⟩

lemma closureRank_le_of_mem [LinearOrder V] [WellFoundedLT V]
    (G : SimpleGraph V) {v a : V}
    (h : v ∈ witnessClosure G (Iic a)) : closureRank G v ≤ a := by
  apply le_of_not_gt
  intro ha
  unfold closureRank at ha
  exact wellFounded_lt.not_lt_min {b | v ∈ witnessClosure G (Iic b)} h ha

lemma closureRank_not_mem_strict [LinearOrder V] [WellFoundedLT V]
    (G : SimpleGraph V) (v : V) :
    v ∉ witnessClosure G (Iio (closureRank G v)) := by
  intro hv
  obtain ⟨b, hb, hvb⟩ := mem_witnessClosure_Iio_exists_Iic hv
  exact (not_lt_of_ge (closureRank_le_of_mem G hvb)) hb

/-- Vertices born at a fixed closure rank. -/
def rankFiber [LinearOrder V] [WellFoundedLT V]
    (G : SimpleGraph V) (a : V) : Set V :=
  {v | closureRank G v = a}

lemma rankFiber_subset_closedInitial [LinearOrder V] [WellFoundedLT V]
    (G : SimpleGraph V) (a : V) :
    rankFiber G a ⊆ witnessClosure G (Iic a) := by
  intro v hv
  change closureRank G v = a at hv
  rw [← hv]
  exact closureRank_mem G v

lemma mk_rankFiber_lt [LinearOrder V] [WellFoundedLT V]
    {G : SimpleGraph V} (huncountable : Cardinal.aleph0 < Cardinal.mk V)
    (hord : (Cardinal.mk V).ord = typeLT V) (a : V) :
    Cardinal.mk (rankFiber G a) < Cardinal.mk V := by
  have hIio : Cardinal.mk (Iio a) < Cardinal.mk V :=
    Cardinal.mk_Iio_lt a hord
  have hIic : Cardinal.mk (Iic a) < Cardinal.mk V := by
    rw [← Iio_insert]
    exact Cardinal.mk_insert_le.trans_lt
      (Cardinal.add_lt_of_lt huncountable.le hIio
        (Cardinal.one_lt_aleph0.trans huncountable))
  have hmax : max (Cardinal.mk (Iic a)) Cardinal.aleph0 < Cardinal.mk V :=
    max_lt hIic huncountable
  exact (Cardinal.mk_subtype_mono (rankFiber_subset_closedInitial G a)).trans_lt
    ((mk_witnessClosure_le G (Iic a)).trans_lt hmax)

/-- Neighbors of `v` that occur at an earlier closure rank. -/
def earlierNeighbors [LinearOrder V] [WellFoundedLT V]
    (G : SimpleGraph V) (v : V) : Set V :=
  {w | closureRank G w < closureRank G v ∧ G.Adj w v}

/-- The finite-extension form of the Hajnal--Komjáth half graph.  There is a
center `a`, an infinite set `X` of its neighbors, and a reservoir `Y` in which
every nonempty finite subset of `X` has infinitely many common neighbors. -/
def HasHalfExtension (G : SimpleGraph V) : Prop :=
  ∃ (a : V) (X Y : Set V), X.Infinite ∧
    (∀ x ∈ X, G.Adj a x) ∧ a ∉ Y ∧
    ∀ (s : Finset V), s.Nonempty → (s : Set V) ⊆ X →
      {y | y ∈ Y ∧ ∀ x ∈ s, G.Adj x y}.Infinite

/-- An infinite earlier neighborhood supplies the finite-extension half graph:
the strict closure is the common-neighbor reservoir. -/
lemma hasHalfExtension_of_infinite_earlierNeighbors
    [LinearOrder V] [WellFoundedLT V] {G : SimpleGraph V} {a : V}
    (hinf : (earlierNeighbors G a).Infinite) : HasHalfExtension G := by
  classical
  let X : Set V := earlierNeighbors G a
  let Y : Set V := witnessClosure G (Iio (closureRank G a))
  have hXY : X ⊆ Y := by
    intro x hx
    exact witnessClosure_mono G
      (show Iic (closureRank G x) ⊆ Iio (closureRank G a) by
        intro z hz
        exact lt_of_le_of_lt hz hx.1)
      (closureRank_mem G x)
  refine ⟨a, X, Y, hinf, ?_, closureRank_not_mem_strict G a, ?_⟩
  · intro x hx
    exact hx.2.symm
  · intro s hsne hsX hfinite
    let t : Finset V := hfinite.toFinset
    have htY : (t : Set V) ⊆ Y := by
      intro z hz
      have hz' : z ∈ {y | y ∈ Y ∧ ∀ x ∈ s, G.Adj x y} := by
        change z ∈ hfinite.toFinset at hz
        exact hfinite.mem_toFinset.mp hz
      exact hz'.1
    have hsY : (s : Set V) ⊆ Y := hsX.trans hXY
    have hat : a ∉ t := by
      intro ha
      exact closureRank_not_mem_strict G a (htY ha)
    have hex : ∃ v : V, v ∉ t ∧ ∀ x ∈ s, G.Adj x v := by
      refine ⟨a, hat, ?_⟩
      intro x hx
      exact (show x ∈ X from hsX hx) |>.2
    obtain ⟨z, hzY, hzt, hzs⟩ :=
      witnessClosure_has_witness G (Iio (closureRank G a)) s t hsne hsY htY hex
    apply hzt
    exact hfinite.mem_toFinset.mpr ⟨hzY, hzs⟩

lemma earlierNeighbors_finite_of_no_halfExtension
    [LinearOrder V] [WellFoundedLT V] {G : SimpleGraph V}
    (hfree : ¬ HasHalfExtension G) (v : V) :
    (earlierNeighbors G v).Finite := by
  by_contra hinf
  exact hfree (hasHalfExtension_of_infinite_earlierNeighbors
    (Set.infinite_coe_iff.mp (not_finite_iff_infinite.mp
      (Set.finite_coe_iff.not.mpr hinf))))

/-- The half-extension property of an induced subgraph is inherited by the
ambient graph. -/
lemma hasHalfExtension_of_induce {G : SimpleGraph V} (S : Set V)
    (h : HasHalfExtension (G.induce S)) : HasHalfExtension G := by
  classical
  rcases h with ⟨a, X, Y, hX, haX, haY, hcommon⟩
  let ι : S → V := fun x ↦ x
  let X' : Set V := ι '' X
  let Y' : Set V := ι '' Y
  have hX' : X'.Infinite := hX.image Subtype.val_injective.injOn
  refine ⟨a, X', Y', hX', ?_, ?_, ?_⟩
  · rintro x ⟨xS, hxS, rfl⟩
    exact haX xS hxS
  · rintro ⟨a', ha'Y, ha'eq⟩
    have : a' = a := Subtype.ext ha'eq
    exact haY (this ▸ ha'Y)
  · intro s hsne hsX'
    have hsS : (s : Set V) ⊆ S := by
      intro x hx
      obtain ⟨xS, -, hxeq⟩ := hsX' hx
      rw [← hxeq]
      exact xS.property
    let sS : Finset S := restrictFinset S s hsS
    have hsSne : sS.Nonempty := by
      obtain ⟨x, hx⟩ := hsne
      exact ⟨⟨x, hsS hx⟩, (mem_restrictFinset S s hsS _).2 hx⟩
    have hsSX : (sS : Set S) ⊆ X := by
      intro x hx
      have hx' := hsX' (show (x : V) ∈ s by simpa [sS] using hx)
      obtain ⟨z, hzX, hz⟩ := hx'
      have hzx : z = x := Subtype.ext (by simpa [ι] using hz)
      simpa [hzx] using hzX
    have hC := hcommon sS hsSne hsSX
    have hImage :
        (ι '' {y | y ∈ Y ∧ ∀ x ∈ sS, (G.induce S).Adj x y}).Infinite :=
      hC.image Subtype.val_injective.injOn
    apply hImage.mono
    rintro y ⟨yS, hy, rfl⟩
    refine ⟨⟨yS, hy.1, rfl⟩, ?_⟩
    intro x hx
    let xS : S := ⟨x, hsS hx⟩
    exact hy.2 xS (by simpa [sS, xS])

def closureRankLT [LinearOrder V] [WellFoundedLT V]
    (G : SimpleGraph V) (u v : V) : Prop :=
  closureRank G u < closureRank G v

lemma closureRankLT_wf [LinearOrder V] [WellFoundedLT V]
    (G : SimpleGraph V) : WellFounded (closureRankLT G) :=
  InvImage.wf (closureRank G) wellFounded_lt

/-- Greedy coloring of the edges joining distinct rank fibers, under failure
of the half-extension property. -/
noncomputable def crossFiberColor [LinearOrder V] [WellFoundedLT V]
    (G : SimpleGraph V) (hfree : ¬ HasHalfExtension G) : V → ℕ :=
  Erdos594.finitePredecessorColor (closureRankLT_wf G) G
    (earlierNeighbors_finite_of_no_halfExtension hfree)

lemma crossFiberColor_ne [LinearOrder V] [WellFoundedLT V]
    (G : SimpleGraph V) (hfree : ¬ HasHalfExtension G) {u v : V}
    (hrank : closureRank G u < closureRank G v) (hadj : G.Adj u v) :
    crossFiberColor G hfree u ≠ crossFiberColor G hfree v :=
  Erdos594.finitePredecessorColor_ne (closureRankLT_wf G) G
    (earlierNeighbors_finite_of_no_halfExtension hfree) hrank hadj

lemma no_halfExtension_induce {G : SimpleGraph V}
    (hfree : ¬ HasHalfExtension G) (S : Set V) :
    ¬ HasHalfExtension (G.induce S) :=
  fun h ↦ hfree (hasHalfExtension_of_induce S h)

/-- A graph without the half-extension configuration is countably colorable.
This is the closure-rank/cardinal-induction core of the
Erdős--Hajnal--Shelah argument. -/
theorem nonempty_coloring_of_no_halfExtension :
    ∀ {V : Type u} (G : SimpleGraph V),
      ¬ HasHalfExtension G → Nonempty (G.Coloring ℕ) := by
  intro V
  let P : Cardinal.{u} → Prop := fun c ↦
    ∀ (W : Type u), Cardinal.mk W = c → ∀ (G : SimpleGraph W),
      ¬ HasHalfExtension G → Nonempty (G.Coloring ℕ)
  have hP : ∀ c : Cardinal.{u}, P c := by
    intro c
    induction c using WellFoundedLT.induction with
    | ind c ih =>
        intro W hW G hfree
        by_cases hcount : Cardinal.mk W ≤ Cardinal.aleph0
        · exact Erdos594.nonempty_coloring_of_mk_le_aleph0 G hcount
        · have huncountable : Cardinal.aleph0 < Cardinal.mk W :=
            lt_of_not_ge hcount
          obtain ⟨r, hr, hord⟩ := Cardinal.exists_ord_eq W
          let _ : IsWellOrder W r := hr
          let _ : LinearOrder W := IsWellOrder.linearOrder r
          let _ : WellFoundedLT W := ⟨hr.wf⟩
          have hord' : (Cardinal.mk W).ord = typeLT W := hord
          have hfiberColor (a : W) :
              Nonempty ((G.induce (rankFiber G a)).Coloring ℕ) := by
            have hsmall := mk_rankFiber_lt (G := G) huncountable hord' a
            have hi := ih (Cardinal.mk (rankFiber G a)) (hsmall.trans_eq hW)
            exact hi (rankFiber G a) rfl (G.induce (rankFiber G a))
              (no_halfExtension_induce hfree _)
          let C : (a : W) → (G.induce (rankFiber G a)).Coloring ℕ :=
            fun a ↦ Classical.choice (hfiberColor a)
          let D : W → W → ℕ := fun a v ↦
            if hv : v ∈ rankFiber G a then C a ⟨v, hv⟩ else 0
          let color : W → ℕ := fun v ↦ Nat.pairEquiv
            (D (closureRank G v) v, crossFiberColor G hfree v)
          refine ⟨SimpleGraph.Coloring.mk color ?_⟩
          intro v w hvw heq
          have hp := Nat.pairEquiv.injective heq
          by_cases hrank : closureRank G v = closureRank G w
          · have hv : v ∈ rankFiber G (closureRank G v) := rfl
            have hw : w ∈ rankFiber G (closureRank G v) := hrank.symm
            have hlocal := (C (closureRank G v)).valid
              (show (G.induce (rankFiber G (closureRank G v))).Adj
                ⟨v, hv⟩ ⟨w, hw⟩ from hvw)
            apply hlocal
            have hfst := congrArg Prod.fst hp
            change D (closureRank G v) v = D (closureRank G w) w at hfst
            have hDeq :
                D (closureRank G v) v = D (closureRank G v) w := by
              calc
                D (closureRank G v) v = D (closureRank G w) w := hfst
                _ = D (closureRank G v) w :=
                  congrArg (fun a ↦ D a w) hrank.symm
            simpa only [D, dif_pos hv, dif_pos hw] using hDeq
          · have hcross : crossFiberColor G hfree v =
                crossFiberColor G hfree w := congrArg Prod.snd hp
            rcases lt_or_gt_of_ne hrank with hlt | hgt
            · exact (crossFiberColor_ne G hfree hlt hvw) hcross
            · exact (crossFiberColor_ne G hfree hgt hvw.symm) hcross.symm
  exact hP (Cardinal.mk V) V rfl

theorem hasHalfExtension_of_isUncountablyChromatic {G : SimpleGraph V}
    (hG : Erdos594.IsUncountablyChromatic G) : HasHalfExtension G := by
  by_contra hfree
  exact (Erdos594.isUncountablyChromatic_iff_not_nonempty.mp hG)
    (nonempty_coloring_of_no_halfExtension G hfree)

/-! ## Finite paths supplied by the half-extension configuration -/

lemma exists_walk_support_eq_cons {G : SimpleGraph V} (u : V) :
    ∀ (l : List V), (u :: l).IsChain G.Adj →
      ∃ v, ∃ p : G.Walk u v, p.support = u :: l := by
  intro l hchain
  induction l generalizing u with
  | nil => exact ⟨u, .nil, rfl⟩
  | cons v l ih =>
      cases hchain with
      | cons_cons huv htail =>
          obtain ⟨w, p, hp⟩ := ih v htail
          exact ⟨w, .cons huv p, by simp [hp]⟩

/-- An injective finite vertex sequence with adjacent successive terms is a
simple path of the prescribed length. -/
lemma exists_path_of_fin_sequence {G : SimpleGraph V} {n : ℕ}
    (f : Fin (n + 1) ↪ V)
    (hadj : ∀ (i : ℕ) (hi : i + 1 < n + 1),
      G.Adj (f ⟨i, by omega⟩) (f ⟨i + 1, hi⟩)) :
    ∃ p : G.Walk (f 0) (f (Fin.last n)),
      p.IsPath ∧ p.length = n ∧ p.support = List.ofFn f := by
  have hchain : (List.ofFn f).IsChain G.Adj :=
    List.isChain_ofFn.mpr hadj
  rw [List.ofFn_succ] at hchain
  obtain ⟨v, p, hsupp⟩ := exists_walk_support_eq_cons (f 0) _ hchain
  have hsupp' : p.support = List.ofFn f := by
    simpa only [List.ofFn_succ] using hsupp
  have hv : v = f (Fin.last n) := by
    have hlast := p.getLast_support
    have hlast' : (List.ofFn f).getLast (by simp) = v := by
      simpa only [hsupp'] using hlast
    exact hlast'.symm.trans (List.getLast_ofFn_succ f)
  subst v
  refine ⟨p, ?_, ?_, hsupp'⟩
  · apply SimpleGraph.Walk.IsPath.mk'
    rw [hsupp']
    exact List.nodup_ofFn.mpr f.injective
  · have hlen := p.length_support
    rw [hsupp', List.length_ofFn] at hlen
    omega

/-- Closing a nontrivial simple path by an edge back to its start produces a
cycle containing that closing edge. -/
lemma isCycle_concat_of_isPath {G : SimpleGraph V} {a r : V}
    (p : G.Walk a r) (hp : p.IsPath) (hclose : G.Adj r a)
    (hlen : 1 < p.length) :
    (p.concat hclose).IsCycle ∧
      (p.concat hclose).length = p.length + 1 ∧
      s(a, r) ∈ (p.concat hclose).edges := by
  have hstart : a ∉ p.support.tail := by
    have hnd := hp.support_nodup
    rw [← p.cons_tail_support] at hnd
    exact (List.nodup_cons.mp hnd).1
  have hdisj : p.support.tail.Disjoint hclose.toWalk.support.tail := by
    change p.support.tail.Disjoint [a]
    simpa only [List.disjoint_cons_right, List.disjoint_nil_right, and_true] using hstart
  refine ⟨?_, by simp, ?_⟩
  · rw [Walk.concat_eq_append]
    exact hp.isCycle_append (SimpleGraph.Walk.IsPath.of_adj hclose) hdisj (Or.inl hlen)
  · simp [Sym2.eq_swap]

/-- A canonical finite injective sample from an infinite set. -/
noncomputable def finEmbeddingIntoInfiniteSet (S : Set V) (hS : S.Infinite)
    (n : ℕ) : Fin n ↪ S := by
  letI : Infinite S := Set.infinite_coe_iff.mpr hS
  exact Fin.valEmbedding.trans (Infinite.natEmbedding S)

/-- An injective `(n+1)`-term sample from an infinite set whose last term is
the prescribed member `r`. -/
noncomputable def finEmbeddingWithLast (S : Set V) (hS : S.Infinite)
    (r : V) (n : ℕ) : Fin (n + 1) ↪ V := by
  let T : Set V := S \ {r}
  have hT : T.Infinite := hS.sdiff (Set.finite_singleton r)
  let e : Fin n ↪ T := finEmbeddingIntoInfiniteSet T hT n
  refine
    { toFun := fun i ↦ if hi : i.val < n then (e ⟨i.val, hi⟩ : V) else r
      inj' := ?_ }
  intro i j hij
  by_cases hi : i.val < n <;> by_cases hj : j.val < n
  · have he : e ⟨i.val, hi⟩ = e ⟨j.val, hj⟩ := by
      apply Subtype.ext
      simpa [hi, hj] using hij
    have hv : i.val = j.val :=
      congrArg (fun z : Fin n ↦ z.val) (e.injective he)
    exact Fin.ext hv
  · have hir : (e ⟨i.val, hi⟩ : V) ≠ r := (e ⟨i.val, hi⟩).property.2
    exact (hir (by simpa [hi, hj] using hij)).elim
  · have hjr : (e ⟨j.val, hj⟩ : V) ≠ r := (e ⟨j.val, hj⟩).property.2
    exact (hjr (by simpa [hi, hj] using hij.symm)).elim
  · apply Fin.ext
    omega

lemma finEmbeddingWithLast_mem (S : Set V) (hS : S.Infinite)
    (r : V) (hr : r ∈ S) (n : ℕ) (i : Fin (n + 1)) :
    finEmbeddingWithLast S hS r n i ∈ S := by
  change (if hi : i.val < n then
    ((finEmbeddingIntoInfiniteSet (S \ {r})
      (hS.sdiff (Set.finite_singleton r)) n ⟨i.val, hi⟩) : V)
    else r) ∈ S
  split_ifs with hi
  · exact (finEmbeddingIntoInfiniteSet (S \ {r})
      (hS.sdiff (Set.finite_singleton r)) n ⟨i.val, hi⟩).property.1
  · exact hr

@[simp]
lemma finEmbeddingWithLast_last (S : Set V) (hS : S.Infinite)
    (r : V) (n : ℕ) :
    finEmbeddingWithLast S hS r n (Fin.last n) = r := by
  change (if hi : (Fin.last n).val < n then
    ((finEmbeddingIntoInfiniteSet (S \ {r})
      (hS.sdiff (Set.finite_singleton r)) n ⟨(Fin.last n).val, hi⟩) : V)
    else r) = r
  simp

/-- A finite injective sample with prescribed distinct endpoints; all internal
vertices avoid `A`. -/
noncomputable def finEmbeddingWithEndsAvoid (S : Set V) (hS : S.Infinite)
    (u r : V) (hur : u ≠ r)
    (A : Finset V) (n : ℕ) : Fin (n + 2) ↪ V := by
  let T : Set V := S \ ((A : Set V) ∪ {u, r})
  have hfinite : ((A : Set V) ∪ {u, r}).Finite :=
    A.finite_toSet.union ((Set.finite_singleton r).insert u)
  have hT : T.Infinite := hS.sdiff hfinite
  let e : Fin n ↪ T := finEmbeddingIntoInfiniteSet T hT n
  refine
    { toFun := fun i ↦ if h0 : i.val = 0 then u
        else if hl : i.val = n + 1 then r
        else (e ⟨i.val - 1, by omega⟩ : V)
      inj' := ?_ }
  intro i j hij
  by_cases hi0 : i.val = 0 <;> by_cases hj0 : j.val = 0
  · exact Fin.ext (hi0.trans hj0.symm)
  · by_cases hjl : j.val = n + 1
    · have heq : u = r := by simpa [hi0, hj0, hjl] using hij
      exact (hur heq).elim
    · have hju : (e ⟨j.val - 1, by omega⟩ : V) ≠ u := by
        intro heq
        exact (e ⟨j.val - 1, by omega⟩).property.2
          (Or.inr (by simp [heq]))
      exact (hju (by simpa [hi0, hj0, hjl] using hij.symm)).elim
  · by_cases hil : i.val = n + 1
    · have heq : r = u := by simpa [hi0, hj0, hil] using hij
      exact (hur heq.symm).elim
    · have hiu : (e ⟨i.val - 1, by omega⟩ : V) ≠ u := by
        intro heq
        exact (e ⟨i.val - 1, by omega⟩).property.2
          (Or.inr (by simp [heq]))
      exact (hiu (by simpa [hi0, hj0, hil] using hij)).elim
  · by_cases hil : i.val = n + 1 <;> by_cases hjl : j.val = n + 1
    · exact Fin.ext (hil.trans hjl.symm)
    · have hjr : (e ⟨j.val - 1, by omega⟩ : V) ≠ r := by
        intro heq
        exact (e ⟨j.val - 1, by omega⟩).property.2
          (Or.inr (by simp [heq]))
      exact (hjr (by simpa [hi0, hj0, hil, hjl] using hij.symm)).elim
    · have hir : (e ⟨i.val - 1, by omega⟩ : V) ≠ r := by
        intro heq
        exact (e ⟨i.val - 1, by omega⟩).property.2
          (Or.inr (by simp [heq]))
      exact (hir (by simpa [hi0, hj0, hil, hjl] using hij)).elim
    · have he : e ⟨i.val - 1, by omega⟩ = e ⟨j.val - 1, by omega⟩ := by
        apply Subtype.ext
        simpa [hi0, hj0, hil, hjl] using hij
      have hv : i.val - 1 = j.val - 1 :=
        congrArg (fun z : Fin n ↦ z.val) (e.injective he)
      apply Fin.ext
      omega

lemma finEmbeddingWithEndsAvoid_mem (S : Set V) (hS : S.Infinite)
    (u r : V) (hu : u ∈ S) (hr : r ∈ S) (hur : u ≠ r)
    (A : Finset V) (n : ℕ) (i : Fin (n + 2)) :
    finEmbeddingWithEndsAvoid S hS u r hur A n i ∈ S := by
  change (if h0 : i.val = 0 then u else if hl : i.val = n + 1 then r else
    ((finEmbeddingIntoInfiniteSet
      (S \ ((A : Set V) ∪ {u, r}))
      (hS.sdiff (A.finite_toSet.union
        ((Set.finite_singleton r).insert u))) n
      ⟨i.val - 1, by omega⟩) : V)) ∈ S
  split_ifs
  · exact hu
  · exact hr
  · exact (finEmbeddingIntoInfiniteSet
      (S \ ((A : Set V) ∪ {u, r}))
      (hS.sdiff (A.finite_toSet.union
        ((Set.finite_singleton r).insert u))) n
      ⟨i.val - 1, by omega⟩).property.1

lemma finEmbeddingWithEndsAvoid_internal_not_mem
    (S : Set V) (hS : S.Infinite) (u r : V)
    (hur : u ≠ r) (A : Finset V) (n : ℕ) (i : Fin (n + 2))
    (hi0 : i.val ≠ 0) (hil : i.val ≠ n + 1) :
    finEmbeddingWithEndsAvoid S hS u r hur A n i ∉ A := by
  change (if h0 : i.val = 0 then u else if hl : i.val = n + 1 then r else
    ((finEmbeddingIntoInfiniteSet
      (S \ ((A : Set V) ∪ {u, r}))
      (hS.sdiff (A.finite_toSet.union
        ((Set.finite_singleton r).insert u))) n
      ⟨i.val - 1, by omega⟩) : V)) ∉ A
  rw [dif_neg hi0, dif_neg hil]
  exact fun hmem ↦ (finEmbeddingIntoInfiniteSet
    (S \ ((A : Set V) ∪ {u, r}))
    (hS.sdiff (A.finite_toSet.union
      ((Set.finite_singleton r).insert u))) n
    ⟨i.val - 1, by omega⟩).property.2 (Or.inl hmem)

@[simp]
lemma finEmbeddingWithEndsAvoid_first
    (S : Set V) (hS : S.Infinite) (u r : V)
    (hur : u ≠ r) (A : Finset V) (n : ℕ) :
    finEmbeddingWithEndsAvoid S hS u r hur A n 0 = u := by
  simp [finEmbeddingWithEndsAvoid]

@[simp]
lemma finEmbeddingWithEndsAvoid_last
    (S : Set V) (hS : S.Infinite) (u r : V)
    (hur : u ≠ r) (A : Finset V) (n : ℕ) :
    finEmbeddingWithEndsAvoid S hS u r hur A n (Fin.last (n + 1)) = r := by
  simp [finEmbeddingWithEndsAvoid]

/-- The center and reservoir of a half-extension configuration give odd
simple paths from the center to any prescribed member of `X`. -/
lemma exists_center_path
    {G : SimpleGraph V} {a r : V} {X Y : Set V}
    (hX : X.Infinite) (haX : ∀ x ∈ X, G.Adj a x) (haY : a ∉ Y)
    (hcommon : ∀ (s : Finset V), s.Nonempty → (s : Set V) ⊆ X →
      {y | y ∈ Y ∧ ∀ x ∈ s, G.Adj x y}.Infinite)
    (hr : r ∈ X) (k : ℕ) (hk : 1 ≤ k) :
    ∃ p : G.Walk a r, p.IsPath ∧ p.length = 2 * k + 1 := by
  classical
  let x : Fin (k + 1) ↪ V := finEmbeddingWithLast X hX r k
  have hxX (i : Fin (k + 1)) : x i ∈ X :=
    finEmbeddingWithLast_mem X hX r hr k i
  let s : Finset V := Finset.univ.map x
  have hsne : s.Nonempty := ⟨x 0, by simp [s]⟩
  have hsX : (s : Set V) ⊆ X := by
    intro z hz
    obtain ⟨i, -, hiz⟩ := Finset.mem_map.mp hz
    rw [← hiz]
    exact hxX i
  let C : Set V := {y | y ∈ Y ∧ ∀ z ∈ s, G.Adj z y}
  have hC : C.Infinite := hcommon s hsne hsX
  let yS : Fin k ↪ C := finEmbeddingIntoInfiniteSet C hC k
  let y : Fin k ↪ V := yS.trans (Function.Embedding.subtype _)
  have hyC (i : Fin k) : y i ∈ C := (yS i).property
  have hxS (i : Fin (k + 1)) : x i ∈ s := by simp [s]
  let f : Fin ((2 * k + 1) + 1) ↪ V :=
    { toFun := fun i ↦
        if h0 : i.val = 0 then a
        else if ho : i.val % 2 = 1 then
          x ⟨i.val / 2, by omega⟩
        else y ⟨i.val / 2 - 1, by omega⟩
      inj' := by
        intro i j hij
        by_cases hi0 : i.val = 0 <;> by_cases hj0 : j.val = 0
        · exact Fin.ext (hi0.trans hj0.symm)
        · by_cases hjo : j.val % 2 = 1
          · let jx : Fin (k + 1) := ⟨j.val / 2, by omega⟩
            have heq : a = x jx := by simpa [hi0, hj0, hjo, jx] using hij
            exact (haX (x jx) (hxX jx)).ne heq |>.elim
          · let jy : Fin k := ⟨j.val / 2 - 1, by omega⟩
            have heq : a = y jy := by simpa [hi0, hj0, hjo, jy] using hij
            exact haY (by simpa [heq] using (hyC jy).1) |>.elim
        · by_cases hio : i.val % 2 = 1
          · let ix : Fin (k + 1) := ⟨i.val / 2, by omega⟩
            have heq : x ix = a := by simpa [hi0, hj0, hio, ix] using hij
            exact (haX (x ix) (hxX ix)).ne heq.symm |>.elim
          · let iy : Fin k := ⟨i.val / 2 - 1, by omega⟩
            have heq : y iy = a := by simpa [hi0, hj0, hio, iy] using hij
            exact haY (by simpa [heq] using (hyC iy).1) |>.elim
        · by_cases hio : i.val % 2 = 1 <;> by_cases hjo : j.val % 2 = 1
          · let ix : Fin (k + 1) := ⟨i.val / 2, by omega⟩
            let jx : Fin (k + 1) := ⟨j.val / 2, by omega⟩
            have heq : x ix = x jx := by
              simpa [hi0, hj0, hio, hjo, ix, jx] using hij
            have hdiv : i.val / 2 = j.val / 2 :=
              congrArg Fin.val (x.injective heq)
            apply Fin.ext
            omega
          · let ix : Fin (k + 1) := ⟨i.val / 2, by omega⟩
            let jy : Fin k := ⟨j.val / 2 - 1, by omega⟩
            have heq : x ix = y jy := by
              simpa [hi0, hj0, hio, hjo, ix, jy] using hij
            exact ((hyC jy).2 (x ix) (hxS ix)).ne heq |>.elim
          · let iy : Fin k := ⟨i.val / 2 - 1, by omega⟩
            let jx : Fin (k + 1) := ⟨j.val / 2, by omega⟩
            have heq : y iy = x jx := by
              simpa [hi0, hj0, hio, hjo, iy, jx] using hij
            exact ((hyC iy).2 (x jx) (hxS jx)).ne heq.symm |>.elim
          · let iy : Fin k := ⟨i.val / 2 - 1, by omega⟩
            let jy : Fin k := ⟨j.val / 2 - 1, by omega⟩
            have heq : y iy = y jy := by
              simpa [hi0, hj0, hio, hjo, iy, jy] using hij
            have hdiv : i.val / 2 - 1 = j.val / 2 - 1 :=
              congrArg Fin.val (y.injective heq)
            apply Fin.ext
            omega }
  have hadj : ∀ (i : ℕ) (hi : i + 1 < (2 * k + 1) + 1),
      G.Adj (f ⟨i, by omega⟩) (f ⟨i + 1, hi⟩) := by
    intro i hi
    by_cases hi0 : i = 0
    · let ix : Fin (k + 1) := ⟨0, by omega⟩
      simpa [f, hi0, ix] using haX (x ix) (hxX ix)
    · by_cases hio : i % 2 = 1
      · let ix : Fin (k + 1) := ⟨i / 2, by omega⟩
        let iy : Fin k := ⟨(i + 1) / 2 - 1, by omega⟩
        have hxy := (hyC iy).2 (x ix) (hxS ix)
        have hnext : (i + 1) % 2 ≠ 1 := by omega
        simpa [f, hi0, hio, hnext, ix, iy] using hxy
      · let iy : Fin k := ⟨i / 2 - 1, by omega⟩
        let ix : Fin (k + 1) := ⟨(i + 1) / 2, by omega⟩
        have hxy := (hyC iy).2 (x ix) (hxS ix)
        have hnext : (i + 1) % 2 = 1 := by omega
        simpa [f, hi0, hio, hnext, ix, iy] using hxy.symm
  obtain ⟨p, hp, hplen, -⟩ := exists_path_of_fin_sequence f hadj
  have hstart : f 0 = a := by simp [f]
  have hend : f (Fin.last (2 * k + 1)) = r := by
    have hfapply : f (Fin.last (2 * k + 1)) =
        x ⟨(Fin.last (2 * k + 1)).val / 2, by omega⟩ := by
      simp [f]
    have hidx :
        (⟨(Fin.last (2 * k + 1)).val / 2, by omega⟩ : Fin (k + 1)) =
          Fin.last k := by
      apply Fin.ext
      change (2 * k + 1) / 2 = k
      omega
    rw [hfapply, hidx]
    exact finEmbeddingWithLast_last X hX r k
  let p' : G.Walk a r := p.copy hstart hend
  refine ⟨p', ?_, ?_⟩
  · simpa [p'] using hp
  · simp [p', hplen]

/-- Between two distinct members of `X` there are arbitrarily long even
simple alternating paths whose internal vertices avoid a prescribed finite
set. -/
lemma exists_even_path_avoiding
    {G : SimpleGraph V} {u r : V} {X Y : Set V}
    (hX : X.Infinite)
    (hcommon : ∀ (s : Finset V), s.Nonempty → (s : Set V) ⊆ X →
      {y | y ∈ Y ∧ ∀ x ∈ s, G.Adj x y}.Infinite)
    (hu : u ∈ X) (hr : r ∈ X) (hur : u ≠ r)
    (A : Finset V) (hrA : r ∉ A) (n : ℕ) :
    ∃ p : G.Walk u r, p.IsPath ∧ p.length = 2 * (n + 1) ∧
      ∀ z ∈ p.support, z ∈ A → z = u := by
  classical
  let x : Fin (n + 2) ↪ V :=
    finEmbeddingWithEndsAvoid X hX u r hur A n
  have hxX (i : Fin (n + 2)) : x i ∈ X :=
    finEmbeddingWithEndsAvoid_mem X hX u r hu hr hur A n i
  let s : Finset V := Finset.univ.map x
  have hsne : s.Nonempty := ⟨x 0, by simp [s]⟩
  have hsX : (s : Set V) ⊆ X := by
    intro z hz
    obtain ⟨i, -, hiz⟩ := Finset.mem_map.mp hz
    rw [← hiz]
    exact hxX i
  let C : Set V := {y | y ∈ Y ∧ ∀ z ∈ s, G.Adj z y}
  have hC : C.Infinite := hcommon s hsne hsX
  let D : Set V := C \ (A : Set V)
  have hD : D.Infinite := hC.sdiff A.finite_toSet
  let yS : Fin (n + 1) ↪ D := finEmbeddingIntoInfiniteSet D hD (n + 1)
  let y : Fin (n + 1) ↪ V := yS.trans (Function.Embedding.subtype _)
  have hyD (i : Fin (n + 1)) : y i ∈ D := (yS i).property
  have hxS (i : Fin (n + 2)) : x i ∈ s := by simp [s]
  let f : Fin (2 * (n + 1) + 1) ↪ V :=
    { toFun := fun i ↦ if he : i.val % 2 = 0 then
        x ⟨i.val / 2, by omega⟩
      else y ⟨i.val / 2, by omega⟩
      inj' := by
        intro i j hij
        by_cases hie : i.val % 2 = 0 <;> by_cases hje : j.val % 2 = 0
        · let ix : Fin (n + 2) := ⟨i.val / 2, by omega⟩
          let jx : Fin (n + 2) := ⟨j.val / 2, by omega⟩
          have heq : x ix = x jx := by simpa [hie, hje, ix, jx] using hij
          have hdiv : i.val / 2 = j.val / 2 :=
            congrArg Fin.val (x.injective heq)
          apply Fin.ext
          omega
        · let ix : Fin (n + 2) := ⟨i.val / 2, by omega⟩
          let jy : Fin (n + 1) := ⟨j.val / 2, by omega⟩
          have heq : x ix = y jy := by simpa [hie, hje, ix, jy] using hij
          exact ((hyD jy).1.2 (x ix) (hxS ix)).ne heq |>.elim
        · let iy : Fin (n + 1) := ⟨i.val / 2, by omega⟩
          let jx : Fin (n + 2) := ⟨j.val / 2, by omega⟩
          have heq : y iy = x jx := by simpa [hie, hje, iy, jx] using hij
          exact ((hyD iy).1.2 (x jx) (hxS jx)).ne heq.symm |>.elim
        · let iy : Fin (n + 1) := ⟨i.val / 2, by omega⟩
          let jy : Fin (n + 1) := ⟨j.val / 2, by omega⟩
          have heq : y iy = y jy := by simpa [hie, hje, iy, jy] using hij
          have hdiv : i.val / 2 = j.val / 2 :=
            congrArg Fin.val (y.injective heq)
          apply Fin.ext
          omega }
  have hadj : ∀ (i : ℕ) (hi : i + 1 < 2 * (n + 1) + 1),
      G.Adj (f ⟨i, by omega⟩) (f ⟨i + 1, hi⟩) := by
    intro i hi
    by_cases hie : i % 2 = 0
    · have hjo : (i + 1) % 2 ≠ 0 := by omega
      let ix : Fin (n + 2) := ⟨i / 2, by omega⟩
      let iy : Fin (n + 1) := ⟨(i + 1) / 2, by omega⟩
      have hxy := (hyD iy).1.2 (x ix) (hxS ix)
      change G.Adj
        (if he : i % 2 = 0 then x ⟨i / 2, by omega⟩ else y ⟨i / 2, by omega⟩)
        (if he : (i + 1) % 2 = 0 then x ⟨(i + 1) / 2, by omega⟩
          else y ⟨(i + 1) / 2, by omega⟩)
      rw [dif_pos hie, dif_neg hjo]
      exact hxy
    · have hje : (i + 1) % 2 = 0 := by omega
      let iy : Fin (n + 1) := ⟨i / 2, by omega⟩
      let ix : Fin (n + 2) := ⟨(i + 1) / 2, by omega⟩
      have hxy := (hyD iy).1.2 (x ix) (hxS ix)
      change G.Adj
        (if he : i % 2 = 0 then x ⟨i / 2, by omega⟩ else y ⟨i / 2, by omega⟩)
        (if he : (i + 1) % 2 = 0 then x ⟨(i + 1) / 2, by omega⟩
          else y ⟨(i + 1) / 2, by omega⟩)
      rw [dif_neg hie, dif_pos hje]
      exact hxy.symm
  obtain ⟨p, hp, hplen, hsupp⟩ := exists_path_of_fin_sequence f hadj
  have hstart : f 0 = u := by simp [f, x]
  have hend : f (Fin.last (2 * (n + 1))) = r := by
    have hfapply : f (Fin.last (2 * (n + 1))) = x (Fin.last (n + 1)) := by
      change (if he : (Fin.last (2 * (n + 1))).val % 2 = 0 then
        x ⟨(Fin.last (2 * (n + 1))).val / 2, by omega⟩
        else y ⟨(Fin.last (2 * (n + 1))).val / 2, by omega⟩) =
          x (Fin.last (n + 1))
      rw [dif_pos (by simp)]
      congr 1
      apply Fin.ext
      change (2 * (n + 1)) / 2 = n + 1
      omega
    rw [hfapply]
    exact finEmbeddingWithEndsAvoid_last X hX u r hur A n
  let p' : G.Walk u r := p.copy hstart hend
  refine ⟨p', by simpa [p'] using hp, by simp [p', hplen], ?_⟩
  intro z hz hza
  have hz' : z ∈ List.ofFn f := by
    simpa [p', hsupp] using hz
  simp only [List.mem_ofFn] at hz'
  obtain ⟨i, hiz⟩ := hz'
  by_cases hie : i.val % 2 = 0
  · let ix : Fin (n + 2) := ⟨i.val / 2, by omega⟩
    have hfval : f i = x ix := by
      change (if he : i.val % 2 = 0 then x ⟨i.val / 2, by omega⟩
        else y ⟨i.val / 2, by omega⟩) = x ix
      rw [dif_pos hie]
    have hzx : z = x ix := hiz.symm.trans hfval
    by_cases hi0 : ix.val = 0
    · calc
        z = x ix := hzx
        _ = x 0 := congrArg x (Fin.ext hi0)
        _ = u := finEmbeddingWithEndsAvoid_first X hX u r hur A n
    · by_cases hil : ix.val = n + 1
      · have : z = r := by
          calc z = x ix := hzx
               _ = x (Fin.last (n + 1)) := congrArg x (Fin.ext hil)
               _ = r := finEmbeddingWithEndsAvoid_last X hX u r hur A n
        exact (hrA (this ▸ hza)).elim
      · exact (finEmbeddingWithEndsAvoid_internal_not_mem
          X hX u r hur A n ix hi0 hil (hzx ▸ hza)).elim
  · let iy : Fin (n + 1) := ⟨i.val / 2, by omega⟩
    have hfval : f i = y iy := by
      change (if he : i.val % 2 = 0 then x ⟨i.val / 2, by omega⟩
        else y ⟨i.val / 2, by omega⟩) = y iy
      rw [dif_neg hie]
    have hzy : z = y iy := hiz.symm.trans hfval
    exact ((hyD iy).2 (hzy ▸ hza)).elim

/-! ## The fixed edge and all sufficiently large cycle lengths -/

/-- Strong form of Thomassen's theorem used by the public problem statement. -/
theorem eventually_cycles_through_fixed_edge {G : SimpleGraph V}
    (hG : Erdos594.IsUncountablyChromatic G) :
    ∃ a r : V, G.Adj a r ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ c : G.Walk a a,
        c.IsCycle ∧ c.length = n ∧ s(a, r) ∈ c.edges := by
  classical
  let H : SimpleGraph V := evenPathCore G
  have hH : Erdos594.IsUncountablyChromatic H :=
    isUncountablyChromatic_evenPathCore hG
  obtain ⟨a, X, Y, hX, haXH, haY, hcommonH⟩ :=
    hasHalfExtension_of_isUncountablyChromatic hH
  have haXG : ∀ x ∈ X, G.Adj a x := by
    intro x hx
    exact evenPathCore_le G (haXH x hx)
  have hcommonG : ∀ (s : Finset V), s.Nonempty → (s : Set V) ⊆ X →
      {y | y ∈ Y ∧ ∀ x ∈ s, G.Adj x y}.Infinite := by
    intro s hsne hsX
    exact (hcommonH s hsne hsX).mono (by
      intro y hy
      exact ⟨hy.1, fun x hx ↦ evenPathCore_le G (hy.2 x hx)⟩)
  obtain ⟨x₀, hx₀X⟩ := hX.nonempty
  have hax₀H : H.Adj a x₀ := haXH x₀ hx₀X
  obtain ⟨q, hqpath, hqeven, hqedge⟩ :=
    hasEvenAlternatePath_of_evenPathCore hax₀H
  let A : Finset V := q.support.toFinset
  have hexr : ∃ r ∈ X, r ∉ A := by
    by_contra h
    push Not at h
    exact hX (A.finite_toSet.subset (fun r hr ↦ h r hr))
  obtain ⟨r, hrX, hrA⟩ := hexr
  have hx₀A : x₀ ∈ A := by simp [A]
  have hx₀r : x₀ ≠ r := fun h ↦ hrA (h ▸ hx₀A)
  have harG : G.Adj a r := haXG r hrX
  refine ⟨a, r, harG, q.length + 5, ?_⟩
  intro n hn
  rcases n.even_or_odd with hneven | hnodd
  · obtain ⟨m, hm⟩ := hneven
    have hmge : 1 ≤ m - 1 := by omega
    obtain ⟨p, hppath, hplen⟩ :=
      exists_center_path hX haXG haY hcommonG hrX (m - 1) hmge
    obtain ⟨hcyc, hclen, hedge⟩ :=
      isCycle_concat_of_isPath p hppath harG.symm (by omega)
    refine ⟨p.concat harG.symm, hcyc, ?_, hedge⟩
    omega
  · obtain ⟨m, hm⟩ := hnodd
    obtain ⟨d, hd⟩ := hqeven
    let k : ℕ := m - d - 1
    obtain ⟨p, hppath, hplen, hpavoid⟩ :=
      exists_even_path_avoiding hX hcommonG hx₀X hrX hx₀r A hrA k
    have hstart_not_tail : x₀ ∉ p.support.tail := by
      have hnd := hppath.support_nodup
      rw [← p.cons_tail_support] at hnd
      exact (List.nodup_cons.mp hnd).1
    have hdisj : q.support.Disjoint p.support.tail := by
      rw [List.disjoint_left]
      intro z hzq hzp
      have hzp' : z ∈ p.support := List.mem_of_mem_tail hzp
      have hzA : z ∈ A := by simpa [A] using hzq
      have hz : z = x₀ := hpavoid z hzp' hzA
      subst z
      exact hstart_not_tail hzp
    have happPath : (q.append p).IsPath := by
      rw [SimpleGraph.Walk.isPath_def, Walk.support_append]
      exact hqpath.support_nodup.append hppath.support_nodup.tail hdisj
    obtain ⟨hcyc, hclen, hedge⟩ :=
      isCycle_concat_of_isPath (q.append p) happPath harG.symm (by
        simp only [Walk.length_append]
        omega)
    refine ⟨(q.append p).concat harG.symm, hcyc, ?_, hedge⟩
    simp only [Walk.length_append] at hclen
    omega

end

end Erdos737

/-- A cycle of a specified length containing a specified edge. -/
def CycleThroughEdgeOfLength {V : Type} (G : SimpleGraph V)
    (e : Sym2 V) (n : ℕ) : Prop :=
  ∃ v : V, ∃ c : G.Walk v v,
    c.IsCycle ∧ c.length = n ∧ e ∈ c.edges

/-- Erdős Problem 737, resolved positively by Thomassen: a graph of
chromatic number `ℵ₁` has one edge lying on a cycle of every sufficiently
large finite length. -/
theorem erdos_737 :
    ∀ (V : Type) (G : SimpleGraph V), Erdos737.ChromaticNumberAlephOne G →
      ∃ e ∈ G.edgeSet, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        CycleThroughEdgeOfLength G e n := by
  refine Iff.mp ?_ trivial
  constructor
  · intro _ V G hG
    obtain ⟨a, r, har, N, hN⟩ :=
      Erdos737.eventually_cycles_through_fixed_edge hG.isUncountablyChromatic
    refine ⟨s(a, r), G.mem_edgeSet.mpr har, N, ?_⟩
    intro n hn
    obtain ⟨c, hcyc, hlen, hedge⟩ := hN n hn
    exact ⟨a, c, hcyc, hlen, hedge⟩
  · intro _
    trivial

#print axioms erdos_737
