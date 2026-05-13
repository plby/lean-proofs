/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 760.
https://www.erdosproblems.com/forum/thread/760

Informal authors:
- Noga Alon
- Michael Krivelevich
- Benny Sudakov

Formal authors:
- Aristotle
- Matteo Del Vecchio

URLs:
- https://www.erdosproblems.com/forum/thread/760#post-5727
- https://gist.githubusercontent.com/madeve-unipi/a7ae50d445f95e73c360f442c3c84143/raw/e85a4b6a72e797488822bb5cbdfe68d9834e835c/Erdos760.lean
-/
/-
Authors: Matteo Del Vecchio, Aristotle (Harmonic)
Released under Apache 2.0 license.
-/

import Mathlib

namespace Erdos760

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.cases false
set_option linter.style.induction false
set_option linter.style.longLine false
set_option linter.style.maxHeartbeats false
set_option linter.style.multiGoal false
set_option linter.style.nativeDecide false
set_option linter.style.refine false
set_option linter.style.whitespace false

/-!
# Erdős Problem 760: Subgraphs with a Large Cochromatic Number

The cochromatic number `ζ(G)` of a graph `G` is the minimum number of colours needed to colour 
the vertices of `G` such that each colour class induces either a complete graph or empty graph.

**Erdős Problem 760**: If `G` is a graph with chromatic number `χ(G) = m`, then `G` must contain 
a subgraph `H` with `ζ(H) ≫ m / log m`.

**Answer**: YES.

This file formalizes and proves this result, following the paper "Subgraphs with a Large Cochromatic
Number" by Alon, Krivelevich, and Sudakov (1997). Note: the reference paper explicitly states
`All graphs considered here are finite and simple`, so we take this as an assumption in our statements.
-/

noncomputable section

open scoped ENat

namespace SimpleGraph

open _root_.SimpleGraph

/-! ## Cochromatic colorability -/

/-- `CochromPartable G n` holds when `G`'s vertices can be coloured with `n` colours so that 
each colour class induces either a complete or an empty graph. -/
def CochromPartable {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ f : V → Fin n, ∀ i : Fin n, G.IsClique (f ⁻¹' {i}) ∨ G.IsIndepSet (f ⁻¹' {i})

/-- The cochromatic number: minimum colours for a cochromatic partition. -/
noncomputable def cochromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ∞ :=
  ⨅ n ∈ {n : ℕ | CochromPartable G n}, (n : ℕ∞)

/-! ## Basic lemmas about CochromPartable -/

/-- Each vertex gets its own singleton colour class. -/
theorem cochromPartable_card {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    CochromPartable G (Fintype.card V) := by
  use Fintype.equivFin V
  intro i
  right
  intro u hu v hv huv 
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hu hv
  exact absurd ((Fintype.equivFin V).injective (hu.trans hv.symm)) huv

/-- If `G` is cochrom-partable with `n` colours, `ζ(G) ≤ n`. -/
theorem cochromaticNumber_le_of_cochromPartable {V : Type*} (G : SimpleGraph V) {n : ℕ}
    (h : CochromPartable G n) :
    cochromaticNumber G ≤ n := iInf₂_le n h

/-- Cochromatic partability is invariant under `comap` by an equivalence (graph isomorphism). -/
theorem CochromPartable_comap_equiv {V W : Type*} (G : SimpleGraph W) (e : V ≃ W) (k : ℕ) :
    CochromPartable (G.comap e) k ↔ CochromPartable G k := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f ∘ e.symm, fun i => ?_⟩
    have heq : (f ∘ ⇑e.symm) ⁻¹' {i} = e '' (f ⁻¹' {i}) := by
      ext w
      simp [Function.comp]
    rw [heq]
    cases hf i with
    | inl h =>
      left
      intro u hu v hv huv
      obtain ⟨u', hu', rfl⟩ := hu
      obtain ⟨v', hv', rfl⟩ := hv
      have : u' ≠ v' := fun h => huv (h ▸ rfl)
      exact (h hu' hv' this)
    | inr h =>
      right
      intro u hu v hv huv
      obtain ⟨u', hu', rfl⟩ := hu
      obtain ⟨v', hv', rfl⟩ := hv
      have : u' ≠ v' := fun h => huv (h ▸ rfl)
      exact (h hu' hv' this)
  · rintro ⟨f, hf⟩
    refine ⟨f ∘ e, fun i => ?_⟩
    have heq : (f ∘ ⇑e) ⁻¹' {i} =
        e ⁻¹' (f ⁻¹' {i}) := by
      ext; simp [Function.comp]
    rw [heq]
    cases hf i with
    | inl h =>
      left
      intro u hu v hv huv
      simp [SimpleGraph.comap] at *
      exact h hu hv (fun h => huv (e.injective h))
    | inr h =>
      right
      intro u hu v hv huv
      simp [SimpleGraph.comap] at *
      exact h hu hv (fun h => huv (e.injective h))

/-- The cochromatic number is invariant under `comap` by an
equivalence. -/
theorem cochromaticNumber_comap_equiv {V W : Type*} (G : SimpleGraph W) (e : V ≃ W) :
    cochromaticNumber (G.comap e) = cochromaticNumber G := by
  simp only [cochromaticNumber]
  congr 1; ext k
  simp [CochromPartable_comap_equiv G e k]

/-! ## Product Coloring: χ ≤ ζ · ω -/

/-- If `G` is cochrom-partable with `k` colours and has clique number `≤ ω`, then 
`G` is `(k * ω)`-colourable. -/
theorem colorable_of_cochromPartable_of_cliqueNum_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k ω : ℕ) (hk : CochromPartable G k)
    (hω : G.cliqueNum ≤ ω) :
    G.Colorable (k * ω) := by
  cases' hk with f hf
  have h_coloring : ∀ i : Fin k, ∃ g : (f ⁻¹' {i}) → Fin ω, ∀ u v : f ⁻¹' {i},
      u ≠ v → g u ≠ g v ∨ ¬G.Adj u v := by
    intro i
    cases' hf i with h h
    · have hsize : (Finset.univ.filter (fun v => f v = i)).card ≤ ω := by
        refine' le_trans _ hω
        refine' le_csSup _ _
        · use Fintype.card V
          intro n hn
          obtain ⟨s, hs⟩ := hn
          exact hs.card_eq ▸ Finset.card_le_univ _
        · refine' ⟨Finset.filter (fun v => f v = i) Finset.univ, _, _⟩ <;> simp_all +decide
          simpa [Set.preimage] using h
      have hequiv : Nonempty
          (Finset.univ.filter (fun v => f v = i) ≃ Fin ((Finset.univ.filter (fun v => f v = i)).card)) :=
        ⟨Fintype.equivOfCardEq <| by simp +decide [Fintype.card_subtype]⟩
      obtain ⟨g⟩ := hequiv
      refine' ⟨fun u => Fin.castLE hsize (g ⟨u, by aesop⟩), fun u v huv => _⟩
      simp_all +decide [Fin.ext_iff]
      left
      exact fun h => huv <| Subtype.ext <| by simpa using g.injective <| Fin.ext h
    · use fun _ => ⟨0, Nat.pos_of_ne_zero (by
          rintro rfl
          apply absurd hω
          simp only [cliqueNum, nonpos_iff_eq_zero]
          refine' ne_of_gt (lt_of_lt_of_le _ (le_csSup _ ⟨{Classical.choose (show ∃ v : V, f v = i from by grind +revert)}, _, rfl⟩))
          all_goals generalize_proofs at *
          · simp +decide
          · exact ⟨Fintype.card V, fun n hn => by
                obtain ⟨s, hs⟩ := hn
                exact hs.card_eq ▸ Finset.card_le_univ _⟩
          · simp +decide [SimpleGraph.IsClique])⟩
      intro u v huv
      right
      have := h u.2 v.2
      aesop
  choose g hg using h_coloring
  have h_unique_color : ∀ u v : V, u ≠ v → 
      (f u, g (f u) ⟨u, by simp⟩) ≠ (f v, g (f v) ⟨v, by simp⟩) ∨ ¬G.Adj u v := by
    grind
  obtain ⟨h, hh⟩ : ∃ h : V → Fin k × Fin ω, ∀ u v : V, u ≠ v → h u ≠ h v ∨ ¬G.Adj u v :=
    ⟨fun u => (f u, g (f u) ⟨u, rfl⟩), h_unique_color⟩
  use fun v => Fintype.equivFinOfCardEq (by simp +decide [Fintype.card_prod]) (h v)
  intro u v huv; specialize hh u v
  contrapose! hh; aesop

/-- Product colouring inequality: `χ(G) ≤ ζ(G) · ω(G)`. -/
theorem chi_le_cochromaticNumber_mul_cliqueNum' {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.chromaticNumber ≤ cochromaticNumber G * G.cliqueNum := by
  have h_le : ∀ n : ℕ, CochromPartable G n → G.chromaticNumber ≤ n * G.cliqueNum := by
    intro n hn
    have := colorable_of_cochromPartable_of_cliqueNum_le G n G.cliqueNum hn le_rfl
    exact_mod_cast this.chromaticNumber_le
  refine' le_trans (h_le _ _) _
  exact (InfSet.sInf {n : ℕ | CochromPartable G n})
  · exact Nat.sInf_mem (show
        {n : ℕ | CochromPartable G n}.Nonempty from ⟨_, cochromPartable_card G⟩)
  · refine' mul_le_mul_left _ _
    refine' le_ciInf fun n => _
    by_cases hn : CochromPartable G n <;> simp +decide [hn]
    exact Nat.sInf_le hn

/-! ## Degeneracy coloring bound -/

/-- If every non-empty induced subgraph has a vertex of degree `< d`,
then `G` is `d`-colourable. -/
theorem colorable_of_degenerate {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (hd : 0 < d)
    (hdegen : ∀ (S : Finset V), S.Nonempty → ∃ v ∈ S, (S.filter (fun w => G.Adj v w)).card < d) :
    G.Colorable d := by
  obtain ⟨c, hc⟩ : ∃ c : V → Fin d, ∀ v w : V, G.Adj v w → c v ≠ c w := by
    suffices h_colorable : ∀ (S : Finset V),
        ∃ c : V → Fin d, ∀ v ∈ S, ∀ w ∈ S, G.Adj v w → c v ≠ c w by
      exact Exists.elim (h_colorable Finset.univ)
        fun c hc => ⟨c, fun v w hvw => hc v (Finset.mem_univ v) w (Finset.mem_univ w) hvw⟩
    intro S
    induction' S using Finset.strongInduction with S ih
    by_cases hS : S.Nonempty
    · obtain ⟨v, hvS, hv⟩ := hdegen S hS
      obtain ⟨c, hc⟩ := ih (S.erase v) (Finset.erase_ssubset hvS)
      obtain ⟨color_v, hcolor_v⟩ :
          ∃ color_v : Fin d, ∀ w ∈ S, G.Adj v w → color_v ≠ c w := by
        have h_color_v :
            Finset.card (Finset.image c (Finset.filter (fun w => G.Adj v w) S)) < d :=
          lt_of_le_of_lt Finset.card_image_le hv
        contrapose! h_color_v
        have : Finset.image c (Finset.filter (fun w => G.Adj v w) S) = Finset.univ :=
          Finset.eq_univ_of_forall fun x => by
            obtain ⟨w, hwS, hw, rfl⟩ :=
              h_color_v x
            exact Finset.mem_image_of_mem _
              (Finset.mem_filter.mpr ⟨hwS, hw⟩)
        simp +decide [this]
      use fun w => if w = v then color_v else c w
      intro u hu w hw huv
      by_cases hu' : u = v <;>
        by_cases hw' : w = v <;> simp_all +decide
      exact Ne.symm (hcolor_v u hu huv.symm)
    · exact ⟨fun _ => ⟨0, hd⟩, by aesop⟩
  exact ⟨c, by aesop⟩

/-! ## Spanning subgraph from an edge subset -/

/-- A spanning subgraph of `G` defined by a subset `T` of `G`'s
edges. -/
def spanSub {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset (Sym2 V)) : SimpleGraph V where
  Adj u v := s(u, v) ∈ T ∧ G.Adj u v
  symm _ _ h := ⟨Sym2.eq_swap ▸ h.1, h.2.symm⟩
  loopless := ⟨fun _ h => G.ne_of_adj h.2 rfl⟩

instance spanSub_decidableRel {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset (Sym2 V)) :
    DecidableRel (spanSub G T).Adj :=
  fun _ _ => instDecidableAnd

/-! ## Key counting identities -/

theorem card_filter_superset' {α : Type*} [DecidableEq α] (U A : Finset α) (hA : A ⊆ U) :
    (U.powerset.filter (A ⊆ ·)).card = 2 ^ (U.card - A.card) := by
  rw [← Finset.Icc_eq_filter_powerset]
  exact Finset.card_Icc_finset hA

theorem card_filter_disjoint' {α : Type*} [DecidableEq α] (U A : Finset α) (hA : A ⊆ U) :
    (U.powerset.filter (Disjoint A ·)).card = 2 ^ (U.card - A.card) := by
  rw [← card_filter_superset' _ _ hA]
  refine Finset.card_bij (fun x _ => U \ x) ?_ ?_ ?_
  · simp +contextual [Finset.subset_iff, Finset.disjoint_left]; tauto
  · simp +contextual [Finset.ext_iff]; grind
  · simp +decide [Finset.disjoint_left, Finset.subset_iff]
    exact fun b hb₁ hb₂ => ⟨U \ b, ⟨fun x hx => by aesop, fun x hx₁ hx₂ => by aesop⟩, by aesop⟩

/-- Key combinatorial estimate: `6 · C(N, 4L+1) ≤ 2^C(4L+1, 2)`. -/
theorem six_choose_le_pow_choose2' (N L : ℕ) (hN : N ≤ 2 ^ L) (hL : 1 ≤ L) :
    6 * N.choose (4 * L + 1) ≤ 2 ^ ((4 * L + 1).choose 2) := by
  have h6 :
      6 * Nat.choose N (4 * L + 1) ≤ 6 * 2 ^ (L * (4 * L + 1)) / Nat.factorial (4 * L + 1) := by
    have : Nat.factorial (4 * L + 1) * Nat.choose N (4 * L + 1) ≤ N ^ (4 * L + 1) := by
      rw [← Nat.descFactorial_eq_factorial_mul_choose]
      exact Nat.descFactorial_le_pow _ _
    rw [Nat.le_div_iff_mul_le (Nat.factorial_pos _)]
    rw [pow_mul]
    nlinarith [pow_le_pow_left' hN (4 * L + 1)]
  refine le_trans h6 ?_
  refine Nat.div_le_of_le_mul ?_
  refine' Nat.mul_le_mul _ _
  · exact le_trans (by decide) (Nat.factorial_le (show 4 * L + 1 ≥ 3 by linarith))
  · gcongr <;> norm_num [Nat.choose_two_right]
    grind

/-- If no `(k+1)`-subset is a clique in `spanSub G T`, then `ω(spanSub G T) ≤ k`. -/
theorem cliqueNum_spanSub_le_of_no_large_clique {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset (Sym2 V)) (k : ℕ)
    (h : ∀ S : Finset V, S.card = k + 1 → ¬((spanSub G T).IsClique ↑S)) :
    (spanSub G T).cliqueNum ≤ k := by
  contrapose! h
  obtain ⟨S, hS⟩ : ∃ S : Finset V, S.card ≥ k + 1 ∧ (spanSub G T).IsNClique S.card S := by
    contrapose! h
    refine' csSup_le' _
    rintro n ⟨s, hs⟩
    exact not_lt.1 fun contra => h s (by linarith [hs.2.symm]) (by simpa [hs.2.symm] using hs)
  obtain ⟨S', hS'⟩ := Finset.exists_subset_card_eq hS.1
  exact ⟨S', hS'.2, fun u hu v hv huv => hS.2.1 (hS'.1 hu) (hS'.1 hv) huv⟩

/-- Contrapositive extraction of the degeneracy witness. -/
theorem degeneracy_of_no_dense_indep {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset (Sym2 V)) (d : ℕ)
    (h : ∀ S : Finset V, S.Nonempty → (∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬(spanSub G T).Adj u v) →
      ¬(∀ v ∈ S, d ≤ (S.filter (fun w => G.Adj v w)).card)) :
    ∀ S : Finset V, S.Nonempty → (∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬(spanSub G T).Adj u v) →
      ∃ v ∈ S, (S.filter (fun w => G.Adj v w)).card < d :=
  fun S hS hS' => by push Not at h; exact h S hS hS'

/-- Double-counting: `d · |S| ≤ 2 · |E(G[S])|`. -/
theorem edgeFinset_within_ge_of_min_deg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (d : ℕ)
    (hmin : ∀ v ∈ S, d ≤ (S.filter (fun w => G.Adj v w)).card) :
    d * S.card ≤ 2 * (G.edgeFinset.filter (fun e => ∀ v, v ∈ e → v ∈ S)).card := by
  have h_double_count : ∑ v ∈ S, (S.filter (fun w => G.Adj v w)).card = 
      2 * (Finset.filter (fun e => (∀ v ∈ e, v ∈ S)) G.edgeFinset).card := by
    have h_double_count : ∑ v ∈ S, (S.filter (fun w => G.Adj v w)).card = 
        ∑ e ∈ Finset.filter (fun e => (∀ v ∈ e, v ∈ S)) G.edgeFinset, (e.toFinset.filter (fun v => v ∈ S)).card := by
      have h_double_count : ∀ v ∈ S, (S.filter (fun w => G.Adj v w)).card = ∑ e ∈ Finset.filter (fun e => (∀ v ∈ e, v ∈ S)) G.edgeFinset, (if v ∈ e.toFinset then 1 else 0) := by
        intro v hv
        simp;
        refine' Finset.card_bij ( fun w hw => s(v, w) ) _ _ _ <;> simp_all +decide;
        · grind;
        · rintro ⟨ u, w ⟩ huv hS hvw; cases hvw; aesop;
      rw [ Finset.sum_congr rfl h_double_count, Finset.sum_comm ];
      simp +decide [Finset.filter_mem_eq_inter];
      exact Finset.sum_congr rfl fun x hx => congr_arg Finset.card ( by ext; aesop );
    rw [ h_double_count, Finset.sum_const_nat ];
    rw [ mul_comm ];
    intro e he; rcases e with ⟨ u, v ⟩ ; simp_all +decide ;
    rw [ Finset.card_eq_two ] ; use u, v ; aesop;
  simpa [ mul_comm, h_double_count ] using Finset.sum_le_sum hmin

/-- The set of edges of `G` with both endpoints in `S`. -/
def edgesWithin {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ∀ v, v ∈ e → v ∈ S)

theorem edgesWithin_sub_edgeFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    edgesWithin G S ⊆ G.edgeFinset :=
  Finset.filter_subset _ _

/-- If `S` is independent in `spanSub G T`, every `G`-edge within `S` avoids `T`. -/
theorem indep_spanSub_edgesWithin_disjoint {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset (Sym2 V)) (S : Finset V)
    (hindep : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬(spanSub G T).Adj u v) :
    Disjoint (edgesWithin G S) T := by
  unfold edgesWithin
  simp_all +decide [Finset.disjoint_left, spanSub]
  rintro ⟨u, v⟩ huv huv' huv''
  specialize hindep u (huv' u (by simp +decide)) v (huv' v (by simp +decide))
  aesop

/-- For a `G`-clique `S`, `|E(G[S])| ≥ C(|S|, 2)`. -/
theorem card_edgesWithin_clique {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (hclique : G.IsClique ↑S) :
    S.card.choose 2 ≤ (edgesWithin G S).card := by
  have h_deg : ∀ v ∈ S, (S.card - 1) ≤ (S.filter (fun w => G.Adj v w)).card := by
    intro v hv
    rw [← Finset.card_erase_of_mem hv]
    exact Finset.card_le_card fun w hw => by
      have := hclique (Finset.mem_coe.2 (Finset.mem_of_mem_erase hw)) hv
      aesop
  have h_double : (S.card - 1) * S.card ≤ 2 * (G.edgeFinset.filter (fun e => ∀ v, v ∈ e → v ∈ S)).card :=
    edgeFinset_within_ge_of_min_deg G S _ h_deg
  rw [Nat.choose_two_right, Nat.div_le_iff_le_mul_add_pred] <;> norm_num
  linarith!

/-- For a fixed `G`-clique `S` of size `k`, at most `2^(m − C(k,2))` edge subsets make `S` a clique. -/
theorem per_clique_bad_count {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (k : ℕ) (hS : S.card = k)
    (hclique : G.IsClique ↑S) :
    (G.edgeFinset.powerset.filter (fun T => (spanSub G T).IsClique ↑S)).card ≤
      2 ^ (G.edgeFinset.card - k.choose 2) := by
  refine' le_trans ( Finset.card_le_card _ ) _;
  exact Finset.image ( fun T => T ∪ edgesWithin G S ) ( Finset.powerset ( G.edgeFinset \ edgesWithin G S ) );
  · intro T hT; simp_all +decide [ Finset.subset_iff ] ;
    refine' ⟨ T \ edgesWithin G S, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff, spanSub ];
    rintro ⟨ u, v ⟩ huv; have := hT.2; simp_all +decide [ Set.Pairwise ] ;
    unfold edgesWithin at huv; aesop;
  · refine' Finset.card_image_le.trans _;
    rw [ Finset.card_powerset, Finset.card_sdiff ];
    rw [ Finset.inter_eq_left.mpr ];
    · exact pow_le_pow_right₀ ( by decide ) ( Nat.sub_le_sub_left ( by simpa [ hS ] using card_edgesWithin_clique G S hclique ) _ );
    · exact edgesWithin_sub_edgeFinset G S

/-- For a dense independent set `S` with min `G`-degree `≥ d`, at most `2^(m − d·|S|/2)` edge 
subsets make `S` independent. -/
theorem per_degen_bad_count {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) 
    [DecidableRel G.Adj] (S : Finset V) (d : ℕ)
    (hdense : ∀ v ∈ S, d ≤ (S.filter (fun w => G.Adj v w)).card) :
    (G.edgeFinset.powerset.filter (fun T => ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬(spanSub G T).Adj u v)).card ≤
      2 ^ (G.edgeFinset.card - d * S.card / 2) := by
  refine' le_trans _ (pow_le_pow_right₀ (by decide) _)
  rotate_left
  · exact G.edgeFinset.card - (edgesWithin G S).card
  · refine' Nat.sub_le_sub_left _ _
    have := edgeFinset_within_ge_of_min_deg G S d hdense
    exact Nat.div_le_of_le_mul this
  · refine' le_trans _ (le_of_eq _)
    · convert Finset.card_le_card ?_
      · show Finset (Finset (Sym2 V))
        exact Finset.image (fun T => T)
          (Finset.filter (fun T => Disjoint (edgesWithin G S) T) (Finset.powerset G.edgeFinset))
      · simp +decide [Finset.subset_iff]
        exact fun T hT₁ hT₂ => ⟨hT₁, indep_spanSub_edgesWithin_disjoint G T S hT₂⟩
    · simp +decide
      convert card_filter_disjoint' G.edgeFinset (edgesWithin G S) 
        (edgesWithin_sub_edgeFinset G S) using 1

/-- Union bound for filters with existential quantifier. -/
theorem card_filter_bexists_le_sum {α β : Type*} [DecidableEq α] [DecidableEq β]
    [Fintype β] (Ω : Finset α) (P : α → β → Prop) [∀ a b, Decidable (P a b)] :
    (Ω.filter (fun a => ∃ b, P a b)).card ≤ ∑ b : β, (Ω.filter (fun a => P a b)).card := by
  refine' le_trans _ Finset.card_biUnion_le
  exact Finset.card_le_card fun x hx => by aesop

/-- When `G` has fewer than `2L` edges, `T = ∅` works. -/
theorem exists_good_edge_subset_of_few_edges {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hm : G.edgeFinset.card < 2 * Nat.clog 2 (Fintype.card V)) :
    ∃ T ∈ G.edgeFinset.powerset,
      (∀ S : Finset V, S.card = 4 * Nat.clog 2 (Fintype.card V) + 1 → ¬((spanSub G T).IsClique ↑S)) ∧
      (∀ S : Finset V, S.Nonempty → (∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬(spanSub G T).Adj u v) →
        ¬(∀ v ∈ S, 4 * Nat.clog 2 (Fintype.card V) ≤ (S.filter (fun w => G.Adj v w)).card)) := by
  refine' ⟨∅, _, _, _⟩ <;>
    simp +decide [spanSub]
  · intro S hS hclique
    have := Finset.card_le_univ S
    simp_all +decide
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 (by linarith : 1 < Finset.card S)
    specialize hclique hu hv; aesop
  · intro S hS_nonempty
    by_contra h_contra
    push Not at h_contra
    have h_deg_sum :
        4 * Nat.clog 2 (Fintype.card V) * S.card ≤
          2 * (G.edgeFinset.filter (fun e => ∀ v, v ∈ e → v ∈ S)).card :=
      edgeFinset_within_ge_of_min_deg G S _ h_contra
    have hSpos := Finset.card_pos.mpr hS_nonempty
    have hfilt := Finset.card_filter_le G.edgeFinset (fun e => ∀ v ∈ e, v ∈ S)
    nlinarith

/-- The total bad-clique count, times 6, is `≤ 2^m`. -/
theorem clique_bad_total_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hn : 2 ≤ Fintype.card V) :
    6 * (G.edgeFinset.powerset.filter (fun T =>
      ∃ S : Finset V, S.card = 4 * Nat.clog 2 (Fintype.card V) + 1 ∧ 
      (spanSub G T).IsClique ↑S)).card ≤ 2 ^ G.edgeFinset.card := by
  refine' le_trans ( mul_le_mul_of_nonneg_left ( card_filter_bexists_le_sum _ _ ) ( by norm_num ) ) _;
  refine' le_trans ( mul_le_mul_of_nonneg_left ( Finset.sum_le_sum fun S hS => _ ) ( by norm_num ) ) _;
  use fun S => if S.card = 4 * Nat.clog 2 ( Fintype.card V ) + 1 ∧ G.IsClique S then 2 ^ ( G.edgeFinset.card - ( S.card.choose 2 ) ) else 0;
  · split_ifs with h;
    · have := per_clique_bad_count G S ( 4 * Nat.clog 2 ( Fintype.card V ) + 1 ) h.1 h.2; aesop;
    · simp_all +decide [ spanSub ];
      intro T hT hS hclique; specialize h hS; simp_all +decide [ Set.Pairwise ] ;
  · by_cases h : 4 * Nat.clog 2 ( Fintype.card V ) + 1 ≤ Fintype.card V <;> simp_all +decide [ Finset.sum_ite ];
    · have h_card : (Finset.filter (fun S : Finset V => S.card = 4 * Nat.clog 2 (Fintype.card V) + 1 ∧ G.IsClique S) (Finset.powerset (Finset.univ : Finset V))).card ≤ Nat.choose (Fintype.card V) (4 * Nat.clog 2 (Fintype.card V) + 1) := by
        exact le_trans ( Finset.card_le_card ( show Finset.filter ( fun S : Finset V => S.card = 4 * Nat.clog 2 ( Fintype.card V ) + 1 ∧ G.IsClique ↑S ) ( Finset.powerset ( Finset.univ : Finset V ) ) ⊆ Finset.powersetCard ( 4 * Nat.clog 2 ( Fintype.card V ) + 1 ) ( Finset.univ : Finset V ) from fun S hS => Finset.mem_powersetCard.mpr ⟨ Finset.subset_univ _, by aesop ⟩ ) ) ( by simp +decide [ Finset.card_univ ] );
      have h_exp : 6 * Nat.choose (Fintype.card V) (4 * Nat.clog 2 (Fintype.card V) + 1) ≤ 2 ^ ((4 * Nat.clog 2 (Fintype.card V) + 1).choose 2) := by
        apply six_choose_le_pow_choose2';
        · exact Nat.le_pow_clog ( by decide ) _;
        · exact Nat.le_trans ( by native_decide ) ( Nat.clog_mono_right _ hn );
      by_cases h₂ : (4 * Nat.clog 2 (Fintype.card V) + 1).choose 2 ≤ G.edgeFinset.card;
      · rw [ ← mul_assoc ];
        refine' le_trans ( Nat.mul_le_mul_right _ ( Nat.mul_le_mul_left _ h_card ) ) _;
        exact le_trans ( Nat.mul_le_mul_right _ h_exp ) ( by rw [ ← pow_add, Nat.add_sub_of_le h₂ ] );
      · have h_empty : ∀ S : Finset V, S.card = 4 * Nat.clog 2 (Fintype.card V) + 1 → ¬G.IsClique S := by
          intro S hS hclique
          have h_edges : (edgesWithin G S).card ≥ (4 * Nat.clog 2 (Fintype.card V) + 1).choose 2 := by
            have := card_edgesWithin_clique G S hclique; aesop;
          exact h₂ ( h_edges.trans ( Finset.card_le_card ( edgesWithin_sub_edgeFinset _ _ ) ) );
        rw [ Finset.card_eq_zero.mpr ] <;> aesop;
    · rw [ Finset.card_eq_zero.mpr ] <;> norm_num;
      exact fun S hS => absurd ( Finset.card_le_univ S ) ( by simp +decide [ hS ] ; linarith )

/-! ## Telescoping sum identity for geometric series -/

/-- `(2^L − 1) · Σ 2^(m−(s+1)L) + 2^(m−KL) = 2^m`. -/
theorem geom_sum_telesc (K m L : ℕ) (hL : 1 ≤ L) (hKL : K * L ≤ m) :
    (2 ^ L - 1) * ∑ s ∈ Finset.range K, 2 ^ (m - (s + 1) * L) + 2 ^ (m - K * L) = 2 ^ m := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    convert ih (by nlinarith) using 1
    rw [Finset.sum_range_succ, mul_add]
    have hstep : m - K * L = (m - (K + 1) * L) + L :=
      Nat.sub_eq_of_eq_add <| by
        linarith [Nat.sub_add_cancel (show (K + 1) * L ≤ m from hKL)]
    rw [hstep]
    zify
    norm_num
    ring

/-- Corollary: `(2^L − 1) · Σ ≤ 2^m`. -/
theorem geom_sum_bound (K m L : ℕ) (hL : 1 ≤ L) (hKL : K * L ≤ m) :
    (2 ^ L - 1) * ∑ s ∈ Finset.range K, 2 ^ (m - (s + 1) * L) ≤ 2 ^ m := by
  have h := geom_sum_telesc K m L hL hKL
  linarith [Nat.one_le_two_pow (n := m - K * L)]

/-- `L ≥ 5` when `4L < N ≤ 2^L`. -/
theorem clog_ge_five (N : ℕ) (hN : 2 ≤ N) (hlarge : 4 * Nat.clog 2 N < N) : 5 ≤ Nat.clog 2 N := by
  by_cases h5 : N ≤ 16
  · interval_cases N <;> exact absurd hlarge (by decide)
  · grind +suggestions

/-- `C(N, s+1) · 2^(m − 2L(s+1)) ≤ 2^(m − L(s+1))`. -/
theorem choose_pow_bound (N L s m : ℕ) (hN : N ≤ 2 ^ L) (hle : 2 * L * (s + 1) ≤ m) :
    N.choose (s + 1) * 2 ^ (m - 2 * L * (s + 1)) ≤ 2 ^ (m - L * (s + 1)) := by
  convert Nat.mul_le_mul_right _ (Nat.choose_le_pow _ _ |> le_trans <| Nat.pow_le_pow_left hN _) using 1
  rw [← pow_mul, ← pow_add]
  grind

/-- Total bad-degeneracy count, times 5, is `≤ 2^m`. -/
theorem degen_bad_total_bound {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) 
    [DecidableRel G.Adj] (hn : 2 ≤ Fintype.card V)
    (hlarge : 4 * Nat.clog 2 (Fintype.card V) < Fintype.card V) :
    5 * (G.edgeFinset.powerset.filter (fun T =>
      ∃ S : Finset V, S.Nonempty ∧
        (∀ u ∈ S, ∀ v ∈ S,
          u ≠ v → ¬(spanSub G T).Adj u v) ∧
        (∀ v ∈ S,
          4 * Nat.clog 2 (Fintype.card V) ≤
            (S.filter
              (fun w => G.Adj v w)).card))).card ≤
      2 ^ G.edgeFinset.card := by
  have L_ge_5 : 5 ≤ Nat.clog 2 (Fintype.card V) := clog_ge_five (Fintype.card V) hn hlarge
  -- Use union bound over dense independent sets S. For each S, per_degen_bad_count gives bound 2^(m - 2L|S|).
  have h_union_bound : (G.edgeFinset.powerset.filter (fun T =>
    ∃ S : Finset V,
      S.Nonempty ∧
        (∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬(spanSub G T).Adj u v) ∧
        (∀ v ∈ S, 4 * Nat.clog 2 (Fintype.card V) ≤ (S.filter (fun w => G.Adj v w)).card))).card ≤
    ∑ s ∈ Finset.range (Nat.floor (G.edgeFinset.card / (2 * Nat.clog 2 (Fintype.card V)))), (Fintype.card V).choose (s + 1) * 2 ^ (G.edgeFinset.card - 2 * Nat.clog 2 (Fintype.card V) * (s + 1)) := by
      have h_union_bound : ∀ s ∈ Finset.range (Nat.floor (G.edgeFinset.card / (2 * Nat.clog 2 (Fintype.card V)))), (G.edgeFinset.powerset.filter (fun T =>
          ∃ S : Finset V,
            S.card = s + 1 ∧
              (∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬(spanSub G T).Adj u v) ∧
              (∀ v ∈ S, 4 * Nat.clog 2 (Fintype.card V) ≤ (S.filter (fun w => G.Adj v w)).card))).card ≤
          (Fintype.card V).choose (s + 1) * 2 ^ (G.edgeFinset.card - 2 * Nat.clog 2 (Fintype.card V) * (s + 1)) := by
            intro s hs
            have h_filter : ∀ S : Finset V, S.card = s + 1 → (G.edgeFinset.powerset.filter (fun T =>
                (∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬(spanSub G T).Adj u v) ∧
                (∀ v ∈ S, 4 * Nat.clog 2 (Fintype.card V) ≤ (S.filter (fun w => G.Adj v w)).card))).card ≤
                2 ^ (G.edgeFinset.card - 2 * Nat.clog 2 (Fintype.card V) * (s + 1)) := by
                  intro S hS_card
                  by_cases hS_dense : ∀ v ∈ S, 4 * Nat.clog 2 (Fintype.card V) ≤ (S.filter (fun w => G.Adj v w)).card;
                  · have := per_degen_bad_count G S ( 4 * Nat.clog 2 ( Fintype.card V ) ) hS_dense;
                    simp_all +decide [mul_comm];
                    grind;
                  · rw [ Finset.card_eq_zero.mpr ] <;> aesop;
            refine' le_trans ( Finset.card_le_card _ ) _;
            exact Finset.biUnion ( Finset.powersetCard ( s + 1 ) Finset.univ ) fun S => Finset.filter ( fun T => ( ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ ( spanSub G T ).Adj u v ) ∧ ∀ v ∈ S, 4 * Nat.clog 2 ( Fintype.card V ) ≤ Finset.card ( Finset.filter ( fun w => G.Adj v w ) S ) ) ( Finset.powerset G.edgeFinset );
            · simp +contextual [ Finset.subset_iff ];
            · refine' le_trans ( Finset.card_biUnion_le ) _;
              exact le_trans ( Finset.sum_le_sum fun x hx => h_filter x <| Finset.mem_powersetCard.mp hx |>.2 ) <| by simp +decide [ Finset.card_univ ] ;
      refine' le_trans ( Finset.card_le_card _ ) ( Finset.card_biUnion_le.trans ( Finset.sum_le_sum h_union_bound ) );
      intro T hT
      obtain ⟨S, hS_nonempty, hS_indep, hS_deg⟩ := (Finset.mem_filter.mp hT).right
      have hS_card : S.card ≤ Nat.floor (G.edgeFinset.card / (2 * Nat.clog 2 (Fintype.card V))) := by
        have hS_card : 4 * Nat.clog 2 (Fintype.card V) * S.card ≤ 2 * G.edgeFinset.card := by
          have := edgeFinset_within_ge_of_min_deg G S ( 4 * Nat.clog 2 ( Fintype.card V ) ) hS_deg;
          exact this.trans ( Nat.mul_le_mul_left _ ( Finset.card_filter_le _ _ ) );
        exact Nat.le_floor ( Nat.le_div_iff_mul_le ( by positivity ) |>.2 ( by linarith ) );
      simp +zetaDelta at *;
      exact ⟨ S.card - 1, by rw [ tsub_lt_iff_left ] <;> linarith [ Finset.card_pos.mpr hS_nonempty ], hT.1, S, by rw [ Nat.sub_add_cancel hS_nonempty.card_pos ], hS_indep, hS_deg ⟩;
  -- Use choose_pow_bound to reduce each term.
  have h_choose_pow_bound : ∀ s ∈ Finset.range (Nat.floor (G.edgeFinset.card / (2 * Nat.clog 2 (Fintype.card V)))), (Fintype.card V).choose (s + 1) * 2 ^ (G.edgeFinset.card - 2 * Nat.clog 2 (Fintype.card V) * (s + 1)) ≤ 2 ^ (G.edgeFinset.card - Nat.clog 2 (Fintype.card V) * (s + 1)) := by
    intros s hs
    apply choose_pow_bound (Fintype.card V) (Nat.clog 2 (Fintype.card V)) s G.edgeFinset.card;
    · exact Nat.le_pow_clog ( by decide ) _;
    · nlinarith [ Finset.mem_range.mp hs, Nat.div_mul_le_self ( G.edgeFinset.card ) ( 2 * Nat.clog 2 ( Fintype.card V ) ), Nat.floor_le ( show 0 ≤ G.edgeFinset.card / ( 2 * Nat.clog 2 ( Fintype.card V ) ) from Nat.zero_le _ ) ];
  -- Use geom_sum_bound to bound the geometric sum.
  have h_geom_sum_bound : 5 * ∑ s ∈ Finset.range (Nat.floor (G.edgeFinset.card / (2 * Nat.clog 2 (Fintype.card V)))), 2 ^ (G.edgeFinset.card - Nat.clog 2 (Fintype.card V) * (s + 1)) ≤ 2 ^ G.edgeFinset.card := by
    have := geom_sum_bound ( Nat.floor ( G.edgeFinset.card / ( 2 * Nat.clog 2 ( Fintype.card V ) ) ) ) G.edgeFinset.card ( Nat.clog 2 ( Fintype.card V ) ) ( by linarith ) ( by
      norm_num +zetaDelta at *;
      nlinarith [ Nat.div_mul_le_self ( G.edgeFinset.card ) ( 2 * Nat.clog 2 ( Fintype.card V ) ) ] );
    simp_all +decide [ mul_comm ];
    exact le_trans ( Nat.mul_le_mul_right _ ( show 5 ≤ 2 ^ Nat.clog 2 ( Fintype.card V ) - 1 from Nat.le_sub_one_of_lt ( lt_of_lt_of_le ( by decide ) ( Nat.pow_le_pow_right ( by decide ) L_ge_5 ) ) ) ) this;
  exact le_trans ( Nat.mul_le_mul_left _ h_union_bound ) ( le_trans ( Nat.mul_le_mul_left _ ( Finset.sum_le_sum h_choose_pow_bound ) ) h_geom_sum_bound )

/-! ## Main existence result via first moment method -/

/-- There exists `T ⊆ E(G)` with no bad configurations. -/
theorem exists_good_edge_subset {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) 
    [DecidableRel G.Adj] (hn : 2 ≤ Fintype.card V)
    (hlarge : 4 * Nat.clog 2 (Fintype.card V) < Fintype.card V) :
    ∃ T ∈ G.edgeFinset.powerset,
      (∀ S : Finset V, S.card = 4 * Nat.clog 2 (Fintype.card V) + 1 → ¬((spanSub G T).IsClique ↑S)) ∧
      (∀ S : Finset V, S.Nonempty → (∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬(spanSub G T).Adj u v) →
        ¬(∀ v ∈ S, 4 * Nat.clog 2 (Fintype.card V) ≤ (S.filter (fun w => G.Adj v w)).card)) := by
  by_contra! h
  set L := Nat.clog 2 (Fintype.card V)
  have h_split : (Finset.powerset G.edgeFinset).card ≤
        (Finset.filter (fun T => ∃ S : Finset V, S.card = 4 * L + 1 ∧ (spanSub G T).IsClique ↑S)
          (Finset.powerset G.edgeFinset)).card +
        (Finset.filter (fun T =>
            ∃ S : Finset V, S.Nonempty ∧ (∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬(spanSub G T).Adj u v) ∧
              (∀ v ∈ S, 4 * L ≤ (S.filter (fun w => G.Adj v w)).card))
          (Finset.powerset G.edgeFinset)).card := by
    rw [← Finset.card_union_add_card_inter]
    refine le_add_right
      (Finset.card_le_card fun T hT => by
        by_cases hT' : ∃ S : Finset V, S.card = 4 * L + 1 ∧ (spanSub G T).IsClique ↑S <;> aesop)
  by_cases hm : G.edgeFinset.card < 2 * L
  · exact absurd (exists_good_edge_subset_of_few_edges G hm) (by aesop)
  · have := clique_bad_total_bound G hn
    have := degen_bad_total_bound G hn hlarge
    norm_num +zetaDelta at *
    linarith [pow_pos (zero_lt_two' ℕ) G.edgeFinset.card]

/-- Combining existence with property extraction. -/
theorem large_N_counting {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hn : 2 ≤ Fintype.card V)
    (hlarge : 4 * Nat.clog 2 (Fintype.card V) < Fintype.card V) :
    ∃ (H : SimpleGraph V) (_ : DecidableRel H.Adj), (∀ u v, H.Adj u v → G.Adj u v) ∧
      H.cliqueNum ≤ 4 * Nat.clog 2 (Fintype.card V) ∧
      (∀ (S : Finset V), S.Nonempty → (∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ H.Adj u v) →
        ∃ v ∈ S, (S.filter (fun w => G.Adj v w)).card < 4 * Nat.clog 2 (Fintype.card V)) := by
  obtain ⟨T, hT⟩ := exists_good_edge_subset G hn hlarge;
  refine' ⟨ spanSub G T, _, _, _, _ ⟩;
  · infer_instance;
  · exact fun u v h => h.2;
  · apply cliqueNum_spanSub_le_of_no_large_clique G T (4 * Nat.clog 2 (Fintype.card V)) hT.2.1;
  · exact fun S hS₁ hS₂ => by push Not at hT; exact hT.2.2 S hS₁ hS₂;

/-- The good spanning subgraph exists for all graphs on `≥ 2` vertices. -/
theorem exists_good_spanning_subgraph {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hn : 2 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V) (_ : DecidableRel H.Adj),
      (∀ u v, H.Adj u v → G.Adj u v) ∧ H.cliqueNum ≤ 4 * Nat.clog 2 (Fintype.card V) ∧
      (∀ (S : Finset V), S.Nonempty → (∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ H.Adj u v) →
        ∃ v ∈ S, (S.filter (fun w => G.Adj v w)).card < 4 * Nat.clog 2 (Fintype.card V)) := by
  by_cases h_large : 4 * Nat.clog 2 ( Fintype.card V ) < Fintype.card V;
  · convert large_N_counting G hn h_large using 1;
  · refine' ⟨ ⊥, _, _, _, _ ⟩ <;> norm_num;
    · infer_instance;
    · refine' le_trans _ ( le_of_not_gt h_large );
      exact csSup_le' fun n hn => by obtain ⟨ s, hs ⟩ := hn; exact hs.card_eq ▸ Finset.card_le_univ _;
    · intro S hS;
      refine' ⟨ hS.choose, hS.choose_spec, lt_of_lt_of_le ( Finset.card_lt_card ( Finset.filter_ssubset.mpr _ ) ) _ ⟩;
      · exact ⟨ hS.choose, hS.choose_spec, by simp +decide ⟩;
      · exact le_trans ( Finset.card_le_univ _ ) ( le_of_not_gt h_large )

/-- Degeneracy colouring restricted to a subset. -/
theorem colorable_on_subset_of_degenerate {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (hd : 0 < d) (S : Finset V)
    (hdegen : ∀ (T : Finset V), T.Nonempty → T ⊆ S →
      ∃ v ∈ T, (T.filter (fun w => G.Adj v w)).card < d) :
    ∃ c : V → Fin d, ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → c u ≠ c v := by
  obtain ⟨c, hc⟩ : ∃ c : S → Fin d, ∀ u : S, ∀ v : S, G.Adj u v → c u ≠ c v := by
    have h_col : (G.comap (fun x : S => x.val)).Colorable d := by
      convert colorable_of_degenerate _ d hd _
      all_goals try infer_instance
      intro T hT
      convert hdegen (Finset.image Subtype.val T)
        _ _ using 1
      · simp +decide [Finset.filter_image, Finset.card_image_of_injective, Function.Injective]
        grind +splitIndPred
      · exact ⟨_, Finset.mem_image_of_mem _ hT.choose_spec⟩
      · exact Finset.image_subset_iff.mpr fun x _ => x.2
    obtain ⟨c, hc⟩ := h_col
    exact ⟨c, fun u v huv => by simpa using hc huv⟩
  exact ⟨fun u => if hu : u ∈ S then c ⟨u, hu⟩ else ⟨0, hd⟩,
    fun u hu v hv huv => by simpa [hu, hv] using hc ⟨u, hu⟩ ⟨v, hv⟩ huv⟩

/-- From cochromatic partition + degeneracy bound → `G` is `(k * d)`-colourable. -/
theorem colorable_of_cochrom_degen {V : Type*} [Fintype V] [DecidableEq V] (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (k d : ℕ) (hd : 0 < d)
    (hk : CochromPartable H k) (hω : H.cliqueNum ≤ d)
    (hdegen : ∀ (S : Finset V), S.Nonempty →
      (∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ H.Adj u v) →
      ∃ v ∈ S, (S.filter (fun w => G.Adj v w)).card < d) :
    G.Colorable (k * d) := by
  obtain ⟨f, hf⟩ := hk
  have h_coloring : ∀ i : Fin k,
      ∃ g : V → Fin d, ∀ u ∈ f ⁻¹' {i}, ∀ v ∈ f ⁻¹' {i}, G.Adj u v → g u ≠ g v := by
    intro i
    by_cases h_clique : H.IsClique (f ⁻¹' {i})
    · have hsize : (Finset.card (Finset.filter (fun v => f v = i) Finset.univ)) ≤ d := by
        refine' le_trans _ hω
        refine' le_csSup _ _
        · exact ⟨Fintype.card V, fun n hn => by
            obtain ⟨s, hs⟩ := hn
            exact hs.card_eq ▸ Finset.card_le_univ _⟩
        · refine' ⟨Finset.filter (fun v => f v = i)
            Finset.univ, _, _⟩ <;> simp_all +decide
          simpa [Set.preimage] using h_clique
      obtain ⟨g, hg⟩ : ∃ g : {v : V | f v = i} → Fin d, Function.Injective g := by
        have hle : Fintype.card {v : V | f v = i} ≤ d := by
          simpa [Fintype.card_subtype] using hsize
        obtain ⟨g⟩ := Trunc.exists_rep (Fintype.truncEquivFinOfCardEq 
          (show Fintype.card {v : V | f v = i} = Fintype.card {v : V | f v = i} from rfl))
        exact ⟨fun x => Fin.castLE hle (g x),
          fun x y hxy => g.injective <| Fin.castLE_injective _ hxy⟩
      use fun u => if hu : f u = i then g ⟨u, hu⟩ else ⟨0, hd⟩
      simp +contextual [hg.eq_iff]
      exact fun u hu v hv huv => by rintro rfl; exact huv.ne rfl
    · have := colorable_on_subset_of_degenerate G d hd (Finset.univ.filter fun v => f v = i) ?_
      · aesop
      · intro T hT hT'
        refine' hdegen T hT _
        intro u hu v hv huv
        specialize hf i
        simp_all +decide [Set.Pairwise]
        grind
  choose g hg using h_coloring
  obtain ⟨c, hc⟩ : ∃ c : V → Fin k × Fin d, ∀ u v, G.Adj u v → c u ≠ c v := by
    use fun u => (f u, g (f u) u)
    intro u v huv; specialize hg (f u) u
    aesop
  use fun u => Fintype.equivFinOfCardEq (by simp +decide) (c u)
  simp +decide
  exact fun { a b } hab => hc a b hab

/-- Connection lemma: `χ(G) ≤ d · ζ(H)`. -/
theorem chromaticNumber_le_of_good_subgraph {V : Type*} [Fintype V] [DecidableEq V] (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (d : ℕ) (hd : 0 < d)
    (hω : H.cliqueNum ≤ d)
    (hdegen : ∀ (S : Finset V), S.Nonempty → (∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ H.Adj u v) →
      ∃ v ∈ S, (S.filter (fun w => G.Adj v w)).card < d) :
    G.chromaticNumber ≤ d * cochromaticNumber H := by
  refine' le_of_forall_le _
  intro c hc
  refine' le_trans hc _
  rw [cochromaticNumber, ENat.mul_iInf]
  refine' le_iInf fun n => _
  by_cases hn : CochromPartable H n <;>
    simp +decide [hn]
  · have :=
      colorable_of_cochrom_degen G H n d hd
        hn hω hdegen
    simpa [mul_comm] using this.chromaticNumber_le
  · simp +decide [ENat.mul_top, hd.ne']

/-- Cochromatic invariance for subgraphs via clique embeddings. -/
theorem exists_subgraph_from_clique_cochrom {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) (hn : n ≤ G.cliqueNum)
    (R : SimpleGraph (Fin n)) [DecidableRel R.Adj] :
    ∃ (S : Set V) (_ : Fintype S) (H : SimpleGraph S) (_ : DecidableEq S) (_ : DecidableRel H.Adj),
      (∀ (u v : S), H.Adj u v → G.Adj ↑u ↑v) ∧ Fintype.card S = n ∧ cochromaticNumber H = cochromaticNumber R := by
  have h_exists_clique : ∃ S : Finset V, S.card = n ∧ G.IsClique S := by
    -- Since $n \leq \omega(G)$, there exists a clique of size $n$ in $G$.
    have h_clique : ∃ S : Finset V, G.IsClique S ∧ S.card ≥ n := by
      contrapose! hn;
      refine' lt_of_le_of_lt ( csSup_le' _ ) _;
      exact n - 1;
      · rintro m ⟨ s, hs ⟩;
        exact Nat.le_sub_one_of_lt ( by simpa [ hs.card_eq ] using hn s hs.isClique );
      · exact Nat.pred_lt ( ne_bot_of_gt ( hn ∅ ( by simp +decide ) ) );
    obtain ⟨ S, hS₁, hS₂ ⟩ := h_clique;
    obtain ⟨ T, hT ⟩ := Finset.exists_subset_card_eq hS₂;
    exact ⟨ T, hT.2, fun u hu v hv huv => hS₁ ( hT.1 hu ) ( hT.1 hv ) huv ⟩;
  obtain ⟨S, hS_card, hS_clique⟩ := h_exists_clique
  obtain ⟨f, hf⟩ : ∃ f : Fin n ≃ S, True := by
    exact ⟨ Fintype.equivOfCardEq ( by simp +decide [ hS_card ] ), trivial ⟩;
  refine' ⟨ S, inferInstance, R.comap f.symm, inferInstance, inferInstance, _, _, _ ⟩ <;> simp_all +decide;
  · intro a ha b hb hab; have := hS_clique ha hb; aesop;
  · convert cochromaticNumber_comap_equiv R f.symm

/-- Extension lemma: colour clique fibres, assign independent fibres their own colour. -/
theorem colorable_of_cochrom_and_induce {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) (f : V → Fin n)
    (hf : ∀ i, G.IsClique (f ⁻¹' {i}) ∨ G.IsIndepSet (f ⁻¹' {i}))
    (S : Set V) [DecidablePred (· ∈ S)]
    (hS : ∀ v, v ∈ S ↔ G.IsClique (f ⁻¹' {f v})) (c : ℕ) (hc : (G.induce S).Colorable c) :
    G.Colorable (c + n) := by
  obtain ⟨col, h_col⟩ := hc
  use fun v => if hv : v ∈ S then Fin.castAdd n (col ⟨v, hv⟩) else Fin.natAdd c (f v)
  intro a b hab
  split_ifs <;> simp_all +decide [SimpleGraph.adj_comm]
  · exact h_col a (hS a |>.1 ‹_›) b (hS b |>.1 ‹_›) hab
  · simp +decide [Fin.ext_iff]
    linarith [Fin.is_lt (col ⟨a, by assumption⟩), Fin.is_lt (f b)]
  · simp +decide [Fin.ext_iff]
    linarith [Fin.is_lt (col ⟨b, by assumption⟩), Fin.is_lt (f a)]
  · contrapose! h_col
    have := hf (f a)
    simp_all [SimpleGraph.isClique_iff, SimpleGraph.isIndepSet_iff]
    exact False.elim (this (by aesop) (by aesop) (by aesop) hab)

/-- Clique fibres have total size `≤ n · ω(G)`. -/
theorem card_clique_fibers_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) (f : V → Fin n) (S : Set V)
    [Fintype S] (hS : ∀ v, v ∈ S ↔ G.IsClique (f ⁻¹' {f v})) :
    Fintype.card S ≤ n * G.cliqueNum := by
  have h_le : ∀ i, (Fintype.card {v ∈ S | f v = i}) ≤ G.cliqueNum := by
    intro i
    by_cases hi : G.IsClique (f ⁻¹' {i})
    · have h_sub :
          Fintype.card {v ∈ S | f v = i} ≤ Fintype.card {v : V // f v = i} :=
        Fintype.card_le_of_embedding
          ⟨fun v => ⟨v.1, v.2.2⟩,
            fun _ _ h => Subtype.ext (congrArg (fun v : {v : V // f v = i} => (v : V)) h)⟩
      have h_fiber_clique :
          G.IsClique (Finset.univ.filter fun v => f v = i) := by
        intro u hu v hv huv
        exact hi (by simpa using hu) (by simpa using hv) huv
      exact le_trans h_sub (by
        rw [Fintype.card_subtype]
        exact h_fiber_clique.card_le_cliqueNum)
    · exact le_trans
        (le_of_eq (Fintype.card_eq_zero_iff.mpr ⟨fun v => by specialize hS v; aesop⟩)) (Nat.zero_le _)
  have h_sum : Fintype.card S = ∑ i : Fin n, Fintype.card {v ∈ S | f v = i} := by
    simp +decide only [Fintype.card_ofFinset, Finset.card_filter]
    rw [Finset.sum_comm]; aesop
  exact h_sum ▸ le_trans (Finset.sum_le_sum fun _ _ => h_le _) (by simp +decide)

/-- **Lemma 2.1** (Cochromatic Partition Reduction): from a cochromatic partition with `n` parts, the 
clique parts have bounded total size and `χ(G) ≤ χ(G[clique union]) + n`. -/
theorem exists_clique_union_subgraph {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) (hn : CochromPartable G n) :
    ∃ (S : Set V) (_ : Fintype S) (_ : DecidableEq S) (_ : DecidableRel (G.induce S).Adj),
      (∀ u : S, ∀ v : S, (G.induce S).Adj u v → G.Adj (↑u) (↑v)) ∧ Fintype.card S ≤ n * G.cliqueNum ∧
      ∀ c : ℕ, (G.induce S).Colorable c → G.Colorable (c + n) := by
  obtain ⟨f, hf⟩ := hn
  let S : Set V := {v | G.IsClique (f ⁻¹' {f v})}
  haveI hSdec : DecidablePred (· ∈ S) := fun v => Classical.dec _
  haveI hSfin : Fintype S := Set.Finite.fintype (Set.toFinite S)
  refine ⟨S, hSfin, Subtype.instDecidableEq, inferInstance, ?_, ?_, ?_⟩
  · intro u v hadj
    simp [SimpleGraph.induce, SimpleGraph.comap] at hadj
    exact hadj
  · exact @card_clique_fibers_le V _ _ G _ n f S hSfin (fun v => Iff.rfl)
  · intro c hc
    exact colorable_of_cochrom_and_induce G n f hf S (fun v => Iff.rfl) c hc

/-- **Random Subgraph Lemma** (Lemma 2.2, AKS 1997): for any graph `G` on `≥ 2` vertices, there exists a spanning
subgraph `H` with `χ(G) ≤ 4⌈log₂|V|⌉ · ζ(H)`. -/
theorem exists_spanning_subgraph_chi_cochrom {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hn : 2 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V) (_ : DecidableRel H.Adj), (∀ u v, H.Adj u v → G.Adj u v) ∧
      G.chromaticNumber ≤ 4 * Nat.clog 2 (Fintype.card V) * cochromaticNumber H := by
  set L := Nat.clog 2 (Fintype.card V)
  by_cases hω : G.cliqueNum ≤ 4 * L
  · refine ⟨G, inferInstance, fun u v h => h, ?_⟩
    calc G.chromaticNumber
        ≤ cochromaticNumber G * G.cliqueNum :=
          chi_le_cochromaticNumber_mul_cliqueNum' G
      _ ≤ cochromaticNumber G * (4 * L) := by
          gcongr; exact_mod_cast hω
      _ = (4 * L) * cochromaticNumber G := by ring
  · push Not at hω
    obtain ⟨H, hdecH, hHG, hωH, hdegen⟩ := exists_good_spanning_subgraph G hn
    have hL_pos : 0 < L := Nat.clog_pos (by omega) (by omega)
    exact ⟨H, hdecH, hHG, chromaticNumber_le_of_good_subgraph G H (4 * L) (by omega) hωH hdegen⟩

/-- Extract a `CochromPartable` witness. -/
theorem exists_cochromPartable_nat {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ k : ℕ, cochromaticNumber G = ↑k ∧ CochromPartable G k := by
  have h_ne : {n : ℕ | CochromPartable G n}.Nonempty := ⟨Fintype.card V, cochromPartable_card G⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, CochromPartable G k ∧ k = cochromaticNumber G := by
    convert Nat.sInf_mem h_ne
    constructor <;> intro h
    · exact Nat.sInf_mem h_ne
    · refine' ⟨_, h, le_antisymm _ _⟩
      · refine' le_ciInf fun n => _
        by_cases hn : CochromPartable G n <;> simp +decide [hn]
        exact Nat.sInf_le hn
      · exact cochromaticNumber_le_of_cochromPartable G h
  exact ⟨k, hk.2.symm, hk.1⟩

/-- `χ(G) ≥ 2` implies `ω(G) ≥ 2`. -/
private theorem cliqueNum_ge_two_of_chi_ge_two {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) (hchi : G.chromaticNumber = ↑m)
    (hm : 2 ≤ m) : 2 ≤ G.cliqueNum := by
  by_contra h
  push Not at h
  have hω1 : G.cliqueNum ≤ 1 := by omega
  have h_col1 : G.Colorable 1 := by
    use fun _ => ⟨0, by omega⟩
    intro a b hab
    exfalso
    have h2 : 2 ≤ G.cliqueNum := by
      refine le_csSup ?_ ⟨{a, b}, ?_⟩
      · exact ⟨Fintype.card V, fun n hn => by
          obtain ⟨s, hs⟩ := hn
          exact hs.card_eq ▸ Finset.card_le_univ _⟩
      · constructor
        · intro u hu v hv huv
          simp at hu hv
          rcases hu with rfl | rfl <;>
            rcases hv with rfl | rfl <;> first
              | exact absurd rfl huv
              | exact hab
              | exact hab.symm
        · simp [G.ne_of_adj hab]
    omega
  have h2 : G.chromaticNumber ≤ 1 := mod_cast h_col1.chromaticNumber_le
  rw [hchi] at h2
  norm_cast at h2
  omega

set_option maxHeartbeats 400000 in
/-- Combined: Lemma 2.1 + random subgraph. -/
theorem exists_subgraph_large_cochrom_of_small_omega' {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) (hchi : G.chromaticNumber = ↑m)
    (hm : 2 ≤ m) (hω : G.cliqueNum < m) :
    ∃ (S : Set V) (_ : Fintype S) (H : SimpleGraph S) (_ : DecidableEq S) (_ : DecidableRel H.Adj),
      (∀ (u v : S), H.Adj u v → G.Adj ↑u ↑v) ∧ (m : ℕ∞) ≤ 16 * Nat.clog 2 m * cochromaticNumber H := by
  set L := Nat.clog 2 m with hL_def
  have hL_pos : 0 < L := Nat.clog_pos (by omega) (by omega)
  obtain ⟨ζ, hζ_eq, hζ_part⟩ := exists_cochromPartable_nat G
  by_cases hζ_large : m ≤ L * ζ
  · -- ζ ≥ m/L: take H = G via Set.univ
    refine' ⟨Set.univ, inferInstance, G.induce Set.univ, inferInstance, inferInstance, by simp +decide, _⟩
    have h_eq : cochromaticNumber (induce Set.univ G) = cochromaticNumber G := by
      unfold cochromaticNumber
      congr! 3
      constructor <;> rintro ⟨f, hf⟩
      · use fun v => f ⟨v, trivial⟩
        simp_all +decide [Set.Pairwise, SimpleGraph.IsClique, SimpleGraph.IsIndepSet]
      · use fun v => f v
        simp_all +decide [Set.Pairwise, SimpleGraph.IsClique, SimpleGraph.IsIndepSet]
    rw [h_eq, hζ_eq]
    norm_cast
    nlinarith
  · -- ζ < m/L: apply Lemma 2.1 + random subgraph
    push Not at hζ_large
    obtain ⟨S, hfinS, hdeqS, hdecS, hsub, hcard, hcolor⟩ := exists_clique_union_subgraph G ζ hζ_part
    have hω2 : 2 ≤ G.cliqueNum := cliqueNum_ge_two_of_chi_ge_two G m hchi hm
    have hm3 : 3 ≤ m := by
      by_contra h
      push Not at h
      interval_cases m
      exact absurd (show G.cliqueNum < 2 from hω) (not_lt.mpr hω2)
    have hL2 : 2 ≤ L := by
      rw [hL_def]
      calc 2 = Nat.clog 2 3 := by decide
        _ ≤ Nat.clog 2 m :=
          Nat.clog_mono_right 2 hm3
    have hS_lower : m ≤ @Fintype.card S hfinS + ζ := by
      have hcol : G.Colorable (@Fintype.card S hfinS + ζ) :=
        hcolor _ (@colorable_of_fintype S (G.induce S) hfinS)
      have := hcol.chromaticNumber_le
      rw [hchi] at this
      exact_mod_cast this
    have hζ_bound : ζ ≤ m - 2 := by
      have : 2 * ζ ≤ L * ζ := Nat.mul_le_mul_right _ hL2
      omega
    have hS_ge : 2 ≤ @Fintype.card S hfinS := by omega
    obtain ⟨H, hdecH, hHsub, hchi_bound⟩ :=
      @exists_spanning_subgraph_chi_cochrom S hfinS hdeqS (G.induce S) hdecS hS_ge
    refine ⟨S, hfinS, H, hdeqS, hdecH, fun u v hadj => hsub u v (hHsub u v hadj), ?_⟩
    have h_m_le : (m : ℕ∞) ≤ (induce S G).chromaticNumber + ζ := by
      rw [← hchi]
      refine' ciInf_le_of_le _ _ _
      · exact ⟨0, Set.forall_mem_range.2 fun n => zero_le _⟩
      · exact (induce S G).chromaticNumber.toNat + ζ
      · refine' le_trans (ciInf_le _ _) _
        · exact ⟨0, Set.forall_mem_range.2 fun _ => zero_le _⟩
        · convert hcolor _ _
          exact colorable_chromaticNumber_of_fintype (induce S G)
        · cases h : (induce S G).chromaticNumber <;> aesop
    have h_combined : (m : ℕ∞) ≤ 4 * (2 * L) * cochromaticNumber H + ζ := by
      refine le_trans h_m_le (add_le_add ?_ le_rfl)
      refine hchi_bound.trans ?_
      gcongr
      norm_cast
      refine' Nat.le_trans (Nat.clog_mono_right _ _) _
      · exact m ^ 2
      · nlinarith
      · refine' Nat.le_of_lt_succ (Nat.lt_succ_of_le (Nat.le_trans (Nat.clog_mono_right _ _) _))
        · exact 2 ^ (2 * L)
        · rw [pow_mul']
          gcongr
          exact Nat.le_pow_clog (by decide) _
        · rw [Nat.clog_pow]; norm_num
    rcases k : cochromaticNumber H with
      _ | _ | k <;> simp_all +decide
    · change (m : ℕ∞) ≤ (16 * (Nat.clog 2 m : ℕ∞)) * (⊤ : ℕ∞)
      rw [ENat.mul_top]
      · exact (le_top : (m : ℕ∞) ≤ (⊤ : ℕ∞))
      · norm_num
        omega
    · erw [WithTop.coe_le_coe] at *
      norm_num at *; nlinarith
    · erw [WithTop.coe_le_coe] at *
      by_cases hζ : ζ ≤ m / 2
      · nlinarith [Nat.div_mul_le_self m 2]
      · rcases m with _ | _ | m <;>
          simp_all +arith +decide
        contrapose! hζ_large
        have h_clog : Nat.clog 2 (m + 2) ≥ 2 := by
          by_cases hm : m < 2
          · grind
          · exact Nat.le_trans (by decide) (Nat.clog_mono_right _ (Nat.add_le_add_right (le_of_not_gt hm) 2))
        nlinarith only [hζ, hζ_large, h_clog, Nat.div_add_mod m 2, Nat.mod_lt m two_pos]

/-! ## Main Theorem (internal version with `Nat.clog`) -/

private theorem erdos_760_clog :
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ),
      G.chromaticNumber = ↑m → 2 ≤ m →
    ∃ (S : Set V) (_ : Fintype S) (H : SimpleGraph S) (_ : DecidableEq S) (_ : DecidableRel H.Adj),
      (∀ (u v : S), H.Adj u v → G.Adj ↑u ↑v) ∧ (m : ℕ∞) ≤ 16 * Nat.clog 2 m * cochromaticNumber H := by
  intro V _ _ G _ m hchi hm
  set L := Nat.clog 2 m
  have hL_pos : 0 < L := Nat.clog_pos (by omega) (by omega)
  by_cases hω : m ≤ G.cliqueNum
  · -- Case 1: ω(G) ≥ m
    obtain ⟨H₀, hdecH₀, _, hbound⟩ :=
      @exists_spanning_subgraph_chi_cochrom (Fin m) _ _ (⊤ : SimpleGraph (Fin m))
        (Classical.decRel _) (by simp [Fintype.card_fin]; omega)
    simp only [chromaticNumber_top, Fintype.card_fin] at hbound
    obtain ⟨S, hfinS, H, hdeqS, hdecH, hsub, _, hcochrom⟩ :=
      @exists_subgraph_from_clique_cochrom V _ _ G _ m hω H₀ hdecH₀
    refine ⟨S, hfinS, H, hdeqS, hdecH, hsub, ?_⟩
    rw [hcochrom]
    calc (m : ℕ∞)
        ≤ ↑(4 * L) * cochromaticNumber H₀ := by
          exact_mod_cast hbound
      _ ≤ ↑(16 * L) * cochromaticNumber H₀ := by
          gcongr; omega
  · -- Case 2: ω(G) < m
    push Not at hω
    exact exists_subgraph_large_cochrom_of_small_omega' G m hchi hm hω

private theorem clog_le_two_mul_log (m : ℕ) (hm : 2 ≤ m) : Nat.clog 2 m ≤ 2 * Nat.log 2 m := by
  have h1 : Nat.clog 2 m ≤ Nat.log 2 m + 1 :=
    Nat.clog_le_of_le_pow (le_of_lt (Nat.lt_pow_succ_log_self (by omega) m))
  have h2 : 1 ≤ Nat.log 2 m := Nat.log_pos (by omega) hm
  omega

/-! ## Main Theorem (explicit bound) -/

/-- **Erdős Problem 760 (explicit bound)**: If `G` has `χ(G) = m ≥ 2`, then `G` contains
a subgraph `H` with `ζ(H) ≥ m / (32 · ⌊log₂ m⌋)`, i.e. `m ≤ 32 · ⌊log₂ m⌋ · ζ(H)`. -/
theorem erdos_760_explicit :
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ),
      G.chromaticNumber = ↑m → 2 ≤ m →
    ∃ (S : Set V) (H : SimpleGraph S),
      (∀ (u v : S), H.Adj u v → G.Adj ↑u ↑v) ∧
      (m : ℕ∞) ≤ 32 * Nat.log 2 m * cochromaticNumber H := by
  intro V _ _ G _ m hchi hm
  obtain ⟨S, _, H, _, _, hsub, hbound⟩ := erdos_760_clog V G m hchi hm
  refine ⟨S, H, hsub, hbound.trans ?_⟩
  apply mul_le_mul_left
  have h : 16 * Nat.clog 2 m ≤ 32 * Nat.log 2 m := by
    have := clog_le_two_mul_log m hm; nlinarith
  exact_mod_cast h

/-! ## Main Theorem (original asymptotic form) -/

/-- **Erdős Problem 760 (original form)**:
If `G` is a graph with chromatic number `χ(G) = m`, then `G` must contain a subgraph `H` with
`ζ(H) ≫ m / log m`.

Formally, there exists a universal constant `C > 0` such that for every finite simple graph `G`
with `χ(G) = m ≥ 2`, the graph `G` contains a subgraph `H` satisfying
`m ≤ C · ⌊log₂ m⌋ · ζ(H)`, i.e. `ζ(H) ≥ m / (C · log₂ m)`. We witness `C = 32`. -/
theorem erdos_760 : ∃ C : ℕ, 0 < C ∧
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ),
      G.chromaticNumber = ↑m → 2 ≤ m →
    ∃ (S : Set V) (H : SimpleGraph S),
      (∀ (u v : S), H.Adj u v → G.Adj ↑u ↑v) ∧
      (m : ℕ∞) ≤ C * Nat.log 2 m * cochromaticNumber H :=
  ⟨32, by omega, erdos_760_explicit⟩

#print axioms erdos_760
-- 'Erdos760.SimpleGraph.erdos_760' depends on axioms: [propext,
-- Classical.choice,
-- Quot.sound,
-- clique_bad_total_bound._native.native_decide.ax_1_5]

end SimpleGraph

end

end Erdos760
