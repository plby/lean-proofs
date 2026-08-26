/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- No license was supplied with the linked formalization.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 716, the Ruzsa–Szemerédi (6,3)-theorem.
Informal authors: Imre Z. Ruzsa, Endre Szemerédi.
Formal authors: Aristotle, JoshuaB.
The proof uses Mathlib's triangle-removal and tripartite-graph machinery
by Yaël Dillies and Bhavik Mehta.
Source: https://www.erdosproblems.com/716#post-7096
Original Lean/Mathlib version: 4.28.0, as specified in the linked editor project.
The full editor URL is preserved as JoshuaB_716 in data/urls.yaml.
-/
import ErdosProblems.Erdos716.Definitions

open Finset Filter SimpleGraph SimpleGraph.TripartiteFromTriangles

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Erdos716

variable {n : ℕ}

/-- The "linear part" of `H`: the edges that share at most one vertex with every other edge. -/
def linPart (H : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  H.filter (fun e => ∀ e' ∈ H, e ≠ e' → (e ∩ e').card ≤ 1)
/-- The triangle-index set associated to a hypergraph: the sorted triples of its edges. -/
def triIdx (H : Finset (Finset (Fin n))) : Finset (Fin n × Fin n × Fin n) :=
  Finset.univ.filter
    (fun p => p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ ({p.1, p.2.1, p.2.2} : Finset (Fin n)) ∈ H)
@[simp] lemma mem_triIdx {H : Finset (Finset (Fin n))} {p : Fin n × Fin n × Fin n} :
    p ∈ triIdx H ↔ p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ ({p.1, p.2.1, p.2.2} : Finset (Fin n)) ∈ H := by
  classical
  simp [triIdx]
lemma linPart_subset (H : Finset (Finset (Fin n))) : linPart H ⊆ H := filter_subset _ _
lemma linPart_linear {H : Finset (Finset (Fin n))} {e : Finset (Fin n)} (he : e ∈ linPart H)
    {e' : Finset (Fin n)} (he' : e' ∈ H) (hne : e ≠ e') : (e ∩ e').card ≤ 1 := by
  classical
  rw [linPart, mem_filter] at he
  exact he.2 e' he' hne
/-
The number of triangle indices equals the number of edges, for a `3`-uniform hypergraph.
-/
lemma card_triIdx {H : Finset (Finset (Fin n))} (h3 : ∀ e ∈ H, e.card = 3) :
    (triIdx H).card = H.card := by
  classical
  refine' Finset.card_bij ( fun p hp => { p.1, p.2.1, p.2.2 } ) _ _ _;
  · aesop;
  · simp +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ];
    grind;
  · intro e he;
    -- Since $e$ is a 3-element subset of $\{0, 1, ..., n-1\}$, we can order its elements as $a < b < c$.
    obtain ⟨a, b, c, ha, hb, hc, habc⟩ : ∃ a b c : Fin n, a < b ∧ b < c ∧ e = {a, b, c} := by
      have := Finset.card_eq_three.mp ( h3 e he );
      obtain ⟨ x, y, z, hxy, hxz, hyz, rfl ⟩ := this;
      cases lt_or_gt_of_ne hxy <;> cases lt_or_gt_of_ne hxz <;> cases lt_or_gt_of_ne hyz <;> simp +decide [ *, Finset.ext_iff ];
      all_goals repeat { exact ⟨ _, _, by assumption, _, by assumption, by tauto ⟩ };
      · exact ⟨ x, y, by assumption, z, by assumption, by tauto ⟩;
      · grind;
      · grind;
      · grind;
    exact ⟨ ⟨ a, b, c ⟩, by aesop ⟩
/-
`triIdx (linPart H)` has edge-disjoint explicit triangles.
-/
lemma explicitDisjoint_triIdx (H : Finset (Finset (Fin n))) :
    ExplicitDisjoint (triIdx (linPart H)) := by
  classical
  constructor;
  · simp_all +decide [ linPart ];
    grind +splitIndPred;
  · intro a b c b' h₁ h₂;
    have h_eq : ({a, b, c} : Finset (Fin n)) ∈ linPart H ∧ ({a, b', c} : Finset (Fin n)) ∈ linPart H := by
      unfold triIdx at *; aesop;
    have := linPart_linear h_eq.1 ( show { a, b', c } ∈ H from linPart_subset _ h_eq.2 ) ; simp_all +decide ;
    grind;
  · simp +contextual [ triIdx ];
    intro a b c c' hab hbc h₁ hbc' h₂; have := linPart_linear h₁ ( Finset.mem_of_mem_filter _ h₂ ) ; simp_all +decide [ Finset.ext_iff ] ;
    specialize this c ; simp_all +decide;
    grind +splitImp
/-
If `H` has no `3` distinct edges spanning `≤ 6` vertices, then `triIdx H` has no accidental
triangles.
-/
lemma noAccidental_triIdx {H : Finset (Finset (Fin n))} (h : ¬ ThreeEdgesIn6 H) :
    NoAccidental (triIdx H) := by
  classical
  -- By contradiction, assume there are three edges in H that share at most 6 vertices.
  by_contra h_contra;
  obtain ⟨a, b, c, a', b', c', habc, habc', hbc, hac⟩ : ∃ a b c a' b' c', (a', b, c) ∈ triIdx H ∧ (a, b', c) ∈ triIdx H ∧ (a, b, c') ∈ triIdx H ∧ ¬(a' = a ∨ b' = b ∨ c' = c) := by
    contrapose! h_contra;
    constructor;
    grind +locals;
  refine h ⟨ { a', b, c }, ?_, { a, b', c }, ?_, { a, b, c' }, ?_, ?_, ?_, ?_, ?_ ⟩ <;> simp_all +decide;
  · intro t; simp_all +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ] ;
    grind;
  · simp_all +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ];
    grind;
  · simp_all +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ];
    grind;
  · grind
/-
An edge-disjoint family of triangle indices has at most `card α * card β` elements.
-/
lemma card_le_of_explicitDisjoint {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [Fintype α] [Fintype β] [Fintype γ] (t : Finset (α × β × γ)) [ExplicitDisjoint t] :
    t.card ≤ Fintype.card α * Fintype.card β := by
  classical
  have h_inj : ∀ (p q : α × β × γ), p ∈ t → q ∈ t → p.1 = q.1 → p.2.1 = q.2.1 → p = q := by
    cases ‹ExplicitDisjoint t›;
    grind;
  have h_card : Finset.card (Finset.image (fun p : α × β × γ => (p.1, p.2.1)) t) ≤ Fintype.card α * Fintype.card β := by
    exact le_trans ( Finset.card_le_univ _ ) ( by simp +decide );
  rwa [ Finset.card_image_of_injOn fun p hp q hq h => h_inj p q hp hq ( by injection h ) ( by injection h ) ] at h_card
/-
The edges of `H` not in its linear part are few: at most `n` of them.
-/
lemma card_sdiff_linPart_le {H : Finset (Finset (Fin n))} (h3 : ∀ e ∈ H, e.card = 3)
    (h : ¬ ThreeEdgesIn6 H) : (H \ linPart H).card ≤ n := by
  classical
  -- For each edge $e \in B$, pick a witness $e' \in H$ with $e \neq e'$ and $2 \leq (e \cap e').card$.
  -- Then $e \setminus e'$ is a singleton, and we can define $\phi(e)$ to be its unique element.
  have h_phi : ∀ e ∈ H \ linPart H, ∃ v ∈ e, ∀ f ∈ H, v ∈ f → f = e := by
    intro e he
    obtain ⟨e', he', hne, hcard⟩ : ∃ e' ∈ H, e ≠ e' ∧ 2 ≤ (e ∩ e').card := by
      unfold linPart at he; aesop;
    -- Since $e$ and $e'$ are distinct and $(e \cup e').card = 4$, any other edge $f \in H$ that intersects $e \cup e'$ must be equal to $e$ or $e'$.
    have h_inter : ∀ f ∈ H, f ∩ (e ∪ e') ≠ ∅ → f = e ∨ f = e' := by
      intros f hf h_inter_nonempty
      by_contra h_contra
      push Not at h_contra;
      refine' h ⟨ e, by aesop, e', by aesop, f, by aesop, hne, h_contra.1.symm, h_contra.2.symm, _ ⟩;
      have he3 := h3 e (Finset.mem_sdiff.mp he).1
      have he'3 := h3 e' he'
      have hf3 := h3 f hf
      have hpair := Finset.card_union_add_card_inter e e'
      have htriple := Finset.card_union_add_card_inter f (e ∪ e')
      have hpos : 0 < (f ∩ (e ∪ e')).card :=
        Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h_inter_nonempty)
      rw [Finset.union_comm f (e ∪ e')] at htriple
      omega
    -- Since $e$ and $e'$ are distinct and $(e \cup e').card = 4$, there exists a vertex $v \in e$ such that $v \notin e'$.
    obtain ⟨v, hv⟩ : ∃ v ∈ e, v ∉ e' := by
      exact Finset.not_subset.mp fun h => hne <| Finset.eq_of_subset_of_card_le h <| by linarith [ h3 e <| Finset.mem_sdiff.mp he |>.1, h3 e' he' ] ;
    exact ⟨ v, hv.1, fun f hf hvf => Or.resolve_right ( h_inter f hf ( Finset.Nonempty.ne_empty ⟨ v, Finset.mem_inter_of_mem hvf ( Finset.mem_union_left _ hv.1 ) ⟩ ) ) fun h => hv.2 <| h ▸ hvf ⟩;
  choose! v hv₁ hv₂ using h_phi;
  have h_inj : Function.Injective (fun e : {e : Finset (Fin n) // e ∈ H \ linPart H} => v e e.2) := by
    intro e₁ e₂ h_eq;
    grind;
  simpa using Finset.card_le_univ ( Finset.image ( fun e : { e : Finset ( Fin n ) // e ∈ H \ linPart H } => v e e.2 ) Finset.univ ) |> le_trans ( by rw [ Finset.card_image_of_injective _ h_inj ] ; simp +decide )
/-
The linear part has at most `n²` edges.
-/
lemma linPart_card_le_sq {H : Finset (Finset (Fin n))} (h3 : ∀ e ∈ H, e.card = 3) :
    ((linPart H).card : ℝ) ≤ (n : ℝ) ^ 2 := by
  classical
  norm_cast;
  convert card_le_of_explicitDisjoint ( triIdx ( linPart H ) ) using 1;
  · exact Eq.symm ( card_triIdx fun e he => h3 e ( Finset.mem_filter.mp he |>.1 ) );
  · norm_num [ sq ];
  · -- Apply the lemma that states the triangle indices of the linear part are explicitly disjoint.
    apply explicitDisjoint_triIdx
/-
The key dichotomy coming from the triangle removal lemma applied to the linear part.
-/
lemma main_dichotomy {H : Finset (Finset (Fin n))} {ε : ℝ}
    (h3 : ∀ e ∈ H, e.card = 3) (h : ¬ ThreeEdgesIn6 H) :
    triangleRemovalBound ε * (((3 * n : ℕ) : ℝ)) ^ 3 ≤ ((linPart H).card : ℝ) ∨
      ((linPart H).card : ℝ) < ε * (((3 * n : ℕ) : ℝ)) ^ 2 := by
  classical
  by_contra h_contra;
  obtain ⟨t, ht⟩ : ∃ t : Finset (Fin n × Fin n × Fin n), t = triIdx (linPart H) ∧ ExplicitDisjoint t ∧ NoAccidental t ∧ (t.card : ℝ) ≥ ε * ((3 * n : ℕ) : ℝ) ^ 2 := by
    refine' ⟨ _, rfl, explicitDisjoint_triIdx _, noAccidental_triIdx _, _ ⟩;
    · exact fun h' => h <| by obtain ⟨ e₁, he₁, e₂, he₂, e₃, he₃, hne₁₂, hne₁₃, hne₂₃, hcard ⟩ := h'; exact ⟨ e₁, linPart_subset _ he₁, e₂, linPart_subset _ he₂, e₃, linPart_subset _ he₃, hne₁₂, hne₁₃, hne₂₃, hcard ⟩ ;
    · rw [ card_triIdx ];
      · exact le_of_not_gt fun h => h_contra <| Or.inr h;
      · exact fun e he => h3 e <| Finset.mem_filter.mp he |>.1;
  obtain ⟨ht_eq, ht_explicit, ht_no_accidental, ht_card⟩ := ht;
  have h_far_from_triangle_free : (graph t).FarFromTriangleFree ε := by
    let := ht_explicit
    apply farFromTriangleFree
    simpa only [Fintype.card_fin, show n + n + n = 3 * n by omega,
      Nat.cast_pow] using ht_card
  have h_card_cliqueFinset : (triangleRemovalBound ε) * ((Fintype.card (Fin n ⊕ Fin n ⊕ Fin n)) : ℝ) ^ 3 ≤ (Finset.card (SimpleGraph.cliqueFinset (graph t) 3)) := by
    convert h_far_from_triangle_free.le_card_cliqueFinset using 1;
  have h_card_t_eq : t.card = (linPart H).card := by
    rw [ht_eq];
    apply card_triIdx;
    exact fun e he => h3 e <| Finset.mem_filter.mp he |>.1;
  simp_all +decide [ Fintype.card_sum ];
  linarith
/-
For every `δ > 0`, eventually every `𝓕`-free `3`-uniform hypergraph on `Fin n` has at most
`δ n²` edges.
-/
lemma exists_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ H : Finset (Finset (Fin n)),
      (∀ e ∈ H, e.card = 3) → ¬ ThreeEdgesIn6 H → (H.card : ℝ) ≤ δ * (n : ℝ) ^ 2 := by
  classical
  -- Set `ε := δ / 18`, so `0 < ε` and `9 * ε = δ / 2`.
  set ε := δ / 18 with hε
  have hε_pos : 0 < ε := by
    positivity
  have h9ε : 9 * ε = δ / 2 := by
    ring;
  -- Let `c := triangleRemovalBound ε`, which is `> 0` by `triangleRemovalBound_pos`.
  obtain ⟨c, hc_pos, hc⟩ : ∃ c > 0, ∀ n : ℕ, ∀ H : Finset (Finset (Fin n)), (∀ e ∈ H, e.card = 3) → ¬ThreeEdgesIn6 H → (linPart H).card < ε * (3 * n : ℝ) ^ 2 ∨ c * (3 * n : ℝ) ^ 3 ≤ (linPart H).card := by
    use triangleRemovalBound ε, by
      grind +suggestions;
    exact fun n H h3 h => Classical.or_iff_not_imp_left.2 fun h' => by simpa using main_dichotomy h3 h |> Or.resolve_right <| by simpa using h';
  -- Choose `N := max (⌈1 / (27 * c)⌉₊ + 1) (⌈2 / δ⌉₊ + 1)`.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, c * (3 * n : ℝ) ^ 3 > (n : ℝ) ^ 2 := by
    exact ⟨ ⌊c⁻¹⌋₊ + 1, fun n hn => by nlinarith [ Nat.lt_of_floor_lt hn, inv_pos.2 hc_pos, mul_inv_cancel₀ hc_pos.ne', show ( n : ℝ ) ^ 3 ≥ n ^ 2 by exact pow_le_pow_right₀ ( by norm_cast; linarith ) ( by norm_num ) ] ⟩;
  use N + ⌈2 / δ⌉₊ + 1;
  intro n hn H h3 h; specialize hc n H h3 h; rcases hc with h | h <;> simp_all +decide ;
  · have h_card_sdiff : (H \ linPart H).card ≤ n := by
      apply card_sdiff_linPart_le h3 ‹_›;
    have h_card_H : (H.card : ℝ) = (linPart H).card + (H \ linPart H).card := by
      rw_mod_cast [ ← Finset.card_union_of_disjoint ( Finset.disjoint_sdiff ), Finset.union_sdiff_of_subset ( linPart_subset H ) ];
    nlinarith [ show ( n : ℝ ) ≥ ⌈2 / δ⌉₊ + 1 by norm_cast; linarith, Nat.le_ceil ( 2 / δ ), mul_div_cancel₀ 2 hδ.ne', show ( # ( H \ linPart H ) : ℝ ) ≤ n by norm_cast ];
  · exact absurd h ( by linarith [ hN n ( by linarith ), linPart_card_le_sq h3 ] )
lemma ex3_le_of_bound {n : ℕ} {b : ℝ}
    (hb : ∀ H : Finset (Finset (Fin n)),
      (∀ e ∈ H, e.card = 3) → ¬ ThreeEdgesIn6 H → (H.card : ℝ) ≤ b) :
    (ex3 n : ℝ) ≤ b := by
  classical
  obtain ⟨H₀, hH₀⟩ : ∃ H₀ ∈ Finset.filter (fun H : Finset (Finset (Fin n)) => (∀ e ∈ H, Finset.card e = 3) ∧ ¬ ThreeEdgesIn6 H) (Finset.univ : Finset (Finset (Finset (Fin n)))), (H₀.card : ℝ) = ex3 n := by
    obtain ⟨H₀, hH₀⟩ : ∃ H₀ ∈ Finset.filter (fun H : Finset (Finset (Fin n)) => (∀ e ∈ H, Finset.card e = 3) ∧ ¬ ThreeEdgesIn6 H) (Finset.univ : Finset (Finset (Finset (Fin n)))), ∀ H ∈ Finset.filter (fun H : Finset (Finset (Fin n)) => (∀ e ∈ H, Finset.card e = 3) ∧ ¬ ThreeEdgesIn6 H) (Finset.univ : Finset (Finset (Finset (Fin n)))), H.card ≤ H₀.card := by
      apply_rules [ Finset.exists_max_image ];
      exact ⟨ ∅, by simp +decide [ ThreeEdgesIn6 ] ⟩;
    refine' ⟨ H₀, hH₀.1, mod_cast le_antisymm _ _ ⟩;
    · exact Finset.le_sup ( f := Finset.card ) ( by aesop );
    · exact Finset.sup_le fun H hH => hH₀.2 H hH;
  grind

end Erdos716
