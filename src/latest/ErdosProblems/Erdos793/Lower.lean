/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- No license was supplied for the problem-specific proof.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 793.
Informal authors: GPT-5.6 Sol Ultra, prompted by Przemek Chojecki;
the upper-bound argument refines Paul Erdős's 1938 proof.
Formal authors: Aristotle, Wouter van Doorn.
Jake Mallen integrated the complete PNT dependency in the selected source.
Source: https://www.erdosproblems.com/793#post-7596
https://github.com/Woett/Lean-files/blob/ce4bcdac98415c60c7a7d7f78ce54c9adb79bc47/ErdosProblem793.lean
https://github.com/Jayyhk/erdos-lean/tree/cc6c94bd3f9de7c4cf7703ed40d8fd06380780a3/problems/793
Selected complete source: Lean 4.30.0, Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f.
The original single-file upload does not specify a toolchain.
This port reuses the tracked PNT+ library instead of copying its vendored proof.
-/
import ErdosProblems.Erdos793.Upper

open Filter Real
open scoped BigOperators Topology

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Erdos793

/-! ## Admissible cells and their weights -/

/-- `Δ_i = e^{(i+1)h} - e^{ih}`. -/
noncomputable def Delta (h : ℝ) (i : ℤ) : ℝ := Real.exp ((i + 1) * h) - Real.exp (i * h)

/-- A pair `(i, j) ∈ ℤ²` is an *admissible cell* if `i ≤ j` and `i + 2j ≤ -4`. -/
def Admissible (c : ℤ × ℤ) : Prop := c.1 ≤ c.2 ∧ c.1 + 2 * c.2 ≤ -4

/-- The third index of a cell `(i, j)` is `k = -i - j - 3`. -/
def thirdIndex (c : ℤ × ℤ) : ℤ := -c.1 - c.2 - 3

/-
**Order and sum of the cell indices.**
-/
lemma cell_order (c : ℤ × ℤ) (hc : Admissible c) :
    c.1 ≤ c.2 ∧ c.2 < thirdIndex c ∧ c.1 + c.2 + thirdIndex c = -3 ∧
      thirdIndex c - c.2 ≥ 1 := by
  exact ⟨ hc.1, by unfold thirdIndex; linarith [ hc.1, hc.2 ], by unfold thirdIndex; linarith [ hc.1, hc.2 ], by unfold thirdIndex; linarith [ hc.1, hc.2 ] ⟩

/-- The `C_N⁻` truncation. -/
def CNneg (N : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range N ×ˢ Finset.range N).image
    (fun p => (-(p.1 : ℤ) - (p.2 : ℤ) - 2, -(p.1 : ℤ) - 1))

/-- The `C_N⁺` truncation. -/
def CNpos (N : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range N ×ˢ Finset.range N).image
    (fun p => (-2 * (p.1 : ℤ) - (p.2 : ℤ) - 4, (p.1 : ℤ)))

/-- The `C_N⁰` (diagonal) truncation. -/
def CNzero (N : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range N).image (fun a : ℕ => (-(a : ℤ) - 2, -(a : ℤ) - 2))

/-- The full truncation `C_N = C_N⁻ ∪ C_N⁺ ∪ C_N⁰`. -/
def CN (N : ℕ) : Finset (ℤ × ℤ) := CNneg N ∪ CNpos N ∪ CNzero N

/-- The cell weight `W_h(C)`. -/
noncomputable def Wh (h : ℝ) (C : Finset (ℤ × ℤ)) : ℝ :=
  (∑ c ∈ C.filter (fun c => c.1 < c.2), Delta h c.1 * Delta h c.2)
    + (1/2) * ∑ c ∈ C.filter (fun c => c.1 = c.2), (Delta h c.1) ^ 2

/-
Every member of `C_N` is admissible.
-/
lemma CN_admissible (N : ℕ) : ∀ c ∈ CN N, Admissible c := by
  -- By definition of CN, we know that every element in CN N is admissible.
  unfold CN Admissible; simp [CNneg, CNpos, CNzero]; (
  grind)

/-
For `h > 0`, `W_h(C_N) → e^{-h} + ½ e^{-2h}` as `N → ∞`.
-/
lemma Wh_CN_limit (h : ℝ) (hh : 0 < h) :
    Tendsto (fun N : ℕ => Wh h (CN N)) atTop
      (𝓝 (Real.exp (-h) + (1/2) * Real.exp (-2*h))) := by
  unfold Wh;
  -- Let's rewrite the expression using the definitions of `Delta` and `Wh`.
  suffices h_suff : Filter.Tendsto (fun N => (∑ a ∈ Finset.range N, ∑ d ∈ Finset.range N, Delta h (-a - d - 2) * Delta h (-a - 1)) + (∑ b ∈ Finset.range N, ∑ d ∈ Finset.range N, Delta h (-2 * b - d - 4) * Delta h b) + (1 / 2) * (∑ a ∈ Finset.range N, Delta h (-a - 2) ^ 2)) Filter.atTop (nhds (Real.exp (-h) + (1 / 2) * Real.exp (-2 * h))) by
    convert h_suff using 3;
    · unfold CN CNneg CNpos CNzero; norm_num [ Finset.sum_filter, Finset.sum_image ] ;
      rw [ Finset.sum_union, Finset.sum_union ];
      · rw [ Finset.sum_image, Finset.sum_image, Finset.sum_image ] <;> norm_num [ Finset.sum_product ];
        · exact congrArg₂ ( · + · ) ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => if_pos <| by linarith ) ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => if_pos <| by linarith );
        · norm_num [ Set.InjOn ];
          intros; subst_vars; exact ⟨ rfl, by linarith ⟩ ;
        · norm_num [ Set.InjOn ];
          intros; omega;
      · norm_num [ Finset.disjoint_left ];
        intros; subst_vars; omega;
      · norm_num [ Finset.disjoint_left ];
        grind;
    · rw [ show CN _ = CNneg _ ∪ CNpos _ ∪ CNzero _ from rfl ] ; norm_num [ CNneg, CNpos, CNzero ] ; ring_nf;
      rw [ Finset.sum_subset ];
      any_goals exact Finset.image ( fun a : ℕ => ( -2 - a, -2 - a ) ) ( Finset.range ‹_› );
      · rw [ Finset.sum_image ] ; aesop;
      · grind;
      · grind;
  -- Let's simplify the expression inside the limit.
  suffices h_simp : Filter.Tendsto (fun N => (Real.exp h - 1) ^ 2 * (Real.exp (-h)) ^ 3 * (∑ a ∈ Finset.range N, (Real.exp (-2 * h)) ^ a) * (∑ d ∈ Finset.range N, (Real.exp (-h)) ^ d) + (Real.exp h - 1) ^ 2 * (Real.exp (-h)) ^ 4 * (∑ b ∈ Finset.range N, (Real.exp (-h)) ^ b) * (∑ d ∈ Finset.range N, (Real.exp (-h)) ^ d) + (1 / 2) * (Real.exp h - 1) ^ 2 * (Real.exp (-h)) ^ 4 * (∑ a ∈ Finset.range N, (Real.exp (-2 * h)) ^ a)) Filter.atTop (nhds (Real.exp (-h) + (1 / 2) * Real.exp (-2 * h))) by
    convert h_simp using 3 <;> norm_num [ Delta ] ; ring_nf;
    · norm_num [ ← Real.exp_add, ← Real.exp_nat_mul ] ; ring_nf;
      norm_num [ Finset.mul_sum _ _ _, Finset.sum_add_distrib, Finset.sum_mul, Real.exp_add, Real.exp_sub, Real.exp_neg ] ; ring_nf;
      norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, sq ] ; ring_nf;
    · rw [ Finset.mul_sum _ _ _ ] ; rw [ Finset.mul_sum _ _ _ ] ; congr ; ext ; ring_nf ; norm_num [ ← Real.exp_nat_mul, ← Real.exp_add ] ; ring_nf;
  -- Recognize that the sums are geometric series and apply the formula for their sum.
  have h_geo_series : Filter.Tendsto (fun N => (∑ a ∈ Finset.range N, (Real.exp (-2 * h)) ^ a)) Filter.atTop (nhds (1 / (1 - Real.exp (-2 * h)))) ∧ Filter.Tendsto (fun N => (∑ d ∈ Finset.range N, (Real.exp (-h)) ^ d)) Filter.atTop (nhds (1 / (1 - Real.exp (-h)))) := by
    exact ⟨ by simpa using ( hasSum_geometric_of_lt_one ( by positivity ) ( by norm_num; positivity ) ) |> HasSum.tendsto_sum_nat, by simpa using ( hasSum_geometric_of_lt_one ( by positivity ) ( by norm_num; positivity ) ) |> HasSum.tendsto_sum_nat ⟩;
  convert Filter.Tendsto.add ( Filter.Tendsto.add ( Filter.Tendsto.mul ( Filter.Tendsto.mul ( tendsto_const_nhds ) h_geo_series.1 ) h_geo_series.2 ) ( Filter.Tendsto.mul ( Filter.Tendsto.mul ( tendsto_const_nhds ) h_geo_series.2 ) h_geo_series.2 ) ) ( Filter.Tendsto.mul ( tendsto_const_nhds ) h_geo_series.1 ) using 2 ; norm_num [ Real.exp_neg ];
  field_simp;
  rw [ eq_div_iff ( sub_ne_zero_of_ne <| by norm_num; linarith ) ] ; ring_nf;
  rw [ show h * 2 = h + h by ring, Real.exp_add ] ; ring_nf;
  nlinarith [ Real.exp_pos h, pow_pos ( Real.exp_pos h ) 3, pow_pos ( Real.exp_pos h ) 4, pow_pos ( Real.exp_pos h ) 5, pow_pos ( Real.exp_pos h ) 6, pow_pos ( Real.exp_pos h ) 7, pow_pos ( Real.exp_pos h ) 8, mul_inv_cancel₀ ( show -1 + Real.exp h ^ 2 ≠ 0 by nlinarith [ Real.add_one_le_exp h, pow_pos ( Real.exp_pos h ) 2 ] ) ]

/-
For every `ε > 0` there are `h > 0` and `N` with `9 · W_h(C_N) > 27/2 - ε`.
-/
lemma near_maximal_weight (ε : ℝ) (hε : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ ∃ N : ℕ, (27:ℝ)/2 - ε < 9 * Wh h (CN N) := by
  -- Let `g h := 9 * (Real.exp (-h) + (1/2) * Real.exp (-2*h))`. `g` is continuous and `g 0 = 9*(1 + 1/2) = 27/2`.
  set g : ℝ → ℝ := fun h => 9 * (Real.exp (-h) + (1/2) * Real.exp (-2 * h))
  have hg_cont : ContinuousAt g 0 := by
    fun_prop
  have hg_zero : g 0 = 27 / 2 := by
    norm_num [ g ]
  have hg_gt : ∃ h, 0 < h ∧ g h > 27 / 2 - ε / 2 := by
    have := Metric.continuousAt_iff.mp hg_cont ( ε / 2 ) ( half_pos hε );
    exact Exists.elim this fun δ hδ => ⟨ δ / 2, half_pos hδ.1, by linarith [ abs_lt.mp ( hδ.2 ( show |δ / 2 - 0| < δ by rw [ abs_of_pos ] <;> linarith ) ) ] ⟩;
  obtain ⟨ h, hh_pos, hh_gt ⟩ := hg_gt; have := Wh_CN_limit h hh_pos; simp_all +decide [ Metric.tendsto_nhds ] ;
  simp +zetaDelta at *;
  exact Exists.elim ( this ( ( 9 * ( Real.exp ( -h ) + 2⁻¹ * Real.exp ( - ( 2 * h ) ) ) - ( 27 / 2 - ε / 2 ) ) / 9 ) ( by linarith ) ) fun N hN => ⟨ h, hh_pos, N, by linarith [ abs_lt.mp ( hN N le_rfl ) ] ⟩

/-! ## Finite proper edge-colourings -/

/-
If `|C| ≥ max(|X|, |Y|)`, then the complete bipartite graph with parts `X` and
`Y` has a proper edge-colouring with colours in `C`: distinct edges sharing an
endpoint get distinct colours.
-/
lemma complete_bipartite_colouring {α β γ : Type*} [DecidableEq α] [DecidableEq β]
    [Nonempty γ] (X : Finset α) (Y : Finset β) (C : Finset γ)
    (h : max X.card Y.card ≤ C.card) :
    ∃ χ : α → β → γ,
      (∀ x ∈ X, ∀ y ∈ Y, χ x y ∈ C) ∧
      (∀ x ∈ X, ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → χ x y ≠ χ x y') ∧
      (∀ x ∈ X, ∀ x' ∈ X, ∀ y ∈ Y, x ≠ x' → χ x y ≠ χ x' y) := by
  -- If `m = 0`, then `X = ∅` and `Y = ∅`; take `χ = fun _ _ => Classical.arbitrary γ` and all conditions hold vacuously.
  by_cases hm : max X.card Y.card = 0;
  · aesop;
  · -- Otherwise `m ≥ 1`. Build `f : α → ZMod m` injective on `X` (from `X ≃ Fin X.card ↪ Fin m ≃ ZMod m`, extended by `0` off `X`) and `g : β → ZMod m` injective on `Y` similarly.
    obtain ⟨m, hm⟩ : ∃ m, max X.card Y.card = m ∧ m ≥ 1 := by
      exact ⟨ _, rfl, Nat.pos_of_ne_zero hm ⟩
    obtain ⟨f, hf⟩ : ∃ f : α → ZMod m, ∀ x x', x ∈ X → x' ∈ X → x ≠ x' → f x ≠ f x' := by
      -- Since $X$ is a finite set, we can construct an injective function $f : X \to \mathbb{Z}/m\mathbb{Z}$.
      obtain ⟨f, hf_inj⟩ : ∃ f : X → ZMod m, Function.Injective f := by
        have h_inj : Nonempty (X ↪ Fin m) := by
          exact ⟨ ( Function.Embedding.trans ( Fintype.equivFinOfCardEq ( by aesop ) |> Equiv.toEmbedding ) ( Fin.castLEEmb ( by aesop ) ) ) ⟩;
        have h_inj : Nonempty (Fin m ↪ ZMod m) := by
          rcases m with ( _ | _ | m ) <;> simp_all +decide [ ZMod ];
          · exact ⟨ ⟨ fun x => x, fun x y hxy => by simp [ Fin.ext_iff ] ⟩ ⟩;
          · exact ⟨ ⟨ fun x => x, fun x y hxy => by simpa using hxy ⟩ ⟩;
        exact ⟨ _, Function.Injective.comp h_inj.some.injective ( ‹Nonempty ( X ↪ Fin m ) ›.some.injective ) ⟩;
      exact ⟨ fun x => if hx : x ∈ X then f ⟨ x, hx ⟩ else 0, fun x x' hx hx' hne => by simpa [ hx, hx', hne ] using hf_inj.ne ( show ⟨ x, hx ⟩ ≠ ⟨ x', hx' ⟩ from by simpa [ Subtype.ext_iff ] using hne ) ⟩
    obtain ⟨g, hg⟩ : ∃ g : β → ZMod m, ∀ y y', y ∈ Y → y' ∈ Y → y ≠ y' → g y ≠ g y' := by
      have h_inj : Nonempty (Y ↪ ZMod m) := by
        have h_card : Y.card ≤ m := by
          exact hm.1 ▸ le_max_right _ _;
        have h_card : Nonempty (Y ↪ Fin m) := by
          exact ⟨ ( Function.Embedding.trans ( Equiv.toEmbedding ( Fintype.equivFinOfCardEq ( by simp +decide ) ) ) ( Fin.castLEEmb h_card ) ) ⟩;
        rcases m with ( _ | _ | m ) <;> simp_all +decide [ ZMod ];
      obtain ⟨ g ⟩ := h_inj; use fun y => if hy : y ∈ Y then g ⟨ y, hy ⟩ else 0; aesop;
    -- Since `m ≤ C.card`, get a subset `t ⊆ C` with `t.card = m` (`Finset.exists_subset_card_eq`), and an equiv `ZMod m ≃ t` (`Fintype.equivOfCardEq`, using `ZMod.card`), giving `emb : ZMod m → γ` injective with `emb z ∈ C` for all `z`.
    obtain ⟨t, ht⟩ : ∃ t : Finset γ, t ⊆ C ∧ t.card = m := by
      exact Finset.exists_subset_card_eq ( by aesop )
    obtain ⟨emb, h_emb⟩ : ∃ emb : ZMod m → γ, Function.Injective emb ∧ ∀ z, emb z ∈ t := by
      rcases m with ( _ | m ) <;> simp_all +decide [ ZMod ];
      have := Finset.equivFinOfCardEq ht.2;
      exact ⟨ fun z => this.symm z, Subtype.val_injective.comp this.symm.injective, fun z => this.symm z |>.2 ⟩;
    refine' ⟨ fun x y => emb ( f x - g y ), _, _, _ ⟩ <;> simp_all +decide [ Function.Injective.eq_iff h_emb.1 ];
    exact fun x hx y hy => ht.1 ( h_emb.2 _ )

/-
If `|C| ≥ |X|`, then the complete graph on `X` has a proper edge-colouring with
colours in `C`, given by a symmetric function `χ` such that at each vertex the
incident edges receive distinct colours.
-/
lemma complete_graph_colouring {α γ : Type*} [DecidableEq α] [Nonempty γ]
    (X : Finset α) (C : Finset γ) (h : X.card ≤ C.card) :
    ∃ χ : α → α → γ,
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y → χ x y ∈ C) ∧
      (∀ x ∈ X, ∀ y ∈ X, χ x y = χ y x) ∧
      (∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a ≠ b → a ≠ c → b ≠ c → χ a b ≠ χ a c) := by
  by_contra h_not_symm;
  -- Let's choose any finite set of colors `C` with `C.card ≥ X.card`.
  obtain ⟨χ, hχ⟩ : ∃ χ : α → α → ℕ, (∀ x ∈ X, ∀ y ∈ X, x ≠ y → χ x y < X.card) ∧ (∀ x ∈ X, ∀ y ∈ X, χ x y = χ y x) ∧ (∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a ≠ b → a ≠ c → b ≠ c → χ a b ≠ χ a c) := by
    -- Let's choose any finite set of colors `C` with `C.card ≥ X.card` and construct a proper edge-colouring for the complete graph on `X`.
    obtain ⟨f, hf⟩ : ∃ f : α → Fin X.card, ∀ x ∈ X, ∀ y ∈ X, x ≠ y → f x ≠ f y := by
      obtain ⟨f, hf⟩ : ∃ f : X → Fin X.card, Function.Injective f := by
        exact ⟨ fun x => Fintype.equivFinOfCardEq ( by simp +decide ) x, by simp +decide [ Function.Injective ] ⟩;
      exact ⟨ fun x => if hx : x ∈ X then f ⟨ x, hx ⟩ else ⟨ 0, Fin.pos ( Fin.mk 0 ( Finset.card_pos.mpr ( Finset.nonempty_of_ne_empty ( by aesop_cat ) ) ) ) ⟩, fun x hx y hy hxy => by simpa [ hx, hy, hxy ] using hf.ne ( by aesop_cat ) ⟩;
    refine' ⟨ fun x y => ( f x + f y |> Fin.val ) % X.card, _, _, _ ⟩ <;> simp +decide [Fin.val_add];
    · exact fun x hx y hy hxy => Nat.mod_lt _ ( Finset.card_pos.mpr ⟨ x, hx ⟩ );
    · exact fun x hx y hy => by rw [ add_comm ] ;
    · intro a ha b hb c hc hab hbc hca H; have := Nat.modEq_iff_dvd.1 H.symm; simp_all +decide [Fin.ext_iff] ;
      exact hf b hb c hc hca ( by obtain ⟨ k, hk ⟩ := this; nlinarith [ show k = 0 by nlinarith [ Fin.is_lt ( f b ), Fin.is_lt ( f c ) ] ] );
  obtain ⟨f, hf⟩ : ∃ f : Fin X.card ↪ γ, ∀ i, f i ∈ C := by
    obtain ⟨ s, hs ⟩ := Finset.exists_subset_card_eq h;
    have h_equiv : Nonempty (Fin X.card ≃ s) := by
      exact ⟨ Fintype.equivOfCardEq <| by simp +decide [ hs.2 ] ⟩;
    exact ⟨ ⟨ fun i => h_equiv.some i, fun i j hij => by simpa [ Fin.ext_iff ] using h_equiv.some.injective ( Subtype.ext hij ) ⟩, fun i => hs.1 ( h_equiv.some i |>.2 ) ⟩;
  refine' h_not_symm ⟨ fun x y => if hx : x ∈ X then if hy : y ∈ X then if hxy : x = y then Classical.arbitrary γ else f ⟨ χ x y, hχ.1 x hx y hy hxy ⟩ else Classical.arbitrary γ else Classical.arbitrary γ, _, _, _ ⟩ <;> simp +decide [ * ];
  · grind;
  · grind;
  · simp +contextual [ hχ.2.2, f.injective.eq_iff ]

/-! ## Linear prime triples -/

/-- The vertex set of a family `H` of triples. -/
def Vset (H : Finset (Finset ℕ)) : Finset ℕ := Finset.biUnion H id

/-- The strongly-2-primitive set built from a linear family `H`: retained primes
(those `≤ n` not used by any triple) together with the triple products. -/
noncomputable def AH (n : ℕ) (H : Finset (Finset ℕ)) : Finset ℕ :=
  ((Finset.Icc 1 n).filter (fun p => Nat.Prime p ∧ p ∉ Vset H))
    ∪ H.image (fun E => ∏ p ∈ E, p)

/-
If `H` is a finite linear family of 3-element sets of distinct primes with each
product `≤ n`, then `A_H ⊆ [n]` is strongly 2-primitive with
`|A_H| + |V(H)| = π(n) + |H|`. -/
lemma linear_triple_replacement (n : ℕ) (H : Finset (Finset ℕ))
    (h3 : ∀ E ∈ H, E.card = 3)
    (hprime : ∀ E ∈ H, ∀ p ∈ E, Nat.Prime p)
    (hprod : ∀ E ∈ H, (∏ p ∈ E, p) ≤ n)
    (hlin : ∀ E ∈ H, ∀ E' ∈ H, E ≠ E' → (E ∩ E').card ≤ 1) :
    Strongly2Primitive (AH n H) ∧ AH n H ⊆ Finset.Icc 1 n ∧
      (AH n H).card + (Vset H).card =
        ((Finset.Icc 1 n).filter Nat.Prime).card + H.card := by
  refine' ⟨ _, _, _ ⟩;
  · -- Take `a ∈ AH`, `b,c ∈ AH`, `a ≠ b`, `a ≠ c`; show `¬ a ∣ b*c`.
    intro a ha b hb c hc hab hbc
    by_cases ha_prime : a ∈ ((Finset.Icc 1 n).filter (fun p => Nat.Prime p ∧ p ∉ Vset H));
    · -- Since $a$ is a prime not in $Vset H$, it cannot divide any element of $H.image (fun E => ∏ p ∈ E, p)$.
      have h_not_div_H : ∀ E ∈ H, ¬(a ∣ ∏ p ∈ E, p) := by
        intro E hE; rw [ Nat.Prime.dvd_iff_not_coprime ] <;> simp_all +decide [Nat.coprime_prod_right_iff] ;
        exact fun p hp => ha_prime.2.1.coprime_iff_not_dvd.mpr fun h => ha_prime.2.2 <| Finset.mem_biUnion.mpr ⟨ E, hE, by have := Nat.prime_dvd_prime_iff_eq ha_prime.2.1 ( hprime E hE p hp ) ; aesop ⟩;
      unfold AH at hb hc; simp_all +decide [ Nat.Prime.dvd_mul ] ;
      rcases hb with ( ⟨ hb₁, hb₂, hb₃ ⟩ | ⟨ E, hE₁, rfl ⟩ ) <;> rcases hc with ( ⟨ hc₁, hc₂, hc₃ ⟩ | ⟨ F, hF₁, rfl ⟩ ) <;> simp_all +decide [ Nat.prime_dvd_prime_iff_eq ];
    · -- Since `a` is not a retained prime, it must be a product of three distinct primes from some `E ∈ H`.
      obtain ⟨E, hE, rfl⟩ : ∃ E ∈ H, a = ∏ p ∈ E, p := by
        unfold AH at ha; aesop;
      -- Each element of `AH \ {a}` shares at most one prime of `E`: a retained prime shares none (retained primes are `∉ Vset H ⊇ E`), and any other triple product `∏_{E'}` shares at most one prime of `E` by linearity `hlin` (`(E ∩ E').card ≤ 1`).
      have h_share : ∀ x ∈ AH n H, x ≠ ∏ p ∈ E, p → (E.filter (fun p => p ∣ x)).card ≤ 1 := by
        intro x hx hx_ne; by_cases hx_prime : x ∈ ((Finset.Icc 1 n).filter (fun p => Nat.Prime p ∧ p ∉ Vset H)); simp_all +decide ;
        · exact Finset.card_le_one.mpr fun p hp q hq => by have := Nat.prime_dvd_prime_iff_eq ( hprime E hE p ( Finset.mem_filter.mp hp |>.1 ) ) hx_prime.2.1; have := Nat.prime_dvd_prime_iff_eq ( hprime E hE q ( Finset.mem_filter.mp hq |>.1 ) ) hx_prime.2.1; aesop;
        · -- Since `x` is not a retained prime, it must be a product of three distinct primes from some `E' ∈ H`.
          obtain ⟨E', hE', rfl⟩ : ∃ E' ∈ H, x = ∏ p ∈ E', p := by
            unfold AH at hx; aesop;
          convert hlin E hE E' hE' _ using 1;
          · congr 1 with p ; simp +decide ;
            intro hp; rw [ Nat.Prime.dvd_iff_not_coprime ( hprime E hE p hp ) ] ; simp +decide [ Nat.coprime_prod_right_iff ] ;
            exact ⟨ fun ⟨ q, hq, hq' ⟩ => by have := Nat.coprime_primes ( hprime E hE p hp ) ( hprime E' hE' q hq ) ; aesop, fun hq => ⟨ p, hq, by have := Nat.Prime.ne_one ( hprime E hE p hp ) ; aesop ⟩ ⟩;
          · grind;
      -- If `a ∣ b*c`, then all three primes of `E` divide `b*c`; each prime of `E` divides `b` or `c`; by pigeonhole two of them divide the same one of `b,c`, contradicting that `b` (resp. `c`) shares at most one prime with `E`.
      by_contra h_div
      have h_div_bc : (E.filter (fun p => p ∣ b)).card + (E.filter (fun p => p ∣ c)).card ≥ 3 := by
        have h_div_bc : ∀ p ∈ E, p ∣ b ∨ p ∣ c := by
          exact fun p hp => Nat.Prime.dvd_mul ( hprime E hE p hp ) |>.1 ( dvd_trans ( Finset.dvd_prod_of_mem _ hp ) h_div );
        rw [ ← h3 E hE, ← Finset.card_union_add_card_inter ];
        exact le_add_right ( Finset.card_le_card fun x hx => by specialize h_div_bc x hx; aesop );
      linarith [ h_share b hb ( by tauto ), h_share c hc ( by tauto ) ];
  · intro x hx; simp_all +decide [ AH ] ;
    rcases hx with ( ⟨ hx₁, hx₂, hx₃ ⟩ | ⟨ E, hE₁, rfl ⟩ ) <;> [ exact hx₁; exact ⟨ Nat.one_le_iff_ne_zero.mpr <| Finset.prod_ne_zero_iff.mpr fun p hp => Nat.Prime.ne_zero <| hprime E hE₁ p hp, hprod E hE₁ ⟩ ];
  · -- We need to show that the cardinality of the union of the retained primes and the triple products is equal to the sum of the cardinalities of the retained primes and the triple products.
    have h_card_union : (AH n H).card + (Vset H).card = ((Finset.Icc 1 n).filter (fun p => Nat.Prime p ∧ p ∉ Vset H)).card + (H.image (fun E => ∏ p ∈ E, p)).card + (Vset H).card := by
      rw [ AH, Finset.card_union_of_disjoint ];
      norm_num [ Finset.disjoint_right ];
      intro E hE h1 h2 h3; have := h3; simp_all +decide ;
      rcases Finset.card_eq_three.mp ( h3 E hE ) with ⟨ p, q, r, hp, hq, hr, h ⟩ ; simp_all +decide [ Nat.prime_mul_iff ];
      aesop;
    -- We need to show that the cardinality of the image of the triple products is equal to the cardinality of H.
    have h_card_image : (H.image (fun E => ∏ p ∈ E, p)).card = H.card := by
      apply Finset.card_image_of_injOn;
      intro E hE E' hE' h_eq; apply_fun fun x => x.primeFactors at h_eq; simp_all +decide ;
      rw [ Nat.primeFactors_prod, Nat.primeFactors_prod ] at h_eq <;> aesop;
    rw [ h_card_union, h_card_image, add_right_comm ];
    rw [ ← Finset.card_union_of_disjoint ];
    · congr 2 with p ; simp +contextual [ Vset ];
      exact ⟨ fun h => by rcases h with ( ⟨ ⟨ hp₁, hp₂ ⟩, hp₃, hp₄ ⟩ | ⟨ E, hE₁, hE₂ ⟩ ) <;> [ exact ⟨ ⟨ hp₁, hp₂ ⟩, hp₃ ⟩ ; exact ⟨ ⟨ Nat.Prime.pos ( hprime E hE₁ p hE₂ ), hprod E hE₁ |> le_trans ( Nat.le_of_dvd ( Finset.prod_pos fun q hq => Nat.Prime.pos ( hprime E hE₁ q hq ) ) ( Finset.dvd_prod_of_mem _ hE₂ ) ) ⟩, hprime E hE₁ p hE₂ ⟩ ], fun h => if h' : ∃ E ∈ H, p ∈ E then Or.inr h' else Or.inl ⟨ ⟨ h.1.1, h.1.2 ⟩, h.2, fun E hE₁ hE₂ => h' ⟨ E, hE₁, hE₂ ⟩ ⟩ ⟩;
    · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.mem_filter.mp hx₁ |>.2.2 hx₂

/-! ## Prime bins and the hypergraph construction -/

/-- `M = n^{1/3} / log n`. -/
noncomputable def Mval (n : ℕ) : ℝ := (n : ℝ) ^ ((1:ℝ)/3) / Real.log n

/-
`M² = S`.
-/
lemma Mval_sq_eq_S (n : ℕ) : (Mval n) ^ 2 = S n := by
  unfold Mval S;
  rw [ div_pow, ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num

/-- The `r`-th prime bin `P_r = {p prime : y e^{rh} < p ≤ y e^{(r+1)h}}`. -/
noncomputable def Pbin (h : ℝ) (n : ℕ) (r : ℤ) : Finset ℕ :=
  (Finset.Ioc ⌊(n : ℝ) ^ ((1:ℝ)/3) * Real.exp ((r : ℝ) * h)⌋₊
             ⌊(n : ℝ) ^ ((1:ℝ)/3) * Real.exp (((r : ℝ) + 1) * h)⌋₊).filter Nat.Prime

/-- `m_r = |P_r|`. -/
noncomputable def mbin (h : ℝ) (n : ℕ) (r : ℤ) : ℕ := (Pbin h n r).card

/-- The set of indices appearing in a cell set `C`. -/
def Rset (C : Finset (ℤ × ℤ)) : Finset ℤ :=
  C.image Prod.fst ∪ C.image Prod.snd ∪ C.image thirdIndex

/-
For fixed `h > 0` and `r`, `m_r / M → 3 Δ_r`.
-/
lemma bin_sizes (hpnt : PNT) (h : ℝ) (hh : 0 < h) (r : ℤ) :
    Tendsto (fun n : ℕ => (mbin h n r : ℝ) / Mval n) atTop (𝓝 (3 * Delta h r)) := by
  convert Tendsto.sub ( pi_mul_ratio hpnt ( Real.exp ( ( r + 1 ) * h ) ) ( by positivity ) |> Filter.Tendsto.comp <| tendsto_y_atTop ) ( pi_mul_ratio hpnt ( Real.exp ( r * h ) ) ( by positivity ) |> Filter.Tendsto.comp <| tendsto_y_atTop ) |> ( ·.mul_const 3 ) using 2 ; norm_num [ mbin, Mval ] ; ring_nf;
  · by_cases hn : ‹_› = 0 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
    rw [ Pbin ];
    rw [ card_primes_Ioc ];
    · rw [ Nat.cast_sub ] <;> norm_num ; ring_nf;
      · rw [ Real.log_rpow ( by positivity ) ] ; ring;
      · exact Nat.monotone_primeCounting <| Nat.floor_mono <| mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by linarith ) <| by positivity;
    · exact Nat.floor_mono <| mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by linarith ) <| by positivity;
  · unfold Delta; ring;

/-
For fixed `h > 0` and finite `C`, for all large `n` every cell `(i,j) ∈ C` with
third index `k` has `m_k ≥ max(m_i, m_j)`.
-/
lemma third_bin_large (hpnt : PNT) (h : ℝ) (hh : 0 < h) (C : Finset (ℤ × ℤ))
    (hC : ∀ c ∈ C, Admissible c) :
    ∀ᶠ n : ℕ in atTop, ∀ c ∈ C,
      max (mbin h n c.1) (mbin h n c.2) ≤ mbin h n (thirdIndex c) := by
  -- By definition of `mbin`, we know that `mbin h n r` is the number of primes in the interval `(⌊(n : ℝ) ^ ((1:ℝ)/3) * Real.exp ((r : ℝ) * h)⌋₊, ⌊(n : ℝ) ^ ((1:ℝ)/3) * Real.exp (((r : ℝ) + 1) * h)⌋₊]`.
  have h_mbin : ∀ c ∈ C, ∀ᶠ n in atTop, mbin h n c.2 < mbin h n (thirdIndex c) ∧ mbin h n c.1 < mbin h n (thirdIndex c) := by
    intro c hc
    have h_mbin_lt : Filter.Tendsto (fun n => (mbin h n c.2 : ℝ) / Mval n) Filter.atTop (nhds (3 * Delta h c.2)) ∧ Filter.Tendsto (fun n => (mbin h n (thirdIndex c) : ℝ) / Mval n) Filter.atTop (nhds (3 * Delta h (thirdIndex c))) ∧ Filter.Tendsto (fun n => (mbin h n c.1 : ℝ) / Mval n) Filter.atTop (nhds (3 * Delta h c.1)) := by
      exact ⟨ bin_sizes hpnt h hh c.2, bin_sizes hpnt h hh ( thirdIndex c ), bin_sizes hpnt h hh c.1 ⟩;
    have h_mbin_lt : 3 * Delta h c.2 < 3 * Delta h (thirdIndex c) ∧ 3 * Delta h c.1 < 3 * Delta h (thirdIndex c) := by
      constructor <;> norm_num [ Delta ];
      · norm_num [ thirdIndex ];
        rw [ show ( -c.1 - c.2 - 3 + 1 : ℝ ) * h = ( -c.1 - c.2 - 3 ) * h + h by ring, show ( c.2 + 1 : ℝ ) * h = c.2 * h + h by ring, Real.exp_add, Real.exp_add ];
        nlinarith [ Real.add_one_le_exp h, Real.exp_pos ( c.2 * h ), Real.exp_lt_exp.mpr ( show ( -c.1 - c.2 - 3 : ℝ ) * h > c.2 * h by nlinarith [ show ( c.1 : ℝ ) ≤ c.2 by exact_mod_cast hC c hc |>.1, show ( c.1 : ℝ ) + 2 * c.2 ≤ -4 by exact_mod_cast hC c hc |>.2 ] ) ];
      · have := cell_order c ( hC c hc );
        rw [ show ( c.1 + 1 : ℝ ) * h = c.1 * h + h by ring, show ( thirdIndex c + 1 : ℝ ) * h = thirdIndex c * h + h by ring, Real.exp_add, Real.exp_add ];
        nlinarith [ Real.add_one_le_exp h, Real.exp_pos ( c.1 * h ), Real.exp_lt_exp.mpr ( show ( c.1 : ℝ ) * h < thirdIndex c * h by exact mul_lt_mul_of_pos_right ( mod_cast by linarith ) hh ) ];
    have h_mbin_lt : ∀ᶠ n in atTop, (mbin h n c.2 : ℝ) / Mval n < (mbin h n (thirdIndex c) : ℝ) / Mval n ∧ (mbin h n c.1 : ℝ) / Mval n < (mbin h n (thirdIndex c) : ℝ) / Mval n := by
      rename_i h;
      exact Filter.eventually_and.mpr ⟨ h.1.eventually_lt h.2.1 h_mbin_lt.1, h.2.2.eventually_lt h.2.1 h_mbin_lt.2 ⟩;
    filter_upwards [ h_mbin_lt, tendsto_M_atTop.eventually_gt_atTop 0 ] with n hn hn';
    rw [ div_lt_div_iff_of_pos_right, div_lt_div_iff_of_pos_right ] at hn <;> norm_cast at *;
  simp +zetaDelta at *;
  choose! N hN using h_mbin;
  exact ⟨ Finset.sup C ( fun x => N x.1 x.2 ), fun n hn a b hab => ⟨ by linarith [ hN a b hab n ( le_trans ( Finset.le_sup ( f := fun x => N x.1 x.2 ) hab ) hn ) ], by linarith [ hN a b hab n ( le_trans ( Finset.le_sup ( f := fun x => N x.1 x.2 ) hab ) hn ) ] ⟩ ⟩

/-- Every element of a prime bin is prime. -/
lemma Pbin_prime (h : ℝ) (n : ℕ) (r : ℤ) {p : ℕ} (hp : p ∈ Pbin h n r) : Nat.Prime p := by
  exact (Finset.mem_filter.mp hp).2

/-- Membership bounds for a prime bin. -/
lemma Pbin_mem_iff (h : ℝ) (n : ℕ) (r : ℤ) (p : ℕ) :
    p ∈ Pbin h n r ↔
      (⌊(n : ℝ) ^ ((1:ℝ)/3) * Real.exp ((r : ℝ) * h)⌋₊ < p ∧
        p ≤ ⌊(n : ℝ) ^ ((1:ℝ)/3) * Real.exp (((r : ℝ) + 1) * h)⌋₊) ∧ Nat.Prime p := by
  simp [Pbin, Finset.mem_filter, Finset.mem_Ioc, and_assoc]

/-- Prime bins with distinct indices are disjoint. -/
lemma Pbin_disjoint (h : ℝ) (hh : 0 < h) (n : ℕ) {i j : ℤ} (hij : i < j) :
    Disjoint (Pbin h n i) (Pbin h n j) := by
  rw [Finset.disjoint_left]
  intro p hp hp'
  rw [Pbin_mem_iff] at hp hp'
  refine hp'.1.1.not_ge (hp.1.2.trans ?_)
  exact Nat.floor_mono <| mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr <| by nlinarith [show (i : ℝ) + 1 ≤ j by exact_mod_cast hij]) (by positivity)

/-
Eventually, every generated triple product is `≤ n`.
-/
lemma triple_prod_le_n_eventually (h : ℝ) (C : Finset (ℤ × ℤ)) :
    ∀ᶠ n : ℕ in atTop, ∀ c ∈ C,
      ∀ p ∈ Pbin h n c.1, ∀ q ∈ Pbin h n c.2, ∀ r ∈ Pbin h n (thirdIndex c), p * q * r ≤ n := by
  refine' Filter.eventually_atTop.mpr ⟨ 8, fun n hn c hc p hp q hq r hr => _ ⟩;
  -- From the definition of `Pbin`, we have `p ≤ ⌊(n : ℝ) ^ ((1:ℝ)/3) * Real.exp ((i+1)*h)⌋₊`, `q ≤ ⌊(n : ℝ) ^ ((1:ℝ)/3) * Real.exp ((j+1)*h)⌋₊`, and `r ≤ ⌊(n : ℝ) ^ ((1:ℝ)/3) * Real.exp ((k+1)*h)⌋₊`.
  have hp_le : (p : ℝ) ≤ (n : ℝ) ^ ((1:ℝ)/3) * Real.exp ((c.1 + 1) * h) := by
    exact le_trans ( Nat.cast_le.mpr <| Finset.mem_Ioc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2 ) <| Nat.floor_le <| by positivity;
  have hq_le : (q : ℝ) ≤ (n : ℝ) ^ ((1:ℝ)/3) * Real.exp ((c.2 + 1) * h) := by
    exact le_trans ( Nat.cast_le.mpr <| Finset.mem_Ioc.mp ( Finset.mem_filter.mp hq |>.1 ) |>.2 ) <| Nat.floor_le <| by positivity;
  have hr_le : (r : ℝ) ≤ (n : ℝ) ^ ((1:ℝ)/3) * Real.exp ((thirdIndex c + 1) * h) := by
    exact le_trans ( Nat.cast_le.mpr <| Finset.mem_Ioc.mp ( Finset.mem_filter.mp hr |>.1 ) |>.2 ) <| Nat.floor_le <| by positivity;
  -- Multiplying the three inequalities gives $p * q * r ≤ n * \exp((i + j + thirdIndex c + 3) * h)$.
  have h_mul : (p * q * r : ℝ) ≤ n * Real.exp ((c.1 + c.2 + thirdIndex c + 3) * h) := by
    convert mul_le_mul ( mul_le_mul hp_le hq_le ( by positivity ) ( by positivity ) ) hr_le ( by positivity ) ( by positivity ) using 1 <;> (try rfl)
    ring_nf
    rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; norm_num ; rw [ mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add ] ; ring_nf;
  norm_num [ thirdIndex ] at *;
  ring_nf at h_mul; norm_num at h_mul; exact_mod_cast h_mul;

/-- The explicit hypergraph family built from off-diagonal colourings `χ` and
diagonal colourings `χ'`. -/
noncomputable def hyperFamily (C : Finset (ℤ × ℤ)) (P : ℤ → Finset ℕ)
    (χ χ' : ℤ × ℤ → ℕ → ℕ → ℕ) : Finset (Finset ℕ) :=
  (C.filter (fun c => c.1 < c.2)).biUnion
      (fun c => (P c.1 ×ˢ P c.2).image (fun pq => ({pq.1, pq.2, χ c pq.1 pq.2} : Finset ℕ)))
    ∪ (C.filter (fun c => c.1 = c.2)).biUnion
      (fun c => ((P c.1 ×ˢ P c.1).filter (fun pq => pq.1 < pq.2)).image
        (fun pq => ({pq.1, pq.2, χ' c pq.1 pq.2} : Finset ℕ)))

/-
Membership characterization of `hyperFamily`.
-/
lemma mem_hyperFamily (C : Finset (ℤ × ℤ)) (P : ℤ → Finset ℕ)
    (χ χ' : ℤ × ℤ → ℕ → ℕ → ℕ) (E : Finset ℕ) :
    E ∈ hyperFamily C P χ χ' ↔
      (∃ c ∈ C, c.1 < c.2 ∧ ∃ p ∈ P c.1, ∃ q ∈ P c.2, E = {p, q, χ c p q}) ∨
      (∃ c ∈ C, c.1 = c.2 ∧ ∃ p ∈ P c.1, ∃ q ∈ P c.1, p < q ∧ E = {p, q, χ' c p q}) := by
  simp_all +decide [ Finset.ext_iff, hyperFamily ];
  grind +qlia

/-- Bundled properness data for the colourings used in `hyperFamily`. -/
structure ColData (C : Finset (ℤ × ℤ)) (P : ℤ → Finset ℕ) (χ χ' : ℤ × ℤ → ℕ → ℕ → ℕ) : Prop where
  χmem : ∀ c ∈ C, c.1 < c.2 → ∀ p ∈ P c.1, ∀ q ∈ P c.2, χ c p q ∈ P (thirdIndex c)
  χ2 : ∀ c ∈ C, c.1 < c.2 → ∀ p ∈ P c.1, ∀ q ∈ P c.2, ∀ q' ∈ P c.2, q ≠ q' → χ c p q ≠ χ c p q'
  χ1 : ∀ c ∈ C, c.1 < c.2 → ∀ p ∈ P c.1, ∀ p' ∈ P c.1, ∀ q ∈ P c.2, p ≠ p' → χ c p q ≠ χ c p' q
  χ'mem : ∀ c ∈ C, c.1 = c.2 → ∀ p ∈ P c.1, ∀ q ∈ P c.1, p ≠ q → χ' c p q ∈ P (thirdIndex c)
  χ'sym : ∀ c ∈ C, c.1 = c.2 → ∀ p ∈ P c.1, ∀ q ∈ P c.1, χ' c p q = χ' c q p
  χ'proper : ∀ c ∈ C, c.1 = c.2 → ∀ p ∈ P c.1, ∀ q ∈ P c.1, ∀ r ∈ P c.1,
      p ≠ q → p ≠ r → q ≠ r → χ' c p q ≠ χ' c p r

variable {C : Finset (ℤ × ℤ)} {P : ℤ → Finset ℕ} {χ χ' : ℤ × ℤ → ℕ → ℕ → ℕ}

/-- A prime lies in at most one bin. -/
lemma bin_unique (hdisj : ∀ i j : ℤ, i < j → Disjoint (P i) (P j)) {x : ℕ} {a b : ℤ}
    (ha : x ∈ P a) (hb : x ∈ P b) : a = b := by
  by_contra hab
  rcases lt_or_gt_of_ne hab with h | h
  · exact Finset.disjoint_left.mp (hdisj a b h) ha hb
  · exact Finset.disjoint_left.mp (hdisj b a h) hb ha

/-
Each member of `hyperFamily` has exactly three elements.
-/
lemma hyperFamily_card3 (hadm : ∀ c ∈ C, Admissible c) (hdisj : ∀ i j : ℤ, i < j → Disjoint (P i) (P j))
    (hcol : ColData C P χ χ') :
    ∀ E ∈ hyperFamily C P χ χ', E.card = 3 := by
  intro E hE
  rw [mem_hyperFamily] at hE
  cases' hE with hcase1 hcase2;
  · obtain ⟨ c, hc, hc', p, hp, q, hq, rfl ⟩ := hcase1;
    have h_distinct : p ≠ q ∧ p ≠ χ c p q ∧ q ≠ χ c p q := by
      have := hcol.χmem c hc hc' p hp q hq; simp_all +decide [ Finset.disjoint_left ] ;
      exact ⟨ fun h => hdisj _ _ hc' hp ( h.symm ▸ hq ), fun h => hdisj _ _ ( by linarith [ cell_order c ( hadm _ _ hc ) ] ) hp ( h.symm ▸ this ), fun h => hdisj _ _ ( by linarith [ cell_order c ( hadm _ _ hc ) ] ) hq ( h.symm ▸ this ) ⟩;
    grind;
  · rcases hcase2 with ⟨ c, hc, hc', p, hp, q, hq, hpq, rfl ⟩;
    have h_card : p ≠ q ∧ p ≠ χ' c p q ∧ q ≠ χ' c p q := by
      have := hcol.χ'mem c hc hc' p hp q hq ( by linarith ) ; simp_all +decide [ Finset.disjoint_left ] ;
      exact ⟨ ne_of_lt hpq, fun h => hdisj _ _ ( by linarith [ cell_order c ( hadm _ _ hc ) ] ) hp ( h.symm ▸ this ), fun h => hdisj _ _ ( by linarith [ cell_order c ( hadm _ _ hc ) ] ) hq ( h.symm ▸ this ) ⟩;
    rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton ] <;> aesop

/-
Each member of `hyperFamily` consists of primes.
-/
lemma hyperFamily_prime (hprime : ∀ r : ℤ, ∀ p ∈ P r, Nat.Prime p) (hcol : ColData C P χ χ') :
    ∀ E ∈ hyperFamily C P χ χ', ∀ p ∈ E, Nat.Prime p := by
  intros E hE p hp
  rw [mem_hyperFamily] at hE
  cases' hE with hE hE';
  · rcases hE with ⟨ c, hc₁, hc₂, p, hp₁, q, hq₁, rfl ⟩ ; simp_all +decide [ Finset.mem_insert, Finset.mem_singleton ] ;
    rcases hp with ( rfl | rfl | rfl ) <;> [ exact hprime _ _ hp₁; exact hprime _ _ hq₁; exact hprime _ _ ( hcol.χmem _ hc₁ hc₂ _ hp₁ _ hq₁ ) ];
  · grind +splitIndPred

/-- Each member of `hyperFamily` has product at most `V`. -/
lemma hyperFamily_prod (V : ℕ) (hadm : ∀ c ∈ C, Admissible c)
    (hdisj : ∀ i j : ℤ, i < j → Disjoint (P i) (P j))
    (hprod : ∀ c ∈ C, ∀ p ∈ P c.1, ∀ q ∈ P c.2, ∀ r ∈ P (thirdIndex c), p * q * r ≤ V)
    (hcol : ColData C P χ χ') :
    ∀ E ∈ hyperFamily C P χ χ', (∏ p ∈ E, p) ≤ V := by
  intro E hE
  rw [mem_hyperFamily] at hE
  cases hE with
  | inl hcase =>
    obtain ⟨c, hc, hc', p, hp, q, hq, rfl⟩ := hcase
    have hord := cell_order c (hadm c hc)
    have hx : χ c p q ∈ P (thirdIndex c) := hcol.χmem c hc hc' p hp q hq
    have hpq : p ≠ q := fun h => Finset.disjoint_left.mp (hdisj c.1 c.2 hc') hp (h.symm ▸ hq)
    have hpx : p ≠ χ c p q := fun h =>
      Finset.disjoint_left.mp (hdisj c.1 (thirdIndex c) (by omega)) hp (h.symm ▸ hx)
    have hqx : q ≠ χ c p q := fun h =>
      Finset.disjoint_left.mp (hdisj c.2 (thirdIndex c) (by omega)) hq (h.symm ▸ hx)
    rw [Finset.prod_insert (by simp [Finset.mem_insert, hpq, hpx]),
      Finset.prod_insert (by simp [hqx]), Finset.prod_singleton]
    calc p * (q * χ c p q) = p * q * χ c p q := by ring
      _ ≤ V := hprod c hc p hp q hq _ hx
  | inr hcase =>
    obtain ⟨c, hc, hc', p, hp, q, hq, hpq, rfl⟩ := hcase
    have hord := cell_order c (hadm c hc)
    have hx : χ' c p q ∈ P (thirdIndex c) := hcol.χ'mem c hc hc' p hp q hq (ne_of_lt hpq)
    have hpx : p ≠ χ' c p q := fun h =>
      Finset.disjoint_left.mp (hdisj c.1 (thirdIndex c) (by omega)) hp (h.symm ▸ hx)
    have hqx : q ≠ χ' c p q := fun h =>
      Finset.disjoint_left.mp (hdisj c.1 (thirdIndex c) (by omega)) hq (h.symm ▸ hx)
    have hq2 : q ∈ P c.2 := hc' ▸ hq
    rw [Finset.prod_insert (by simp [Finset.mem_insert, ne_of_lt hpq, hpx]),
      Finset.prod_insert (by simp [hqx]), Finset.prod_singleton]
    calc p * (q * χ' c p q) = p * q * χ' c p q := by ring
      _ ≤ V := hprod c hc p hp q hq2 _ hx

/-- The family `hyperFamily` is linear: two distinct members meet in ≤ 1 element. -/
lemma hyperFamily_linear (hadm : ∀ c ∈ C, Admissible c)
    (hdisj : ∀ i j : ℤ, i < j → Disjoint (P i) (P j)) (hcol : ColData C P χ χ') :
    ∀ E ∈ hyperFamily C P χ χ', ∀ E' ∈ hyperFamily C P χ χ', E ≠ E' → (E ∩ E').card ≤ 1 := by
  have huniq : ∀ (x : ℕ) (a b : ℤ), x ∈ P a → x ∈ P b → a = b :=
    fun x a b ha hb => bin_unique hdisj ha hb
  intro E hE E' hE' hne
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [Finset.mem_inter] at ha hb
  by_contra hab
  apply hne
  rw [mem_hyperFamily] at hE hE'
  obtain ⟨haE, haE'⟩ := ha
  obtain ⟨hbE, hbE'⟩ := hb
  rcases hE with ⟨c, hc, hlt, p, hp, q, hq, rfl⟩ | ⟨c, hc, he, p, hp, q, hq, hpq, rfl⟩ <;>
    rcases hE' with ⟨d, hd, hltd, r, hr, s, hs, rfl⟩ | ⟨d, hd, hed, r, hr, s, hs, hrs, rfl⟩
  · -- off / off
    have hoc := cell_order c (hadm c hc)
    have hod := cell_order d (hadm d hd)
    have hwc : χ c p q ∈ P (thirdIndex c) := hcol.χmem c hc hlt p hp q hq
    have hwd : χ d r s ∈ P (thirdIndex d) := hcol.χmem d hd hltd r hr s hs
    have h2c := hcol.χ2 c hc hlt
    have h1c := hcol.χ1 c hc hlt
    simp only [Finset.mem_insert, Finset.mem_singleton] at haE haE' hbE hbE'
    grind
  · -- off / diag
    have hoc := cell_order c (hadm c hc)
    have hod := cell_order d (hadm d hd)
    have hwc : χ c p q ∈ P (thirdIndex c) := hcol.χmem c hc hlt p hp q hq
    have hwd : χ' d r s ∈ P (thirdIndex d) := hcol.χ'mem d hd hed r hr s hs (ne_of_lt hrs)
    simp only [Finset.mem_insert, Finset.mem_singleton] at haE haE' hbE hbE'
    grind
  · -- diag / off
    have hoc := cell_order c (hadm c hc)
    have hod := cell_order d (hadm d hd)
    have hwc : χ' c p q ∈ P (thirdIndex c) := hcol.χ'mem c hc he p hp q hq (ne_of_lt hpq)
    have hwd : χ d r s ∈ P (thirdIndex d) := hcol.χmem d hd hltd r hr s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at haE haE' hbE hbE'
    grind
  · -- diag / diag
    have hoc := cell_order c (hadm c hc)
    have hod := cell_order d (hadm d hd)
    have hwc : χ' c p q ∈ P (thirdIndex c) := hcol.χ'mem c hc he p hp q hq (ne_of_lt hpq)
    have hwd : χ' d r s ∈ P (thirdIndex d) := hcol.χ'mem d hd hed r hr s hs (ne_of_lt hrs)
    have hprc := hcol.χ'proper c hc he
    have hprd := hcol.χ'proper d hd hed
    have hsymc := hcol.χ'sym c hc he
    have hsymd := hcol.χ'sym d hd hed
    simp only [Finset.mem_insert, Finset.mem_singleton] at haE haE' hbE hbE'
    grind

/-- The vertex set of `hyperFamily` is small. -/
lemma hyperFamily_vset (hcol : ColData C P χ χ') :
    (Vset (hyperFamily C P χ χ')).card ≤ ∑ r ∈ Rset C, (P r).card := by
  refine le_trans (Finset.card_le_card ?_) Finset.card_biUnion_le
  intro v hv
  rw [Vset, Finset.mem_biUnion] at hv
  obtain ⟨E, hE, hvE⟩ := hv
  simp only [id] at hvE
  rw [mem_hyperFamily] at hE
  rw [Finset.mem_biUnion]
  rcases hE with ⟨c, hc, hc', p, hp, q, hq, rfl⟩ | ⟨c, hc, hc', p, hp, q, hq, hpq, rfl⟩
  · have h1 : c.1 ∈ Rset C := by
      simp only [Rset, Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inl ⟨c, hc, rfl⟩)
    have h2 : c.2 ∈ Rset C := by
      simp only [Rset, Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inr ⟨c, hc, rfl⟩)
    have h3 : thirdIndex c ∈ Rset C := by
      simp only [Rset, Finset.mem_union, Finset.mem_image]; exact Or.inr ⟨c, hc, rfl⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvE
    rcases hvE with rfl | rfl | rfl
    · exact ⟨c.1, h1, hp⟩
    · exact ⟨c.2, h2, hq⟩
    · exact ⟨thirdIndex c, h3, hcol.χmem c hc hc' p hp q hq⟩
  · have h1 : c.1 ∈ Rset C := by
      simp only [Rset, Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inl ⟨c, hc, rfl⟩)
    have h3 : thirdIndex c ∈ Rset C := by
      simp only [Rset, Finset.mem_union, Finset.mem_image]; exact Or.inr ⟨c, hc, rfl⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvE
    rcases hvE with rfl | rfl | rfl
    · exact ⟨c.1, h1, hp⟩
    · exact ⟨c.1, h1, hq⟩
    · exact ⟨thirdIndex c, h3, hcol.χ'mem c hc hc' p hp q hq (ne_of_lt hpq)⟩

/-- The number of strictly-increasing pairs from `s × s` is `s.card.choose 2`. -/
lemma card_filter_lt_product (s : Finset ℕ) :
    ((s ×ˢ s).filter (fun pq => pq.1 < pq.2)).card = s.card.choose 2 := by
  rw [← Finset.card_powersetCard]
  apply Finset.card_bij (fun pq _ => ({pq.1, pq.2} : Finset ℕ))
  · rintro ⟨p, q⟩ hpq
    simp only [Finset.mem_filter, Finset.mem_product] at hpq
    simp only [Finset.mem_powersetCard]
    refine ⟨?_, ?_⟩
    · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hpq.1.1
      · exact hpq.1.2
    · rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; omega), Finset.card_singleton]
  · rintro ⟨p, q⟩ hpq ⟨p', q'⟩ hpq' h
    simp only [Finset.mem_filter, Finset.mem_product] at hpq hpq'
    simp only [Finset.ext_iff, Finset.mem_insert, Finset.mem_singleton] at h
    have := h p; have := h q; have := h p'; have := h q'
    have h1 := hpq.2; have h2 := hpq'.2
    ext <;> simp <;> omega
  · rintro t ht
    simp only [Finset.mem_powersetCard] at ht
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp ht.2
    rcases lt_or_gt_of_ne hxy with h | h
    · exact ⟨(x, y), by simp only [Finset.mem_filter, Finset.mem_product]; exact ⟨⟨ht.1 (by simp), ht.1 (by simp)⟩, h⟩, by simp⟩
    · exact ⟨(y, x), by simp only [Finset.mem_filter, Finset.mem_product]; exact ⟨⟨ht.1 (by simp), ht.1 (by simp)⟩, h⟩, by rw [Finset.pair_comm]⟩

/-- Exact edge count of `hyperFamily`. -/
lemma hyperFamily_card (hadm : ∀ c ∈ C, Admissible c)
    (hdisj : ∀ i j : ℤ, i < j → Disjoint (P i) (P j)) (hcol : ColData C P χ χ') :
    (hyperFamily C P χ χ').card =
      (∑ c ∈ C.filter (fun c => c.1 < c.2), (P c.1).card * (P c.2).card)
        + ∑ c ∈ C.filter (fun c => c.1 = c.2), ((P c.1).card).choose 2 := by
  classical
  have huniq : ∀ (x : ℕ) (a b : ℤ), x ∈ P a → x ∈ P b → a = b :=
    fun x a b ha hb => bin_unique hdisj ha hb
  -- injectivity on off-diagonal cells
  have hinjoff : ∀ c ∈ C.filter (fun c => c.1 < c.2),
      Set.InjOn (fun pq : ℕ × ℕ => ({pq.1, pq.2, χ c pq.1 pq.2} : Finset ℕ)) ↑(P c.1 ×ˢ P c.2) := by
    intro c hcf pq hpq pq' hpq' heq
    rw [Finset.mem_filter] at hcf
    obtain ⟨hc, hlt⟩ := hcf
    have hoc := cell_order c (hadm c hc)
    rw [Finset.mem_coe, Finset.mem_product] at hpq hpq'
    have hw := hcol.χmem c hc hlt pq.1 hpq.1 pq.2 hpq.2
    have hw' := hcol.χmem c hc hlt pq'.1 hpq'.1 pq'.2 hpq'.2
    have hp := hpq.1; have hq := hpq.2; have hp' := hpq'.1; have hq' := hpq'.2
    simp only [] at heq
    have m1 : pq.1 ∈ ({pq'.1, pq'.2, χ c pq'.1 pq'.2} : Finset ℕ) := by rw [← heq]; simp
    have m2 : pq.2 ∈ ({pq'.1, pq'.2, χ c pq'.1 pq'.2} : Finset ℕ) := by rw [← heq]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at m1 m2
    have key1 : pq.1 = pq'.1 := by
      rcases m1 with h | h | h
      · exact h
      · exact absurd (huniq pq.1 c.1 c.2 hp (by rw [h]; exact hq')) (by omega)
      · exact absurd (huniq pq.1 c.1 (thirdIndex c) hp (by rw [h]; exact hw')) (by omega)
    have key2 : pq.2 = pq'.2 := by
      rcases m2 with h | h | h
      · exact absurd (huniq pq.2 c.2 c.1 hq (by rw [h]; exact hp')) (by omega)
      · exact h
      · exact absurd (huniq pq.2 c.2 (thirdIndex c) hq (by rw [h]; exact hw')) (by omega)
    exact Prod.ext key1 key2
  -- injectivity on diagonal cells
  have hinjdiag : ∀ c ∈ C.filter (fun c => c.1 = c.2),
      Set.InjOn (fun pq : ℕ × ℕ => ({pq.1, pq.2, χ' c pq.1 pq.2} : Finset ℕ))
        ↑((P c.1 ×ˢ P c.1).filter (fun pq => pq.1 < pq.2)) := by
    intro c hcf pq hpq pq' hpq' heq
    rw [Finset.mem_filter] at hcf
    obtain ⟨hc, he⟩ := hcf
    have hoc := cell_order c (hadm c hc)
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hpq hpq'
    have hw := hcol.χ'mem c hc he pq.1 hpq.1.1 pq.2 hpq.1.2 (ne_of_lt hpq.2)
    have hw' := hcol.χ'mem c hc he pq'.1 hpq'.1.1 pq'.2 hpq'.1.2 (ne_of_lt hpq'.2)
    have hp := hpq.1.1; have hq := hpq.1.2; have hp' := hpq'.1.1; have hq' := hpq'.1.2
    have hlt1 := hpq.2; have hlt2 := hpq'.2
    simp only [] at heq
    have m1 : pq.1 ∈ ({pq'.1, pq'.2, χ' c pq'.1 pq'.2} : Finset ℕ) := by rw [← heq]; simp
    have m2 : pq.2 ∈ ({pq'.1, pq'.2, χ' c pq'.1 pq'.2} : Finset ℕ) := by rw [← heq]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at m1 m2
    have hne1 : ¬ pq.1 = χ' c pq'.1 pq'.2 := fun h =>
      absurd (huniq pq.1 c.1 (thirdIndex c) hp (by rw [h]; exact hw')) (by omega)
    have hne2 : ¬ pq.2 = χ' c pq'.1 pq'.2 := fun h =>
      absurd (huniq pq.2 c.1 (thirdIndex c) hq (by rw [h]; exact hw')) (by omega)
    have hd1 : pq.1 = pq'.1 ∨ pq.1 = pq'.2 := by tauto
    have hd2 : pq.2 = pq'.1 ∨ pq.2 = pq'.2 := by tauto
    rcases hd1 with h1 | h1 <;> rcases hd2 with h2 | h2 <;> refine Prod.ext ?_ ?_ <;> omega
  -- distinct off-diagonal cells give disjoint triple sets
  have hpdoff : ∀ c ∈ C.filter (fun c => c.1 < c.2), ∀ d ∈ C.filter (fun c => c.1 < c.2), c ≠ d →
      Disjoint ((P c.1 ×ˢ P c.2).image (fun pq => ({pq.1, pq.2, χ c pq.1 pq.2} : Finset ℕ)))
               ((P d.1 ×ˢ P d.2).image (fun pq => ({pq.1, pq.2, χ d pq.1 pq.2} : Finset ℕ))) := by
    intro c hcf d hdf hcd
    rw [Finset.mem_filter] at hcf hdf
    obtain ⟨hc, hlt⟩ := hcf; obtain ⟨hd, hltd⟩ := hdf
    have hoc := cell_order c (hadm c hc); have hod := cell_order d (hadm d hd)
    rw [Finset.disjoint_left]
    intro E hE hE'
    rw [Finset.mem_image] at hE hE'
    obtain ⟨pq, hpq, rfl⟩ := hE
    obtain ⟨pq', hpq', heq⟩ := hE'
    rw [Finset.mem_product] at hpq hpq'
    have hw := hcol.χmem c hc hlt pq.1 hpq.1 pq.2 hpq.2
    have hw' := hcol.χmem d hd hltd pq'.1 hpq'.1 pq'.2 hpq'.2
    have hp := hpq.1; have hq := hpq.2; have hp' := hpq'.1; have hq' := hpq'.2
    have m1 : pq.1 ∈ ({pq'.1, pq'.2, χ d pq'.1 pq'.2} : Finset ℕ) := by rw [heq]; simp
    have m2 : pq.2 ∈ ({pq'.1, pq'.2, χ d pq'.1 pq'.2} : Finset ℕ) := by rw [heq]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at m1 m2
    apply hcd
    have e1 : c.1 = d.1 ∨ c.1 = d.2 ∨ c.1 = thirdIndex d := by
      rcases m1 with h | h | h
      · exact Or.inl (huniq pq.1 c.1 d.1 hp (by rw [h]; exact hp'))
      · exact Or.inr (Or.inl (huniq pq.1 c.1 d.2 hp (by rw [h]; exact hq')))
      · exact Or.inr (Or.inr (huniq pq.1 c.1 (thirdIndex d) hp (by rw [h]; exact hw')))
    have e2 : c.2 = d.1 ∨ c.2 = d.2 ∨ c.2 = thirdIndex d := by
      rcases m2 with h | h | h
      · exact Or.inl (huniq pq.2 c.2 d.1 hq (by rw [h]; exact hp'))
      · exact Or.inr (Or.inl (huniq pq.2 c.2 d.2 hq (by rw [h]; exact hq')))
      · exact Or.inr (Or.inr (huniq pq.2 c.2 (thirdIndex d) hq (by rw [h]; exact hw')))
    refine Prod.ext ?_ ?_ <;> rcases e1 with h1 | h1 | h1 <;> rcases e2 with h2 | h2 | h2 <;> omega
  -- distinct diagonal cells give disjoint triple sets
  have hpddiag : ∀ c ∈ C.filter (fun c => c.1 = c.2), ∀ d ∈ C.filter (fun c => c.1 = c.2), c ≠ d →
      Disjoint (((P c.1 ×ˢ P c.1).filter (fun pq => pq.1 < pq.2)).image
                  (fun pq => ({pq.1, pq.2, χ' c pq.1 pq.2} : Finset ℕ)))
               (((P d.1 ×ˢ P d.1).filter (fun pq => pq.1 < pq.2)).image
                  (fun pq => ({pq.1, pq.2, χ' d pq.1 pq.2} : Finset ℕ))) := by
    intro c hcf d hdf hcd
    rw [Finset.mem_filter] at hcf hdf
    obtain ⟨hc, he⟩ := hcf; obtain ⟨hd, hed⟩ := hdf
    have hoc := cell_order c (hadm c hc); have hod := cell_order d (hadm d hd)
    rw [Finset.disjoint_left]
    intro E hE hE'
    rw [Finset.mem_image] at hE hE'
    obtain ⟨pq, hpq, rfl⟩ := hE
    obtain ⟨pq', hpq', heq⟩ := hE'
    rw [Finset.mem_filter, Finset.mem_product] at hpq hpq'
    have hw := hcol.χ'mem c hc he pq.1 hpq.1.1 pq.2 hpq.1.2 (ne_of_lt hpq.2)
    have hw' := hcol.χ'mem d hd hed pq'.1 hpq'.1.1 pq'.2 hpq'.1.2 (ne_of_lt hpq'.2)
    have hp := hpq.1.1; have hq := hpq.1.2; have hp' := hpq'.1.1; have hq' := hpq'.1.2
    have hlt1 := hpq.2
    have m1 : pq.1 ∈ ({pq'.1, pq'.2, χ' d pq'.1 pq'.2} : Finset ℕ) := by rw [heq]; simp
    have m2 : pq.2 ∈ ({pq'.1, pq'.2, χ' d pq'.1 pq'.2} : Finset ℕ) := by rw [heq]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at m1 m2
    apply hcd
    have hkey : c.1 = d.1 := by
      rcases m1 with h | h | h <;> rcases m2 with h' | h' | h' <;>
        first
          | exact huniq pq.1 c.1 d.1 hp (by rw [h]; exact hp')
          | exact huniq pq.1 c.1 d.1 hp (by rw [h]; exact hq')
          | exact huniq pq.2 c.1 d.1 hq (by rw [h']; exact hp')
          | exact huniq pq.2 c.1 d.1 hq (by rw [h']; exact hq')
          | exact absurd (h.trans h'.symm) (Nat.ne_of_lt hlt1)
    exact Prod.ext hkey (by omega)
  -- the off-diagonal and diagonal parts are disjoint
  have hAB : Disjoint
      ((C.filter (fun c => c.1 < c.2)).biUnion
        (fun c => (P c.1 ×ˢ P c.2).image (fun pq => ({pq.1, pq.2, χ c pq.1 pq.2} : Finset ℕ))))
      ((C.filter (fun c => c.1 = c.2)).biUnion
        (fun c => ((P c.1 ×ˢ P c.1).filter (fun pq => pq.1 < pq.2)).image
          (fun pq => ({pq.1, pq.2, χ' c pq.1 pq.2} : Finset ℕ)))) := by
    rw [Finset.disjoint_left]
    intro E hE hE'
    rw [Finset.mem_biUnion] at hE hE'
    obtain ⟨c, hcf, hEc⟩ := hE
    obtain ⟨d, hdf, hEd⟩ := hE'
    rw [Finset.mem_filter] at hcf hdf
    obtain ⟨hc, hlt⟩ := hcf; obtain ⟨hd, hed⟩ := hdf
    have hoc := cell_order c (hadm c hc); have hod := cell_order d (hadm d hd)
    rw [Finset.mem_image] at hEc hEd
    obtain ⟨pq, hpq, rfl⟩ := hEc
    obtain ⟨pq', hpq', heq⟩ := hEd
    rw [Finset.mem_product] at hpq
    rw [Finset.mem_filter, Finset.mem_product] at hpq'
    have hw := hcol.χmem c hc hlt pq.1 hpq.1 pq.2 hpq.2
    have hp := hpq.1; have hq := hpq.2; have hp' := hpq'.1.1; have hq' := hpq'.1.2
    have hlt' := hpq'.2
    have n1 : pq'.1 ∈ ({pq.1, pq.2, χ c pq.1 pq.2} : Finset ℕ) := by rw [← heq]; simp
    have n2 : pq'.2 ∈ ({pq.1, pq.2, χ c pq.1 pq.2} : Finset ℕ) := by rw [← heq]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at n1 n2
    exfalso
    rcases n1 with h1 | h1 | h1 <;> rcases n2 with h2 | h2 | h2
    · exact absurd (h1.trans h2.symm) (Nat.ne_of_lt hlt')
    · have := huniq pq'.1 d.1 c.1 hp' (by rw [h1]; exact hp)
      have := huniq pq'.2 d.1 c.2 hq' (by rw [h2]; exact hq); omega
    · have := huniq pq'.1 d.1 c.1 hp' (by rw [h1]; exact hp)
      have := huniq pq'.2 d.1 (thirdIndex c) hq' (by rw [h2]; exact hw); omega
    · have := huniq pq'.1 d.1 c.2 hp' (by rw [h1]; exact hq)
      have := huniq pq'.2 d.1 c.1 hq' (by rw [h2]; exact hp); omega
    · exact absurd (h1.trans h2.symm) (Nat.ne_of_lt hlt')
    · have := huniq pq'.1 d.1 c.2 hp' (by rw [h1]; exact hq)
      have := huniq pq'.2 d.1 (thirdIndex c) hq' (by rw [h2]; exact hw); omega
    · have := huniq pq'.1 d.1 (thirdIndex c) hp' (by rw [h1]; exact hw)
      have := huniq pq'.2 d.1 c.1 hq' (by rw [h2]; exact hp); omega
    · have := huniq pq'.1 d.1 (thirdIndex c) hp' (by rw [h1]; exact hw)
      have := huniq pq'.2 d.1 c.2 hq' (by rw [h2]; exact hq); omega
    · exact absurd (h1.trans h2.symm) (Nat.ne_of_lt hlt')
  rw [hyperFamily, Finset.card_union_of_disjoint hAB,
      Finset.card_biUnion hpdoff, Finset.card_biUnion hpddiag]
  congr 1
  · apply Finset.sum_congr rfl
    intro c hc
    rw [Finset.card_image_of_injOn (hinjoff c hc), Finset.card_product]
  · apply Finset.sum_congr rfl
    intro c hc
    rw [Finset.card_image_of_injOn (hinjdiag c hc), card_filter_lt_product]

/-
Given admissible cells `C`, pairwise-disjoint all-prime bins `P`, a third-bin
size condition, and product/vertex bounds by `V`, there is a linear family of
prime triples with the exact edge count and vertex bound. This is the purely
combinatorial core of `exists_hypergraph`.
-/
lemma abstract_hypergraph (C : Finset (ℤ × ℤ)) (P : ℤ → Finset ℕ) (V : ℕ)
    (hadm : ∀ c ∈ C, Admissible c)
    (hdisj : ∀ i j : ℤ, i < j → Disjoint (P i) (P j))
    (hprime : ∀ r : ℤ, ∀ p ∈ P r, Nat.Prime p)
    (hbig : ∀ c ∈ C, max (P c.1).card (P c.2).card ≤ (P (thirdIndex c)).card)
    (hprod : ∀ c ∈ C, ∀ p ∈ P c.1, ∀ q ∈ P c.2, ∀ r ∈ P (thirdIndex c), p * q * r ≤ V) :
    ∃ H : Finset (Finset ℕ),
      (∀ E ∈ H, E.card = 3) ∧
      (∀ E ∈ H, ∀ p ∈ E, Nat.Prime p) ∧
      (∀ E ∈ H, (∏ p ∈ E, p) ≤ V) ∧
      (∀ E ∈ H, ∀ E' ∈ H, E ≠ E' → (E ∩ E').card ≤ 1) ∧
      (Vset H).card ≤ ∑ r ∈ Rset C, (P r).card ∧
      H.card =
        (∑ c ∈ C.filter (fun c => c.1 < c.2), (P c.1).card * (P c.2).card)
          + ∑ c ∈ C.filter (fun c => c.1 = c.2), ((P c.1).card).choose 2 := by
  -- Choose colorings `χ` and `χ'` satisfying the required properties.
  obtain ⟨χ, χ', hχ⟩ : ∃ χ : ℤ × ℤ → ℕ → ℕ → ℕ, ∃ χ' : ℤ × ℤ → ℕ → ℕ → ℕ, ColData C P χ χ' := by
    have h_off_diag : ∀ c ∈ C, c.1 < c.2 → ∃ χ : ℕ → ℕ → ℕ, (∀ p ∈ P c.1, ∀ q ∈ P c.2, χ p q ∈ P (thirdIndex c)) ∧ (∀ p ∈ P c.1, ∀ q ∈ P c.2, ∀ q' ∈ P c.2, q ≠ q' → χ p q ≠ χ p q') ∧ (∀ p ∈ P c.1, ∀ p' ∈ P c.1, ∀ q ∈ P c.2, p ≠ p' → χ p q ≠ χ p' q) := by
      intros c hc hlt
      obtain ⟨χ, hχ⟩ := complete_bipartite_colouring (P c.1) (P c.2) (P (thirdIndex c)) (by
      exact hbig c hc);
      exact ⟨ χ, hχ ⟩;
    have h_diag : ∀ c ∈ C, c.1 = c.2 → ∃ χ' : ℕ → ℕ → ℕ, (∀ p ∈ P c.1, ∀ q ∈ P c.1, p ≠ q → χ' p q ∈ P (thirdIndex c)) ∧ (∀ p ∈ P c.1, ∀ q ∈ P c.1, χ' p q = χ' q p) ∧ (∀ p ∈ P c.1, ∀ q ∈ P c.1, ∀ r ∈ P c.1, p ≠ q → p ≠ r → q ≠ r → χ' p q ≠ χ' p r) := by
      intro c hc h_eq
      obtain ⟨χ', hχ'⟩ := complete_graph_colouring (P c.1) (P (thirdIndex c)) (by
      exact le_trans ( le_max_left _ _ ) ( hbig c hc ));
      exact ⟨ χ', hχ' ⟩;
    choose! χ hχ₁ hχ₂ hχ₃ using h_off_diag;
    choose! χ' hχ'₁ hχ'₂ hχ'₃ using h_diag;
    exact ⟨ χ, χ', ⟨ hχ₁, hχ₂, hχ₃, hχ'₁, hχ'₂, hχ'₃ ⟩ ⟩;
  refine' ⟨ _, hyperFamily_card3 hadm hdisj hχ, hyperFamily_prime hprime hχ, hyperFamily_prod V hadm hdisj hprod hχ, hyperFamily_linear hadm hdisj hχ, hyperFamily_vset hχ, hyperFamily_card hadm hdisj hχ ⟩

/-
For fixed `h > 0` and finite admissible `C`, for all large `n` there is a linear
family `H` of prime triples, each with product `≤ n`, with the exact edge count
and a vertex bound.
-/
lemma exists_hypergraph (hpnt : PNT) (h : ℝ) (hh : 0 < h) (C : Finset (ℤ × ℤ))
    (hC : ∀ c ∈ C, Admissible c) :
    ∀ᶠ n : ℕ in atTop, ∃ H : Finset (Finset ℕ),
      (∀ E ∈ H, E.card = 3) ∧
      (∀ E ∈ H, ∀ p ∈ E, Nat.Prime p) ∧
      (∀ E ∈ H, (∏ p ∈ E, p) ≤ n) ∧
      (∀ E ∈ H, ∀ E' ∈ H, E ≠ E' → (E ∩ E').card ≤ 1) ∧
      (Vset H).card ≤ ∑ r ∈ Rset C, mbin h n r ∧
      H.card =
        (∑ c ∈ C.filter (fun c => c.1 < c.2), mbin h n c.1 * mbin h n c.2)
          + ∑ c ∈ C.filter (fun c => c.1 = c.2), (mbin h n c.1).choose 2 := by
  filter_upwards [ Erdos793.third_bin_large hpnt h hh C hC, Erdos793.triple_prod_le_n_eventually h C ] with n hn hn';
  simpa only [mbin] using abstract_hypergraph C (Pbin h n) n hC
    (fun i j hij => Pbin_disjoint h hh n hij)
    (fun r p hp => Pbin_prime h n r hp) hn hn'

/-
`|H_n(C)| / M² → 9 W_h(C)`.
-/
lemma edge_count_asymp (hpnt : PNT) (h : ℝ) (hh : 0 < h) (C : Finset (ℤ × ℤ)) :
    Tendsto (fun n : ℕ =>
      ((∑ c ∈ C.filter (fun c => c.1 < c.2), mbin h n c.1 * mbin h n c.2)
        + ∑ c ∈ C.filter (fun c => c.1 = c.2), (mbin h n c.1).choose 2 : ℝ)
        / (Mval n) ^ 2) atTop (𝓝 (9 * Wh h C)) := by
  -- Each product over pairs (i, j) tends to 9 * Delta h i * Delta h j as n tends to infinity.
  have h_prod : ∀ c ∈ C, Filter.Tendsto (fun n => (mbin h n c.1 * mbin h n c.2 : ℝ) / (Mval n)^2) Filter.atTop (nhds (9 * Delta h c.1 * Delta h c.2)) := by
    intro c hc;
    convert Filter.Tendsto.mul ( bin_sizes hpnt h hh c.1 ) ( bin_sizes hpnt h hh c.2 ) using 2 <;> ring;
  -- Each binomial coefficient over the diagonal pairs tends to (9/2) * Delta h i^2 as n tends to infinity.
  have h_diag : ∀ c ∈ C, Filter.Tendsto (fun n => (Nat.choose (mbin h n c.1) 2 : ℝ) / (Mval n)^2) Filter.atTop (nhds ((9 / 2) * (Delta h c.1)^2)) := by
    intro c hc
    have h_diag_term : Filter.Tendsto (fun n => ((mbin h n c.1 : ℝ) * ((mbin h n c.1 : ℝ) - 1)) / (2 * (Mval n)^2)) Filter.atTop (nhds ((9 / 2) * (Delta h c.1)^2)) := by
      have h_diag_term : Filter.Tendsto (fun n => ((mbin h n c.1 : ℝ) / Mval n) * ((mbin h n c.1 : ℝ) / Mval n - 1 / Mval n)) Filter.atTop (nhds (9 * (Delta h c.1)^2)) := by
        have h_diag_term : Filter.Tendsto (fun n => ((mbin h n c.1 : ℝ) / Mval n)) Filter.atTop (nhds (3 * Delta h c.1)) := by
          convert bin_sizes hpnt h hh c.1 using 1;
        convert h_diag_term.mul ( h_diag_term.sub ( tendsto_const_nhds.div_atTop ( show Filter.Tendsto ( fun n : ℕ => Mval n ) Filter.atTop Filter.atTop from tendsto_M_atTop ) ) ) using 2 ; ring;
      convert h_diag_term.div_const 2 using 2 <;> ring;
    convert h_diag_term using 2 ; norm_num [ Nat.choose_two_right ] ; ring_nf;
    cases k : mbin h ‹_› c.1 <;> simp +decide [Nat.dvd_iff_mod_eq_zero, Nat.mod_two_of_bodd] ; ring;
  simp_all +decide [ Finset.sum_div _ _ _, add_div ];
  convert Filter.Tendsto.add ( tendsto_finsetSum _ fun x hx => h_prod _ _ <| Finset.mem_filter.mp hx |>.1 ) ( tendsto_finsetSum _ fun x hx => h_diag _ _ <| Finset.mem_filter.mp hx |>.1 ) using 2 ; norm_num [ Wh ] ; ring_nf;
  rw [ Finset.sum_mul _ _ _, Finset.sum_mul _ _ _ ]

/-
Vertex count is `o(S)`.
-/
lemma vertex_count_asymp (hpnt : PNT) (h : ℝ) (hh : 0 < h) (C : Finset (ℤ × ℤ)) :
    Tendsto (fun n : ℕ => (∑ r ∈ Rset C, mbin h n r : ℝ) / S n) atTop (𝓝 0) := by
  -- Apply the fact that the sum of a finite number of terms each tending to zero also tends to zero.
  have h_sum_zero : ∀ r ∈ Rset C, Filter.Tendsto (fun n : ℕ => (mbin h n r : ℝ) / S n) Filter.atTop (nhds 0) := by
    intro r hr
    have h_lim : Filter.Tendsto (fun n => (mbin h n r : ℝ) / Mval n * (Mval n / S n)) Filter.atTop (nhds 0) := by
      simpa [Mval] using (bin_sizes hpnt h hh r).mul M_div_S_tendsto_zero
    refine h_lim.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn; rw [ div_mul_div_cancel₀ ( ne_of_gt ( show 0 < Mval n from div_pos ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| pos_of_gt hn ) _ ) <| Real.log_pos <| Nat.one_lt_cast.mpr hn ) ) ] );
  simpa [ Finset.sum_div _ _ _ ] using tendsto_finsetSum _ h_sum_zero

/-
For every `ε > 0`, eventually `F(n) - π(n) ≥ (27/2 - ε) S`.
-/
lemma F_lower (hpnt : PNT) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (27/2 - ε) * S n ≤ (F n : ℝ) - Nat.primeCounting n := by
  obtain ⟨ h, hh, N, hN ⟩ := Erdos793.near_maximal_weight ε hε;
  -- Set `C := CN N`, `hC := CN_admissible N`, `L := 9 * Wh h C`, so `L > 27/2 - ε`, `edge n` and `vtx n`.
  set C := CN N
  set hC := CN_admissible N
  set L := 9 * Wh h C
  have hL : L > 27 / 2 - ε := by
    exact hN
  set edge := fun n => (∑ c ∈ C.filter (fun c => c.1 < c.2), mbin h n c.1 * mbin h n c.2) + (∑ c ∈ C.filter (fun c => c.1 = c.2), (mbin h n c.1).choose 2)
  set vtx := fun n => ∑ r ∈ Rset C, mbin h n r;
  -- By `edge_count_asymp`, `(edge n:ℝ)/S n → L`. By `vertex_count_asymp`, `(vtx n:ℝ)/S n → 0`. Hence `((edge n:ℝ) - vtx n)/S n = (edge n)/S n - (vtx n)/S n → L`.
  have h_edge_vtx : Filter.Tendsto (fun n => ((edge n : ℝ) - vtx n) / S n) Filter.atTop (nhds L) := by
    have h_edge : Filter.Tendsto (fun n => (edge n : ℝ) / S n) Filter.atTop (nhds L) := by
      have := edge_count_asymp hpnt h hh C;
      simp +zetaDelta at *;
      refine' this.congr' ( by filter_upwards [ Filter.eventually_ge_atTop 2 ] with n hn; rw [ Mval_sq_eq_S n ] );
    have h_vtx : Filter.Tendsto (fun n => (vtx n : ℝ) / S n) Filter.atTop (nhds 0) := by
      convert vertex_count_asymp hpnt h hh C using 1;
      norm_num +zetaDelta at *;
    simpa [ sub_div ] using h_edge.sub h_vtx;
  -- Since `L > 27/2 - ε`, eventually `((edge n:ℝ) - vtx n)/S n > 27/2 - ε`, i.e. (as `S n > 0` by `S_pos`) eventually `(27/2 - ε) * S n < (edge n:ℝ) - vtx n`.
  have h_eventually : ∀ᶠ n in Filter.atTop, (27 / 2 - ε) * S n < (edge n : ℝ) - vtx n := by
    filter_upwards [ h_edge_vtx.eventually ( lt_mem_nhds hL ), Filter.eventually_gt_atTop 1 ] with n hn hn';
    rwa [ lt_div_iff₀ ( by exact div_pos ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr hn'.le ) _ ) ( sq_pos_of_pos ( Real.log_pos ( Nat.one_lt_cast.mpr hn' ) ) ) ) ] at hn;
  filter_upwards [ h_eventually, Filter.eventually_ge_atTop 2, exists_hypergraph hpnt h hh C hC ] with n hn hn' hn'';
  obtain ⟨ H, hH₁, hH₂, hH₃, hH₄, hH₅, hH₆ ⟩ := hn''; have := linear_triple_replacement n H hH₁ hH₂ hH₃ hH₄; simp_all +decide [ card_primes_Icc ] ;
  linarith [ show ( F n : ℝ ) ≥ ( AH n H |> Finset.card ) by exact_mod_cast card_le_F n ( AH n H ) this.2.1 this.1, show ( Vset H |> Finset.card : ℝ ) ≤ vtx n by exact_mod_cast hH₅, show ( AH n H |> Finset.card : ℝ ) + ( Vset H |> Finset.card : ℝ ) = n.primeCounting + edge n by exact_mod_cast this.2.2 ]

/-
Assuming `PNT`, as `n → ∞`, `(F(n) - π(n)) / (n^{2/3}/(log n)²) → 27/2`.
-/
theorem second_order_asymptotic_of_PNT (hpnt : PNT) :
    Tendsto
      (fun n : ℕ =>
        ((F n : ℝ) - Nat.primeCounting n) /
          ((n : ℝ) ^ ((2:ℝ)/3) / (Real.log n) ^ 2))
      atTop (𝓝 (27/2)) := by
  refine' Metric.tendsto_atTop.mpr _;
  intro ε hε;
  -- Use the upper and lower bounds to find such an N.
  obtain ⟨N1, hN1⟩ : ∃ N1, ∀ n ≥ N1, (F n : ℝ) - Nat.primeCounting n ≤ (27 / 2 + ε / 2) * S n := by
    have := F_upper hpnt ( ε / 2 ) ( half_pos hε ) ; aesop;
  obtain ⟨N2, hN2⟩ : ∃ N2, ∀ n ≥ N2, (27 / 2 - ε / 2) * S n ≤ (F n : ℝ) - Nat.primeCounting n := by
    exact Filter.eventually_atTop.mp ( F_lower hpnt ( ε / 2 ) ( half_pos hε ) ) |> fun ⟨ N2, hN2 ⟩ => ⟨ N2, fun n hn => hN2 n hn ⟩
  use max N1 (max N2 2);
  intro n hn; rw [ dist_eq_norm ] ; rw [ Real.norm_eq_abs ] ; rw [ abs_lt ] ; constructor <;> norm_num at *;
  · rw [ add_div', lt_div_iff₀ ] <;> norm_num at *;
    · have := hN2 n hn.2.1; norm_num [ S ] at *; nlinarith [ show 0 < ( n : ℝ ) ^ ( 2 / 3 : ℝ ) / Real.log n ^ 2 by exact div_pos ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _ ) ( sq_pos_of_pos ( Real.log_pos ( Nat.one_lt_cast.mpr ( by linarith ) ) ) ) ] ;
    · exact div_pos ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _ ) ( sq_pos_of_pos ( Real.log_pos ( Nat.one_lt_cast.mpr ( by linarith ) ) ) );
    · grind +revert;
  · rw [ sub_lt_iff_lt_add' ];
    rw [ div_lt_iff₀ ] <;> nlinarith [ hN1 n hn.1, hN2 n hn.2.1, show 0 < ( n : ℝ ) ^ ( 2 / 3 : ℝ ) / Real.log n ^ 2 from div_pos ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _ ) ( sq_pos_of_pos ( Real.log_pos ( Nat.one_lt_cast.mpr ( by linarith ) ) ) ), show S n = ( n : ℝ ) ^ ( 2 / 3 : ℝ ) / Real.log n ^ 2 from rfl ]

end Erdos793
