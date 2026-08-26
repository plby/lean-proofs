import ErdosProblems.Erdos788.FiniteDistribution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite product distributions and prediction from total variation

These lemmas isolate the probability bookkeeping used by the reconstruction
argument.  In particular, the predictor theorem is stated with unnormalised
context masses, so no conditional-probability denominator or zero-mass case
is needed.
-/

namespace Erdos788

open scoped BigOperators

namespace FinDist

variable {α β γ : Type*}

/-- Product of two finite distributions. -/
noncomputable def prod [Fintype α] [Fintype β]
    (P : FinDist α) (Q : FinDist β) : FinDist (α × β) where
  mass := fun z ↦ P.mass z.1 * Q.mass z.2
  nonneg := fun z ↦ mul_nonneg (P.nonneg z.1) (Q.nonneg z.2)
  sum_mass := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ a, ∑ b, P.mass a * Q.mass b) =
          ∑ a, P.mass a * ∑ b, Q.mass b := by
        apply Finset.sum_congr rfl
        intro a _ha
        rw [Finset.mul_sum]
      _ = 1 := by rw [Q.sum_mass]; simp [P.sum_mass]

@[simp]
theorem prod_mass [Fintype α] [Fintype β]
    (P : FinDist α) (Q : FinDist β) (z : α × β) :
    (P.prod Q).mass z = P.mass z.1 * Q.mass z.2 :=
  rfl

/-- Total variation is unchanged after adjoining the same independent right
factor. -/
theorem tv_prod_right [Fintype α] [Fintype β]
    (P Q : FinDist α) (R : FinDist β) :
    (P.prod R).tv (Q.prod R) = P.tv Q := by
  rw [tv, tv, Fintype.sum_prod_type]
  simp only [prod_mass]
  have hpoint : ∀ a : α, ∀ b : β,
      |P.mass a * R.mass b - Q.mass a * R.mass b| =
        |P.mass a - Q.mass a| * R.mass b := by
    intro a b
    rw [← sub_mul, abs_mul, abs_of_nonneg (R.nonneg b)]
  simp_rw [hpoint]
  calc
    (1 / 2 : ℝ) * ∑ a, ∑ b, |P.mass a - Q.mass a| * R.mass b =
        (1 / 2 : ℝ) * ∑ a, |P.mass a - Q.mass a| * ∑ b, R.mass b := by
      congr 1
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.mul_sum]
    _ = (1 / 2 : ℝ) * ∑ a, |P.mass a - Q.mass a| := by
      rw [R.sum_mass]
      simp

/-- Total variation is unchanged after adjoining the same independent left
factor. -/
theorem tv_prod_left [Fintype α] [Fintype β]
    (R : FinDist α) (P Q : FinDist β) :
    (R.prod P).tv (R.prod Q) = P.tv Q := by
  rw [tv, tv, Fintype.sum_prod_type]
  simp only [prod_mass]
  have hpoint : ∀ a : α, ∀ b : β,
      |R.mass a * P.mass b - R.mass a * Q.mass b| =
        R.mass a * |P.mass b - Q.mass b| := by
    intro a b
    rw [← mul_sub, abs_mul, abs_of_nonneg (R.nonneg a)]
  simp_rw [hpoint]
  calc
    (1 / 2 : ℝ) * ∑ a, ∑ b, R.mass a * |P.mass b - Q.mass b| =
        (1 / 2 : ℝ) * ∑ a, R.mass a * ∑ b, |P.mass b - Q.mass b| := by
      congr 1
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.mul_sum]
    _ = (1 / 2 : ℝ) * ∑ b, |P.mass b - Q.mass b| := by
      rw [← Finset.sum_mul, R.sum_mass, one_mul]

/-- Pushing forward cannot increase finite total variation. -/
theorem tv_map_le [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (P Q : FinDist α) :
    (P.map f).tv (Q.map f) ≤ P.tv Q := by
  rw [tv, tv]
  have hfiber : ∀ b : β,
      |∑ a with f a = b, P.mass a - ∑ a with f a = b, Q.mass a| ≤
        ∑ a with f a = b, |P.mass a - Q.mass a| := by
    intro b
    rw [← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  have hsum := Finset.sum_le_sum fun b
      (_hb : b ∈ (Finset.univ : Finset β)) ↦ hfiber b
  have hpartition :
      (∑ b, ∑ a with f a = b, |P.mass a - Q.mass a|) =
        ∑ a, |P.mass a - Q.mass a| := by
    simp [Finset.sum_fiberwise_eq_sum_filter Finset.univ Finset.univ f
      (fun a ↦ |P.mass a - Q.mass a|)]
  rw [hpartition] at hsum
  exact mul_le_mul_of_nonneg_left hsum (by norm_num)

@[simp]
theorem map_equiv_mass [Fintype α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (P : FinDist α) (a : α) :
    (P.map e).mass (e a) = P.mass a := by
  rw [map_mass]
  have hfiber :
      (Finset.univ.filter fun x : α ↦ e x = e a) = {a} := by
    ext x
    simp
  rw [hfiber]
  simp

/-- A uniform finite distribution remains uniform under a reindexing
equivalence. -/
theorem map_uniform_equiv [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] [DecidableEq β]
    (e : α ≃ β) :
    (FinDist.uniform α).map e = FinDist.uniform β := by
  classical
  ext b
  let a : α := e.symm b
  have hab : e a = b := e.apply_symm_apply b
  rw [← hab, map_equiv_mass]
  simp only [uniform_mass]
  rw [Fintype.card_congr e]

/-- Total variation is invariant under a reindexing equivalence. -/
theorem tv_map_equiv [Fintype α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (P Q : FinDist α) :
    (P.map e).tv (Q.map e) = P.tv Q := by
  rw [tv, tv]
  congr 1
  calc
    (∑ b : β, |(P.map e).mass b - (Q.map e).mass b|) =
        ∑ a : α, |(P.map e).mass (e a) - (Q.map e).mass (e a)| :=
      (e.sum_comp fun b ↦ |(P.map e).mass b - (Q.map e).mass b|).symm
    _ = ∑ a : α, |P.mass a - Q.mass a| := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [map_equiv_mass e P a, map_equiv_mass e Q a]

/-- Functoriality of finite pushforward. -/
theorem map_map [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ]
    (P : FinDist α) (f : α → β) (g : β → γ) :
    (P.map f).map g = P.map (g ∘ f) := by
  ext c
  rw [map_mass, map_mass]
  simp only [map_mass]
  let T : Finset β := Finset.univ.filter fun b ↦ g b = c
  have h := Finset.sum_fiberwise_eq_sum_filter
    (Finset.univ : Finset α) T f P.mass
  simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.comp_apply] using! h

/-- A deterministic maximizer on a nonempty finite type. -/
noncomputable def finiteArgmax (α : Type*) [Fintype α] [Nonempty α]
    (f : α → ℝ) : α :=
  Classical.choose
    (Finset.exists_max_image (Finset.univ : Finset α) f Finset.univ_nonempty)

theorem le_finiteArgmax (α : Type*) [Fintype α] [Nonempty α]
    (f : α → ℝ) (a : α) : f a ≤ f (finiteArgmax α f) := by
  exact (Classical.choose_spec
    (Finset.exists_max_image (Finset.univ : Finset α) f
      Finset.univ_nonempty)).2 a (Finset.mem_univ a)

/-- Marginal distribution on the first coordinate. -/
noncomputable def fst [Fintype α] [Fintype β] [DecidableEq α]
    (P : FinDist (α × β)) : FinDist α :=
  P.map Prod.fst

@[simp]
theorem fst_mass [Fintype α] [Fintype β] [DecidableEq α]
    (P : FinDist (α × β)) (a : α) :
    P.fst.mass a = ∑ b, P.mass (a, b) := by
  rw [fst, map_mass]
  apply Finset.sum_bij (fun z _hz ↦ z.2)
  · intro z _hz
    exact Finset.mem_univ z.2
  · intro z₁ hz₁ z₂ hz₂ hsnd
    apply Prod.ext
    · exact ((Finset.mem_filter.mp hz₁).2).trans
        ((Finset.mem_filter.mp hz₂).2).symm
    · exact hsnd
  · intro b _hb
    exact ⟨(a, b), by simp, rfl⟩
  · intro z hz
    congr 1
    exact Prod.ext (Finset.mem_filter.mp hz).2 rfl

/-- The first marginal of an independent product is its first factor. -/
@[simp]
theorem fst_prod [Fintype α] [Fintype β] [DecidableEq α]
    (P : FinDist α) (Q : FinDist β) :
    (P.prod Q).fst = P := by
  ext a
  rw [fst_mass]
  simp only [prod_mass]
  rw [← Finset.mul_sum, Q.sum_mass, mul_one]

/-- The uniform law on a product is the product of the uniform laws. -/
theorem uniform_prod [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] :
    FinDist.uniform (α × β) =
      (FinDist.uniform α).prod (FinDist.uniform β) := by
  classical
  ext z
  simp only [uniform_mass, prod_mass, Fintype.card_prod]
  have ha : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card α))
  have hb : (Fintype.card β : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card β))
  push_cast
  field_simp

/-- Associativity of independent finite products, after the canonical
reindexing of the underlying product type. -/
theorem map_prodAssoc
    {δ : Type*} [Fintype α] [Fintype β] [Fintype δ]
    [DecidableEq α] [DecidableEq β] [DecidableEq δ]
    (P : FinDist α) (Q : FinDist β) (R : FinDist δ) :
    ((P.prod Q).prod R).map (Equiv.prodAssoc α β δ) =
      P.prod (Q.prod R) := by
  classical
  ext z
  let w : (α × β) × δ := ((z.1, z.2.1), z.2.2)
  have hw : Equiv.prodAssoc α β δ w = z := by
    exact Prod.ext rfl (Prod.ext rfl rfl)
  rw [← hw, map_equiv_mass]
  simp only [prod_mass]
  rw [hw]
  dsimp [w]
  ring

/-- The point selected by `finiteArgmax` has at least the average mass. -/
theorem average_le_argmax_mass [Fintype β] [Nonempty β]
    (μ : β → ℝ) :
    (∑ b, μ b) / Fintype.card β ≤ μ (finiteArgmax β μ) := by
  have hsum : ∑ b, μ b ≤
      ∑ _b : β, μ (finiteArgmax β μ) :=
    Finset.sum_le_sum fun b _hb ↦ le_finiteArgmax β μ b
  rw [Finset.sum_const] at hsum
  simp only [nsmul_eq_mul] at hsum
  have hcard : (0 : ℝ) < Fintype.card β := by
    exact_mod_cast Fintype.card_pos
  exact (div_le_iff₀ hcard).2 (by simpa [mul_comm] using! hsum)

/-- Pointwise `L¹` deviation from the uniform split of a total mass is at
most twice the alphabet size times the best prediction advantage. -/
theorem sum_abs_sub_average_le
    [Fintype β] [Nonempty β]
    (μ : β → ℝ) :
    ∑ b, |μ b - (∑ c, μ c) / Fintype.card β| ≤
      2 * Fintype.card β *
        (μ (finiteArgmax β μ) - (∑ c, μ c) / Fintype.card β) := by
  let t : ℝ := (∑ c, μ c) / Fintype.card β
  let M : ℝ := μ (finiteArgmax β μ) - t
  have hM : 0 ≤ M := by
    dsimp [M, t]
    exact sub_nonneg.mpr (average_le_argmax_mass μ)
  have hle : ∀ b : β, μ b - t ≤ M := by
    intro b
    dsimp [M]
    linarith [le_finiteArgmax β μ b]
  have hpoint : ∀ b : β, |μ b - t| ≤ 2 * M - (μ b - t) := by
    intro b
    by_cases hb : 0 ≤ μ b - t
    · rw [abs_of_nonneg hb]
      linarith [hle b]
    · rw [abs_of_neg (lt_of_not_ge hb)]
      linarith
  calc
    ∑ b, |μ b - (∑ c, μ c) / Fintype.card β| =
        ∑ b, |μ b - t| := by rfl
    _ ≤ ∑ b, (2 * M - (μ b - t)) := Finset.sum_le_sum fun b _ ↦ hpoint b
    _ = 2 * Fintype.card β * M := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      dsimp [t]
      have hcard : (Fintype.card β : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card β))
      field_simp
      ring
    _ = 2 * Fintype.card β *
        (μ (finiteArgmax β μ) -
          (∑ c, μ c) / Fintype.card β) := by rfl

/-- If a joint law is far from its context marginal times a uniform
alphabet symbol, a deterministic context predictor has a corresponding
unconditional success advantage.  The denominator `p` is slightly weaker
than the optimal `p-1`, but is fully sufficient for the extractor
parameters and avoids all conditional-probability cases. -/
theorem exists_predictor_of_tv_gt
    {p : ℕ} [NeZero p]
    {Context : Type*} [Fintype Context] [DecidableEq Context]
    (Q : FinDist (Context × ZMod p)) (δ : ℝ)
    (hδ : δ < Q.tv (Q.fst.prod (FinDist.uniform (ZMod p)))) :
    ∃ predictor : Context → ZMod p,
      1 / (p : ℝ) + δ / p <
        ∑ c, Q.mass (c, predictor c) := by
  classical
  let predictor : Context → ZMod p := fun c ↦
    finiteArgmax (ZMod p) (fun a ↦ Q.mass (c, a))
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hcontext (c : Context) :
      ∑ a, |Q.mass (c, a) - Q.fst.mass c * (p : ℝ)⁻¹| ≤
        2 * p * (Q.mass (c, predictor c) - Q.fst.mass c / p) := by
    have h := sum_abs_sub_average_le (fun a : ZMod p ↦ Q.mass (c, a))
    rw [hcard] at h
    rw [Q.fst_mass c]
    simpa [predictor, div_eq_mul_inv] using! h
  have htvUpper : Q.tv (Q.fst.prod (FinDist.uniform (ZMod p))) ≤
      (p : ℝ) *
        ((∑ c, Q.mass (c, predictor c)) - 1 / (p : ℝ)) := by
    rw [tv, Fintype.sum_prod_type]
    simp only [prod_mass, uniform_mass]
    rw [hcard]
    have hsum := Finset.sum_le_sum fun c
        (_hc : c ∈ (Finset.univ : Finset Context)) ↦ hcontext c
    calc
      (1 / 2 : ℝ) *
          ∑ c, ∑ a, |Q.mass (c, a) - Q.fst.mass c * (p : ℝ)⁻¹| ≤
          (1 / 2 : ℝ) *
            ∑ c, 2 * p *
              (Q.mass (c, predictor c) - Q.fst.mass c / p) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = (p : ℝ) *
          ((∑ c, Q.mass (c, predictor c)) - 1 / (p : ℝ)) := by
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_div,
          Q.fst.sum_mass]
        field_simp [NeZero.ne p]
  refine ⟨predictor, ?_⟩
  have hpNat : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hp : (0 : ℝ) < p := by exact_mod_cast hpNat
  have hmain : δ < (p : ℝ) *
      ((∑ c, Q.mass (c, predictor c)) - 1 / (p : ℝ)) :=
    hδ.trans_le htvUpper
  have hdiv : δ / (p : ℝ) <
      (∑ c, Q.mass (c, predictor c)) - 1 / (p : ℝ) := by
    apply (div_lt_iff₀ hp).2
    simpa [mul_comm] using! hmain
  linarith

/-- Repeated triangle inequality along a finite chain. -/
theorem tv_le_sum_range_chain [Fintype α]
    (H : ℕ → FinDist α) (r : ℕ) :
    (H 0).tv (H r) ≤
      ∑ i ∈ Finset.range r, (H i).tv (H (i + 1)) := by
  induction r with
  | zero => simp
  | succ r ih =>
      calc
        (H 0).tv (H (r + 1)) ≤
            (H 0).tv (H r) + (H r).tv (H (r + 1)) :=
          tv_triangle (H 0) (H r) (H (r + 1))
        _ ≤ (∑ i ∈ Finset.range r, (H i).tv (H (i + 1))) +
            (H r).tv (H (r + 1)) := add_le_add ih le_rfl
        _ = ∑ i ∈ Finset.range (r + 1),
            (H i).tv (H (i + 1)) := by
          rw [Finset.sum_range_succ]

/-- If the endpoints of a chain are more than `ε` apart, one of its `r`
steps is more than `ε/r` apart. -/
theorem exists_step_tv_gt [Fintype α]
    (H : ℕ → FinDist α) {r : ℕ} (hr : 0 < r) (ε : ℝ)
    (hend : ε < (H 0).tv (H r)) :
    ∃ i < r, ε / r < (H i).tv (H (i + 1)) := by
  by_contra hnone
  push Not at hnone
  have hsum :
      (∑ i ∈ Finset.range r, (H i).tv (H (i + 1))) ≤ ε := by
    calc
      (∑ i ∈ Finset.range r, (H i).tv (H (i + 1))) ≤
          ∑ _i ∈ Finset.range r, ε / r :=
        Finset.sum_le_sum fun i hi ↦ hnone i (Finset.mem_range.mp hi)
      _ = ε := by
        rw [Finset.sum_const, Finset.card_range]
        simp only [nsmul_eq_mul]
        have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
        field_simp
  exact (not_lt_of_ge ((tv_le_sum_range_chain H r).trans hsum)) hend

end FinDist

end Erdos788
