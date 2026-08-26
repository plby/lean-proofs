/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
MIT License

Copyright (c) 2026 Axiom Math.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

Modified for this repository and Lean/Mathlib 4.33.0.
-/
/-
Erdős Problem 1134.
Informal proof: D. J. Crampin and A. J. W. Hilton.
Formal proof: AxiomProver, published by Axiom Math.
Source: https://www.erdosproblems.com/1134#post-7068
https://github.com/AxiomMath/erdos-public/blob/3ccf48c78b9df4aa26e1b2f90058bdd3f61da1ab/Erdos/Erdos1134/solution.lean
Original Lean version: 4.27.0.
Original Mathlib commit: a3a10db0e9d66acbebf76c5e6a135066525ac900.
-/
import ErdosProblems.Erdos1134.Canonical

namespace Erdos1134

-- The single-op Dirichlet weight q(s)
noncomputable def single_op_weight (s : ℝ) : ℝ :=
  ∑' (op : NTOp), ((op.mult : ℝ) ^ (-s))

-- Equiv between NTOp and Unit ⊕ ℕ for tsum decomposition
def ntopEquiv : NTOp ≃ Unit ⊕ ℕ where
  toFun | NTOp.f6 => Sum.inl () | NTOp.gk k => Sum.inr k
  invFun | Sum.inl () => NTOp.f6 | Sum.inr k => NTOp.gk k
  left_inv := by intro x; cases x <;> simp
  right_inv := by intro x; rcases x with ⟨⟩ | k <;> simp

-- Helper: decompose (3·2^k)^{-s} = 3^{-s} · (2^{-s})^k
lemma ntop_gk_rpow (s : ℝ) (k : ℕ) :
    ((NTOp.gk k).mult : ℝ) ^ (-s) = (3:ℝ)^(-s) * ((2:ℝ)^(-s))^k := by
  simp only [NTOp.mult]
  have : ((3 * 2 ^ k : ℕ) : ℝ) = (3 : ℝ) * (2 : ℝ) ^ k := by push_cast; ring
  rw [this, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) (by positivity : (0:ℝ) ≤ (2:ℝ)^k)]
  congr 1
  rw [← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [show ↑k * -s = (-s) * ↑k from by ring]
  rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]

-- Helper: version with cast from ℕ for the NTOp.mult unfolded form
lemma gk_cast_rpow (k : ℕ) :
    ((3 * 2 ^ k : ℕ) : ℝ) ^ (-(19/20 : ℝ)) = (3:ℝ)^(-(19/20:ℝ)) * ((2:ℝ)^(-(19/20:ℝ)))^k := by
  have : ((3 * 2 ^ k : ℕ) : ℝ) = (3 : ℝ) * (2 : ℝ) ^ k := by push_cast; ring
  rw [this, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) (by positivity : (0:ℝ) ≤ (2:ℝ)^k)]
  congr 1
  rw [← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [show ↑k * -(19/20 : ℝ) = (-(19/20:ℝ)) * ↑k from by ring]
  rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]

-- Helper: 2^{-19/20} < 1
lemma two_rpow_neg_lt_one : (2:ℝ) ^ (-(19/20 : ℝ)) < 1 := by
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  exact inv_lt_one_of_one_lt₀ (by
    rw [Real.one_lt_rpow_iff_of_pos (by norm_num : (0:ℝ) < 2)]
    left; exact ⟨by norm_num, by norm_num⟩)

-- Helper: 2^{-19/20} ≥ 0
lemma two_rpow_neg_nonneg : 0 ≤ (2:ℝ) ^ (-(19/20 : ℝ)) :=
  Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _

-- Helper: gk series is summable (geometric series with ratio 2^{-19/20})
lemma gk_summable :
    Summable (fun k : ℕ => ((NTOp.gk k).mult : ℝ) ^ (-(19/20 : ℝ))) := by
  simp_rw [ntop_gk_rpow]
  exact (summable_geometric_of_lt_one two_rpow_neg_nonneg two_rpow_neg_lt_one).mul_left _

lemma single_op_summable :
    Summable (fun op : NTOp => ((op.mult : ℝ) ^ (-(19/20 : ℝ)))) := by
  rw [← Equiv.summable_iff ntopEquiv.symm]
  apply Summable.sum
  · exact summable_of_hasFiniteSupport (Set.Finite.subset (Set.finite_univ) (Set.subset_univ _))
  · change Summable (fun k => ((NTOp.gk k).mult : ℝ) ^ (-(19/20 : ℝ)))
    exact gk_summable

lemma rpow_bound_2 : (2 : ℝ) ^ (-(19/20 : ℝ)) ≤ 10/19 := by
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  rw [inv_le_comm₀ (by positivity : 0 < (2:ℝ) ^ ((19:ℝ)/20)) (by positivity : (0:ℝ) < 10/19)]
  simp only [inv_div]
  rw [show (19:ℝ)/20 = 19 * (20:ℝ)⁻¹ from by ring]
  rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [show (19:ℝ) = ((19:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
  rw [show (20:ℝ)⁻¹ = 1/(20:ℝ) from by ring]
  push_cast
  conv_lhs => rw [show (19:ℝ)/10 = ((19/10 : ℝ)^20)^((1:ℝ)/20) from by
    rw [← Real.rpow_natCast (19/10 : ℝ) 20, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 19/10)]
    norm_num]
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num : (0:ℝ) ≤ 1/20)
  norm_num

lemma rpow_bound_3 : (3 : ℝ) ^ (-(19/20 : ℝ)) ≤ 5/14 := by
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3)]
  rw [inv_le_comm₀ (by positivity : 0 < (3:ℝ) ^ ((19:ℝ)/20)) (by positivity : (0:ℝ) < 5/14)]
  simp only [inv_div]
  rw [show (19:ℝ)/20 = 19 * (20:ℝ)⁻¹ from by ring]
  rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
  rw [show (19:ℝ) = ((19:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
  rw [show (20:ℝ)⁻¹ = 1/(20:ℝ) from by ring]
  conv_lhs => rw [show (14:ℝ)/5 = ((14/5 : ℝ)^20)^((1:ℝ)/20) from by
    rw [← Real.rpow_natCast (14/5 : ℝ) 20, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 14/5)]
    norm_num]
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num : (0:ℝ) ≤ 1/20)
  norm_num

lemma rpow_bound_6 : (6 : ℝ) ^ (-(19/20 : ℝ)) ≤ 5/27 := by
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 6)]
  rw [inv_le_comm₀ (by positivity : 0 < (6:ℝ) ^ ((19:ℝ)/20)) (by positivity : (0:ℝ) < 5/27)]
  simp only [inv_div]
  rw [show (19:ℝ)/20 = 19 * (20:ℝ)⁻¹ from by ring]
  rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 6)]
  rw [show (19:ℝ) = ((19:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
  rw [show (20:ℝ)⁻¹ = 1/(20:ℝ) from by ring]
  conv_lhs => rw [show (27:ℝ)/5 = ((27/5 : ℝ)^20)^((1:ℝ)/20) from by
    rw [← Real.rpow_natCast (27/5 : ℝ) 20, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 27/5)]
    norm_num]
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num : (0:ℝ) ≤ 1/20)
  norm_num

lemma rpow_bound_12 : 5/53 ≤ (12 : ℝ) ^ (-(19/20 : ℝ)) := by
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 12)]
  rw [le_inv_comm₀ (by positivity : (0:ℝ) < 5/53) (by positivity : 0 < (12:ℝ) ^ ((19:ℝ)/20))]
  simp only [inv_div]
  rw [show (19:ℝ)/20 = 19 * (20:ℝ)⁻¹ from by ring]
  rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 12)]
  rw [show (19:ℝ) = ((19:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
  rw [show (20:ℝ)⁻¹ = 1/(20:ℝ) from by ring]
  conv_rhs => rw [show (53:ℝ)/5 = ((53/5 : ℝ)^20)^((1:ℝ)/20) from by
    rw [← Real.rpow_natCast (53/5 : ℝ) 20, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 53/5)]
    norm_num]
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num : (0:ℝ) ≤ 1/20)
  norm_num

lemma single_op_weight_eq :
    single_op_weight (19/20 : ℝ) =
    (6 : ℝ) ^ (-(19/20 : ℝ)) + (3 : ℝ) ^ (-(19/20 : ℝ)) / (1 - (2 : ℝ) ^ (-(19/20 : ℝ))) := by
  unfold single_op_weight
  rw [single_op_summable.tsum_eq_add_tsum_ite NTOp.f6]
  simp only [NTOp.mult]
  congr 1
  rw [← Function.Injective.tsum_eq
      (g := NTOp.gk) (by intro a b h; cases h; rfl)
      (by intro op hop
          simp only [Function.mem_support] at hop
          cases op with
          | f6 => simp at hop
          | gk k => exact ⟨k, rfl⟩)]
  simp only [reduceCtorEq, ↓reduceIte]
  simp_rw [gk_cast_rpow]
  rw [tsum_mul_left, tsum_geometric_of_lt_one two_rpow_neg_nonneg two_rpow_neg_lt_one]
  ring

lemma one_sub_two_rpow_pos : 0 < 1 - (2 : ℝ) ^ (-(19/20 : ℝ)) := by
  have h := rpow_bound_2; linarith

lemma q_lt_one : single_op_weight (19/20 : ℝ) < 1 := by
  rw [single_op_weight_eq]
  have h2 := rpow_bound_2
  have h3 := rpow_bound_3
  have h6 := rpow_bound_6
  have hpos := one_sub_two_rpow_pos
  have hden : (9:ℝ)/19 ≤ 1 - (2:ℝ) ^ (-(19/20 : ℝ)) := by linarith
  have hden_pos : (0:ℝ) < 9/19 := by norm_num
  calc (6:ℝ) ^ (-(19/20 : ℝ)) + (3:ℝ) ^ (-(19/20 : ℝ)) / (1 - (2:ℝ) ^ (-(19/20 : ℝ)))
      ≤ 5/27 + (5/14) / (1 - (2:ℝ) ^ (-(19/20 : ℝ))) := by
        gcongr
    _ ≤ 5/27 + (5/14) / (9/19) := by
        gcongr
    _ = 355/378 := by norm_num
    _ < 1 := by norm_num

lemma q_nonneg : 0 ≤ single_op_weight (19/20 : ℝ) := by
  unfold single_op_weight
  apply tsum_nonneg
  intro op
  exact Real.rpow_nonneg (Nat.cast_nonneg _) _

-- Equivalence: {l : List NTOp // l.length = n+1} ≃ NTOp × {l : List NTOp // l.length = n}
def listLenSuccEquiv (n : ℕ) :
    {l : List NTOp // l.length = n + 1} ≃ NTOp × {l : List NTOp // l.length = n} where
  toFun := fun ⟨l, hl⟩ =>
    match l, hl with
    | op :: rest, h => ⟨op, ⟨rest, Nat.add_right_cancel (by simpa only [List.length_cons] using h)⟩⟩
  invFun := fun ⟨op, ⟨rest, hr⟩⟩ => ⟨op :: rest, by simp [hr]⟩
  left_inv := by
    intro ⟨l, hl⟩
    match l, hl with
    | op :: rest, h => simp
  right_inv := by
    intro ⟨op, ⟨rest, hr⟩⟩
    simp

-- {l : List NTOp // l.length = 0} is unique (only element is ⟨[], rfl⟩)
instance : Unique {l : List NTOp // l.length = 0} where
  default := ⟨[], rfl⟩
  uniq := by
    intro ⟨l, hl⟩
    simp only [Subtype.mk.injEq]
    exact List.eq_nil_of_length_eq_zero hl

lemma listLenSuccEquiv_symm_apply (n : ℕ) (op : NTOp) (rest : {l : List NTOp // l.length = n}) :
    ((listLenSuccEquiv n).symm (op, rest)).val = op :: rest.val := by
  simp [listLenSuccEquiv]

-- Summability of the ops series restricted to lists of length n
lemma ops_length_n_summable (n : ℕ) :
    Summable (fun ops : {l : List NTOp // l.length = n} =>
      ((ntOpsMult ops.val : ℝ) ^ (-(19/20 : ℝ)))) := by
  induction n with
  | zero =>
    exact summable_of_hasFiniteSupport
      (Set.Finite.subset (Set.finite_univ) (Set.subset_univ _))
  | succ n ih =>
    have heq : (fun ops : {l : List NTOp // l.length = n + 1} =>
        ((ntOpsMult ops.val : ℝ) ^ (-(19/20 : ℝ)))) =
      (fun p : NTOp × {l : List NTOp // l.length = n} =>
        ((ntOpsMult ((listLenSuccEquiv n).symm p).val : ℝ) ^ (-(19/20 : ℝ)))) ∘
      (listLenSuccEquiv n) := by
      ext ⟨l, hl⟩
      simp [Function.comp]
    rw [heq, Equiv.summable_iff]
    suffices h : Summable (fun p : NTOp × {l : List NTOp // l.length = n} =>
        ((p.1.mult : ℝ) ^ (-(19/20 : ℝ))) * ((ntOpsMult p.2.val : ℝ) ^ (-(19/20 : ℝ)))) by
      apply h.of_nonneg_of_le
        (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      intro ⟨op, rest⟩
      rw [listLenSuccEquiv_symm_apply, ntOpsMult,
        show ((op.mult * ntOpsMult rest.val : ℕ) : ℝ) = (op.mult : ℝ) * (ntOpsMult rest.val : ℝ)
          from by push_cast; ring,
        Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    exact Summable.mul_of_nonneg single_op_summable ih
      (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

-- Helper: sum over lists of length n equals q^n
set_option maxHeartbeats 3200000 in
-- The nested infinite-series decompositions need extra elaboration time.
lemma ops_length_n_sum (n : ℕ) :
    ∑' (ops : {l : List NTOp // l.length = n}),
      ((ntOpsMult ops.val : ℝ) ^ (-(19/20 : ℝ))) =
    single_op_weight (19/20 : ℝ) ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero]
    have huniq : ∀ (x : {l : List NTOp // l.length = 0}), x = ⟨[], rfl⟩ :=
      fun x => Subtype.ext (List.eq_nil_of_length_eq_zero x.property)
    rw [tsum_eq_single ⟨[], rfl⟩ (fun b hb => absurd (huniq b) hb)]
    simp [ntOpsMult]
  | succ n ih =>
    rw [pow_succ, mul_comm, ← ih]
    have step1 : ∑' (ops : {l : List NTOp // l.length = n + 1}),
          ((ntOpsMult ops.val : ℝ) ^ (-(19/20 : ℝ))) =
        ∑' (p : NTOp × {l : List NTOp // l.length = n}),
          ((p.1.mult : ℝ) ^ (-(19/20 : ℝ))) * ((ntOpsMult p.2.val : ℝ) ^ (-(19/20 : ℝ))) := by
      have := (listLenSuccEquiv n).symm.tsum_eq
        (fun ops : {l : List NTOp // l.length = n + 1} =>
          ((ntOpsMult ops.val : ℝ) ^ (-(19/20 : ℝ))))
      rw [← this]
      congr 1
      ext ⟨op, rest⟩
      rw [listLenSuccEquiv_symm_apply, ntOpsMult,
        show ((op.mult * ntOpsMult rest.val : ℕ) : ℝ) = (op.mult : ℝ) * (ntOpsMult rest.val : ℝ)
          from by push_cast; ring,
        Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    rw [step1]
    symm
    unfold single_op_weight
    have hf_norm : Summable (fun x : NTOp => ‖((x.mult : ℝ) ^ (-(19/20 : ℝ)))‖) := by
      have : ∀ (x : NTOp), ‖((x.mult : ℝ) ^ (-(19/20 : ℝ)))‖ =
          ((x.mult : ℝ) ^ (-(19/20 : ℝ))) :=
        fun x => Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      simp_rw [this]
      exact single_op_summable
    have hg_norm : Summable (fun x : {l : List NTOp // l.length = n} =>
        ‖((ntOpsMult x.val : ℝ) ^ (-(19/20 : ℝ)))‖) := by
      have : ∀ (x : {l : List NTOp // l.length = n}),
          ‖((ntOpsMult x.val : ℝ) ^ (-(19/20 : ℝ)))‖ =
          ((ntOpsMult x.val : ℝ) ^ (-(19/20 : ℝ))) :=
        fun x => Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      simp_rw [this]
      exact ops_length_n_summable n
    rw [tsum_mul_tsum_of_summable_norm hf_norm hg_norm]

-- Equivalence: List NTOp ≃ Σ (n : ℕ), {l : List NTOp // l.length = n}
def listLengthEquiv : (Σ (n : ℕ), {l : List NTOp // l.length = n}) ≃ List NTOp :=
  Equiv.sigmaFiberEquiv List.length

set_option maxHeartbeats 1600000 in
-- The nested infinite-series decompositions need extra elaboration time.
lemma ops_series_summable :
    Summable (fun ops : List NTOp => ((ntOpsMult ops : ℝ) ^ (-(19/20 : ℝ)))) := by
  rw [← Equiv.summable_iff listLengthEquiv]
  show Summable ((fun ops : List NTOp => ((ntOpsMult ops : ℝ) ^ (-(19/20 : ℝ)))) ∘ listLengthEquiv)
  have : ((fun ops : List NTOp => ((ntOpsMult ops : ℝ) ^ (-(19/20 : ℝ)))) ∘ listLengthEquiv) =
      (fun σ : Σ (n : ℕ), {l : List NTOp // l.length = n} =>
        ((ntOpsMult σ.2.val : ℝ) ^ (-(19/20 : ℝ)))) := by
    ext ⟨n, l, hl⟩
    simp [listLengthEquiv, Equiv.sigmaFiberEquiv]
  rw [this]
  rw [summable_sigma_of_nonneg (fun x => Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  exact ⟨fun n => ops_length_n_summable n,
    by simp_rw [ops_length_n_sum]; exact summable_geometric_of_lt_one q_nonneg q_lt_one⟩

lemma terminal_series_summable :
    Summable (fun t : ℕ => ((2 : ℝ) ^ (t : ℝ)) ^ (-(19/20 : ℝ))) := by
  -- Rewrite (2^(t:ℝ))^(-19/20) = (2^(-19/20))^t
  have h : ∀ t : ℕ, ((2 : ℝ) ^ (t : ℝ)) ^ (-(19/20 : ℝ)) = ((2:ℝ) ^ (-(19/20 : ℝ))) ^ t := by
    intro t
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    rw [show (↑t * -(19/20 : ℝ)) = (-(19/20 : ℝ)) * ↑t from by ring]
    rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    rw [Real.rpow_natCast]
  simp_rw [h]
  exact summable_geometric_of_lt_one two_rpow_neg_nonneg two_rpow_neg_lt_one

-- Equivalence: CanonWord ≃ List NTOp × ℕ
def canonWordEquiv : CanonWord ≃ List NTOp × ℕ where
  toFun w := (w.ops, w.terminal)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

set_option maxHeartbeats 3200000 in
-- The nested infinite-series decompositions need extra elaboration time.
lemma canonword_dirichlet_summable :
    Summable (fun w : CanonWord => ((w.mult : ℝ) ^ (-(19/20 : ℝ)))) := by
  have h1 : (fun w : CanonWord => ((w.mult : ℝ) ^ (-(19/20 : ℝ)))) =
      (fun p : List NTOp × ℕ =>
        ((ntOpsMult p.1 : ℝ) ^ (-(19/20 : ℝ))) * (((2 : ℝ) ^ (p.2 : ℝ)) ^ (-(19/20 : ℝ)))) ∘
      canonWordEquiv := by
    ext w
    simp only [Function.comp, canonWordEquiv, CanonWord.mult]
    rw [show ((ntOpsMult w.ops * 2 ^ w.terminal : ℕ) : ℝ) =
        (ntOpsMult w.ops : ℝ) * ((2 : ℝ) ^ (w.terminal : ℝ)) from by
      push_cast; rw [Real.rpow_natCast]]
    exact Real.mul_rpow (Nat.cast_nonneg _) (by positivity)
  rw [h1, Equiv.summable_iff]
  exact Summable.mul_of_nonneg ops_series_summable terminal_series_summable
    (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun _ => Real.rpow_nonneg (by positivity) _)

lemma canonical_dirichlet_bound :
    ∃ D : ℝ, 0 < D ∧
    ∀ (W : Finset CanonWord),
      W.sum (fun w => ((w.mult : ℝ) ^ (-(19/20 : ℝ)))) ≤ D := by
  -- Use the tsum as D (it is finite by canonword_dirichlet_summable)
  have hsumm := canonword_dirichlet_summable
  refine ⟨∑' (w : CanonWord), ((w.mult : ℝ) ^ (-(19/20 : ℝ))), ?_, fun W => ?_⟩
  · have hterm : (0 : ℝ) < ((⟨[], 0⟩ : CanonWord).mult : ℝ) ^ (-(19/20 : ℝ)) := by
      have : (⟨[], 0⟩ : CanonWord).mult = 1 := by simp [CanonWord.mult, ntOpsMult]
      rw [this]; simp
    exact lt_of_lt_of_le hterm (Summable.le_tsum hsumm ⟨[], 0⟩
      (fun j _ => Real.rpow_nonneg (Nat.cast_nonneg _) _))
  · exact Summable.sum_le_tsum W (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) hsumm

lemma erdos_set_sublinear_bound :
    ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ,
      (Set.ncard (Set.ofPred ErdosSetA ∩ Set.Iic N) : ℝ) ≤ C * (N : ℝ) ^ (19/20 : ℝ) := by
  obtain ⟨D, hDpos, hDbound⟩ := canonical_dirichlet_bound
  refine ⟨D, hDpos, fun N => ?_⟩
  obtain ⟨W, hcard, hW⟩ := erdos_injection_canonical N
  have hrankin := rankin_trick W CanonWord.mult N (19/20 : ℝ) (by norm_num)
    (fun w hw => hW w hw)
  have hsum := hDbound W
  have h1 : (Set.ncard (Set.ofPred ErdosSetA ∩ Set.Iic N) : ℝ) ≤ (W.card : ℝ) :=
    Nat.cast_le.mpr hcard
  have h2 : (N : ℝ) ^ (19/20 : ℝ) * W.sum (fun w => ((w.mult : ℝ) ^ (-(19/20 : ℝ)))) ≤
      (N : ℝ) ^ (19/20 : ℝ) * D :=
    mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  calc (Set.ncard (Set.ofPred ErdosSetA ∩ Set.Iic N) : ℝ)
      ≤ W.card := h1
    _ ≤ (N : ℝ) ^ (19/20 : ℝ) * W.sum (fun w => ((w.mult : ℝ) ^ (-(19/20 : ℝ)))) := hrankin
    _ ≤ (N : ℝ) ^ (19/20 : ℝ) * D := h2
    _ = D * (N : ℝ) ^ (19/20 : ℝ) := mul_comm _ _

end Erdos1134
