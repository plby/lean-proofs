/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1089.
https://www.erdosproblems.com/forum/thread/1089

Informal authors:
- Eiichi Bannai
- Etsuko Bannai
- Dennis Stanton
- Aletheia

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1089.md
-/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 1089

For a finite set of points in `d`-dimensional Euclidean space, we count the
distinct nonzero distances that it determines.  We define the genuine minimal
forcing number `g d n`, prove the Bannai--Bannai--Stanton upper bound and the
constant-weight lower construction, and deduce the fixed-`n` limit.

The detailed mathematical proof and Leanization plan are in `tex/1089.tex`.
-/

open Asymptotics Filter Metric Set
open scoped BigOperators Topology RealInnerProductSpace

namespace Erdos1089

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The finset of nonzero distances determined by a finite point set. -/
noncomputable def distanceFinset {d : ℕ} (P : Finset (Point d)) : Finset ℝ :=
  open scoped Classical in
  P.offDiag.image fun xy => dist xy.1 xy.2

/-- The number of distinct nonzero distances determined by `P`. -/
noncomputable def distanceCount {d : ℕ} (P : Finset (Point d)) : ℕ :=
  (distanceFinset P).card

/-- Every `m`-point subset of `ℝ^d` determines at least `n` distances. -/
def ForcesDistances (d n m : ℕ) : Prop :=
  ∀ P : Finset (Point d), P.card = m → n ≤ distanceCount P

@[simp] lemma mem_distanceFinset_iff {d : ℕ} {P : Finset (Point d)} {r : ℝ} :
    r ∈ distanceFinset P ↔
      ∃ x ∈ P, ∃ y ∈ P, x ≠ y ∧ dist x y = r := by
  classical
  constructor
  · intro hr
    rw [distanceFinset, Finset.mem_image] at hr
    obtain ⟨⟨x, y⟩, hxy, hdist⟩ := hr
    rw [Finset.mem_offDiag] at hxy
    exact ⟨x, hxy.1, y, hxy.2.1, hxy.2.2, hdist⟩
  · rintro ⟨x, hx, y, hy, hxy, hdist⟩
    rw [distanceFinset, Finset.mem_image]
    exact ⟨(x, y), Finset.mem_offDiag.mpr ⟨hx, hy, hxy⟩, hdist⟩

lemma distanceFinset_pos {d : ℕ} {P : Finset (Point d)} {r : ℝ}
    (hr : r ∈ distanceFinset P) : 0 < r := by
  obtain ⟨x, hx, y, hy, hxy, rfl⟩ := mem_distanceFinset_iff.mp hr
  exact dist_pos.mpr hxy

/-! ## Weak compositions and stars and bars -/

/-- Exponent vectors of total degree at most `s`. -/
def WeakComposition (d s : ℕ) :=
  {e : Fin d → ℕ // ∑ i, e i ≤ s}

/-- Add the slack coordinate.  This is the stars-and-bars equivalence between
weak compositions of total mass at most `s` in `d` coordinates and multisets
of size `s` on `d+1` labels. -/
noncomputable def weakCompositionEquiv (d s : ℕ) :
    WeakComposition d s ≃ Sym (Fin (d + 1)) s := by
  let E : WeakComposition d s ≃
      {u : Fin (d + 1) → ℕ // ∑ i, u i = s} :=
    { toFun := fun e =>
        ⟨Fin.snoc e.1 (s - ∑ i, e.1 i), by
          rw [Fin.sum_univ_castSucc]
          simp only [Fin.snoc_castSucc, Fin.snoc_last]
          exact Nat.add_sub_of_le e.2⟩
      invFun := fun u =>
        ⟨fun i => u.1 i.castSucc, by
          have hu := u.2
          rw [Fin.sum_univ_castSucc] at hu
          change (∑ i : Fin d, u.1 (Fin.castSucc i)) ≤ s
          calc
            (∑ i : Fin d, u.1 (Fin.castSucc i)) ≤
                (∑ i : Fin d, u.1 (Fin.castSucc i)) + u.1 (Fin.last d) :=
              Nat.le_add_right _ _
            _ = s := hu⟩
      left_inv := by
        intro e
        apply Subtype.ext
        funext i
        simp
      right_inv := by
        intro u
        apply Subtype.ext
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · have hu := u.2
          rw [Fin.sum_univ_castSucc] at hu
          simp only [Fin.snoc_last]
          omega
        · simp }
  exact E.trans (Sym.equivNatSumOfFintype (Fin (d + 1)) s).symm

noncomputable instance weakCompositionFintype (d s : ℕ) :
    Fintype (WeakComposition d s) :=
  Fintype.ofEquiv (Sym (Fin (d + 1)) s) (weakCompositionEquiv d s).symm

lemma card_weakComposition (d s : ℕ) :
    Fintype.card (WeakComposition d s) = (d + s).choose s := by
  rw [Fintype.card_congr (weakCompositionEquiv d s), Sym.card_sym_eq_choose]
  simp only [Fintype.card_fin]
  congr 2
  omega

/-- Evaluation of the monomial indexed by a weak composition. -/
def monomialValue {d s : ℕ} (e : WeakComposition d s) (x : Point d) : ℝ :=
  ∏ i, x i ^ e.1 i

/-! ## The polynomial moment argument -/

/-- Join two Euclidean points to obtain a valuation of two copies of the
coordinate variables. -/
def pairCoordinates {d : ℕ} (x y : Point d) : Sum (Fin d) (Fin d) → ℝ :=
  Sum.elim x y

@[simp] lemma pairCoordinates_inl {d : ℕ} (x y : Point d) (i : Fin d) :
    pairCoordinates x y (Sum.inl i) = x i := rfl

@[simp] lemma pairCoordinates_inr {d : ℕ} (x y : Point d) (i : Fin d) :
    pairCoordinates x y (Sum.inr i) = y i := rfl

lemma pairCoordinates_monomial {d : ℕ} (m : Sum (Fin d) (Fin d) →₀ ℕ)
    (x y : Point d) :
    (∏ i, pairCoordinates x y i ^ m i) =
      (∏ i : Fin d, x i ^ m (Sum.inl i)) *
        ∏ i : Fin d, y i ^ m (Sum.inr i) := by
  rw [Fintype.prod_sum_type]
  rfl

/-- The moment map taking a function on a finite point configuration to all
of its monomial moments of degree at most `s`. -/
def momentMap {A : Type*} [Fintype A] {d : ℕ} (x : A → Point d) (s : ℕ) :
    (A → ℝ) →ₗ[ℝ] (WeakComposition d s → ℝ) where
  toFun f e := ∑ a, f a * monomialValue e (x a)
  map_add' f g := by
    ext e
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c f := by
    ext e
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

lemma leftDegree_add_rightDegree {d : ℕ}
    (m : Sum (Fin d) (Fin d) →₀ ℕ) :
    (∑ i : Fin d, m (Sum.inl i)) + (∑ i : Fin d, m (Sum.inr i)) =
      m.degree := by
  rw [Finsupp.degree_eq_sum, Fintype.sum_sum_type]

private lemma polynomial_double_sum_eq_zero
    {A : Type*} [Fintype A] {d s : ℕ} (x : A → Point d)
    (p : MvPolynomial (Sum (Fin d) (Fin d)) ℝ)
    (hp : p.totalDegree ≤ 2 * s) (f : A → ℝ)
    (hf : momentMap x s f = 0) :
    ∑ a, ∑ b, f a * f b * p.eval (pairCoordinates (x a) (x b)) = 0 := by
  classical
  have hmoment (e : WeakComposition d s) :
      ∑ a, f a * monomialValue e (x a) = 0 := by
    exact congrFun hf e
  have hterm (m : Sum (Fin d) (Fin d) →₀ ℕ) (hm : m ∈ p.support) :
      (∑ a, f a * ∏ i : Fin d, (x a i) ^ m (Sum.inl i)) *
        (∑ b, f b * ∏ i : Fin d, (x b i) ^ m (Sum.inr i)) = 0 := by
    have hmdeg :
        (∑ i : Fin d, m (Sum.inl i)) + (∑ i : Fin d, m (Sum.inr i)) ≤
          2 * s := by
      calc
        _ = m.degree := leftDegree_add_rightDegree m
        _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hm
        _ ≤ 2 * s := hp
    by_cases hleft : ∑ i : Fin d, m (Sum.inl i) ≤ s
    · have hz := hmoment
          (⟨fun i => m (Sum.inl i), hleft⟩ : WeakComposition d s)
      simp only [monomialValue] at hz
      rw [hz, zero_mul]
    · have hright : ∑ i : Fin d, m (Sum.inr i) ≤ s := by omega
      have hz := hmoment
          (⟨fun i => m (Sum.inr i), hright⟩ : WeakComposition d s)
      simp only [monomialValue] at hz
      rw [hz, mul_zero]
  calc
    (∑ a, ∑ b, f a * f b * p.eval (pairCoordinates (x a) (x b))) =
        ∑ m ∈ p.support, p.coeff m *
          ((∑ a, f a * ∏ i : Fin d, (x a i) ^ m (Sum.inl i)) *
            (∑ b, f b * ∏ i : Fin d, (x b i) ^ m (Sum.inr i))) := by
      simp_rw [MvPolynomial.eval_eq', pairCoordinates_monomial]
      conv_lhs => simp only [Finset.mul_sum]
      calc
        (∑ a, ∑ b, ∑ m ∈ p.support,
            f a * f b * (p.coeff m *
              ((∏ i : Fin d, (x a i) ^ m (Sum.inl i)) *
                ∏ i : Fin d, (x b i) ^ m (Sum.inr i)))) =
            ∑ a, ∑ m ∈ p.support, ∑ b,
              f a * f b * (p.coeff m *
                ((∏ i : Fin d, (x a i) ^ m (Sum.inl i)) *
                  ∏ i : Fin d, (x b i) ^ m (Sum.inr i))) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.sum_comm]
        _ = ∑ m ∈ p.support, ∑ a, ∑ b,
              f a * f b * (p.coeff m *
                ((∏ i : Fin d, (x a i) ^ m (Sum.inl i)) *
                  ∏ i : Fin d, (x b i) ^ m (Sum.inr i))) := by
          rw [Finset.sum_comm]
        _ = ∑ m ∈ p.support, p.coeff m *
              ((∑ a, f a * ∏ i : Fin d, (x a i) ^ m (Sum.inl i)) *
                (∑ b, f b * ∏ i : Fin d, (x b i) ^ m (Sum.inr i))) := by
          apply Finset.sum_congr rfl
          intro m hm
          simp only [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          ring
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      rw [hterm m hm, mul_zero]

lemma momentMap_injective_of_polynomial_kernel
    {A : Type*} [Fintype A] {d s : ℕ} (x : A → Point d)
    (p : MvPolynomial (Sum (Fin d) (Fin d)) ℝ)
    (hp : p.totalDegree ≤ 2 * s) (c : ℝ) (hc : 0 < c)
    (hdiag : ∀ a, p.eval (pairCoordinates (x a) (x a)) = c)
    (hoffdiag : ∀ a b, a ≠ b → p.eval (pairCoordinates (x a) (x b)) = 0) :
    Function.Injective (momentMap x s) := by
  classical
  refine (injective_iff_map_eq_zero (momentMap x s)).2 ?_
  intro f hf
  have hdouble := polynomial_double_sum_eq_zero x p hp f hf
  have hkernel (a b : A) :
      p.eval (pairCoordinates (x a) (x b)) = if b = a then c else 0 := by
    split_ifs with hab
    · subst b
      exact hdiag a
    · exact hoffdiag a b (Ne.symm hab)
  have hsquares : c * ∑ a, f a ^ 2 = 0 := by
    rw [← hdouble]
    simp_rw [hkernel]
    simp only [mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [Finset.mul_sum]
    ring
  have hsum : ∑ a, f a ^ 2 = 0 := by
    exact (mul_eq_zero.mp hsquares).resolve_left hc.ne'
  funext a
  change f a = 0
  have hle : f a ^ 2 ≤ ∑ i, f i ^ 2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg (f i)) (Finset.mem_univ a)
  rw [hsum] at hle
  nlinarith [sq_nonneg (f a)]

lemma card_le_choose_of_polynomial_kernel
    {A : Type*} [Fintype A] {d s : ℕ} (x : A → Point d)
    (p : MvPolynomial (Sum (Fin d) (Fin d)) ℝ)
    (hp : p.totalDegree ≤ 2 * s) (c : ℝ) (hc : 0 < c)
    (hdiag : ∀ a, p.eval (pairCoordinates (x a) (x a)) = c)
    (hoffdiag : ∀ a b, a ≠ b → p.eval (pairCoordinates (x a) (x b)) = 0) :
    Fintype.card A ≤ (d + s).choose s := by
  have hi := momentMap_injective_of_polynomial_kernel x p hp c hc hdiag hoffdiag
  have hrank := (momentMap x s).finrank_le_finrank_of_injective hi
  simpa only [Module.finrank_fintype_fun_eq_card, card_weakComposition] using hrank

/-! ## The Euclidean distance kernel -/

/-- The squared Euclidean distance as a polynomial in two copies of the
coordinate variables. -/
noncomputable def sqDistPoly (d : ℕ) : MvPolynomial (Sum (Fin d) (Fin d)) ℝ :=
  ∑ i : Fin d,
    (MvPolynomial.X (Sum.inl i) - MvPolynomial.X (Sum.inr i)) ^ 2

lemma sqDistPoly_totalDegree (d : ℕ) : (sqDistPoly d).totalDegree ≤ 2 := by
  unfold sqDistPoly
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  have hsub :
      (MvPolynomial.X (Sum.inl i) - MvPolynomial.X (Sum.inr i) :
        MvPolynomial (Sum (Fin d) (Fin d)) ℝ).totalDegree ≤ 1 := by
    exact (MvPolynomial.totalDegree_sub _ _).trans (by simp)
  calc
    (((MvPolynomial.X (Sum.inl i) - MvPolynomial.X (Sum.inr i)) ^ 2 :
        MvPolynomial (Sum (Fin d) (Fin d)) ℝ)).totalDegree
        ≤ 2 * (MvPolynomial.X (Sum.inl i) -
          MvPolynomial.X (Sum.inr i) :
            MvPolynomial (Sum (Fin d) (Fin d)) ℝ).totalDegree :=
      MvPolynomial.totalDegree_pow _ _
    _ ≤ 2 * 1 := Nat.mul_le_mul_left 2 hsub
    _ = 2 := by omega

@[simp] lemma eval_sqDistPoly (d : ℕ) (x y : Point d) :
    (sqDistPoly d).eval (pairCoordinates x y) = dist x y ^ 2 := by
  simp only [sqDistPoly, map_sum, MvPolynomial.eval_sub, MvPolynomial.eval_X,
    map_pow, pairCoordinates_inl, pairCoordinates_inr]
  rw [EuclideanSpace.dist_sq_eq]
  congr 1
  funext i
  simp [Real.dist_eq, sq_abs]

/-- The product kernel associated to all distances occurring in `P`. -/
noncomputable def distanceKernel {d : ℕ} (P : Finset (Point d)) :
    MvPolynomial (Sum (Fin d) (Fin d)) ℝ :=
  open scoped Classical in
  ∏ r ∈ distanceFinset P,
    (MvPolynomial.C (r ^ 2) - sqDistPoly d)

lemma distanceKernel_totalDegree {d : ℕ} (P : Finset (Point d)) :
    (distanceKernel P).totalDegree ≤ 2 * distanceCount P := by
  classical
  unfold distanceKernel distanceCount
  calc
    (∏ r ∈ distanceFinset P,
        (MvPolynomial.C (r ^ 2) - sqDistPoly d)).totalDegree
        ≤ ∑ r ∈ distanceFinset P,
          (MvPolynomial.C (r ^ 2) - sqDistPoly d).totalDegree :=
      MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ _r ∈ distanceFinset P, 2 := by
      apply Finset.sum_le_sum
      intro r hr
      have hc : (MvPolynomial.C (r ^ 2) :
          MvPolynomial (Sum (Fin d) (Fin d)) ℝ).totalDegree ≤ 2 := by
        rw [MvPolynomial.totalDegree_C]
        omega
      exact (MvPolynomial.totalDegree_sub _ _).trans
        (max_le hc (sqDistPoly_totalDegree d))
    _ = 2 * (distanceFinset P).card := by simp [mul_comm]

@[simp] lemma eval_distanceKernel {d : ℕ} (P : Finset (Point d))
    (x y : Point d) :
    (distanceKernel P).eval (pairCoordinates x y) =
      ∏ r ∈ distanceFinset P, (r ^ 2 - dist x y ^ 2) := by
  classical
  simp [distanceKernel, eval_sqDistPoly]

/-- The positive value taken by the distance kernel on the diagonal. -/
noncomputable def distanceKernelDiagonal {d : ℕ} (P : Finset (Point d)) : ℝ :=
  open scoped Classical in
  ∏ r ∈ distanceFinset P, r ^ 2

lemma distanceKernelDiagonal_pos {d : ℕ} (P : Finset (Point d)) :
    0 < distanceKernelDiagonal P := by
  classical
  unfold distanceKernelDiagonal
  apply Finset.prod_pos
  intro r hr
  exact sq_pos_of_pos (distanceFinset_pos hr)

lemma eval_distanceKernel_eq_ite {d : ℕ} (P : Finset (Point d))
    (x y : {z // z ∈ P}) :
    (distanceKernel P).eval (pairCoordinates x.1 y.1) =
      if x = y then distanceKernelDiagonal P else 0 := by
  classical
  by_cases hxy : x = y
  · subst y
    simp [distanceKernelDiagonal]
  · have hval : (x : Point d) ≠ y := by
      intro h
      apply hxy
      exact Subtype.ext h
    have hmem : dist (x : Point d) y ∈ distanceFinset P :=
      mem_distanceFinset_iff.mpr
        ⟨x, x.property, y, y.property, hval, rfl⟩
    simp only [hxy, if_false, eval_distanceKernel]
    exact Finset.prod_eq_zero hmem (by ring)

/-- Bannai--Bannai--Stanton: an `s`-distance set in `ℝ^d` has at most
`choose (d+s) s` points. -/
theorem card_le_choose_of_distanceCount {d s : ℕ} (P : Finset (Point d))
    (hP : distanceCount P ≤ s) :
    P.card ≤ (d + s).choose s := by
  let x : {z // z ∈ P} → Point d := fun z => z.1
  have hdeg : (distanceKernel P).totalDegree ≤ 2 * s :=
    (distanceKernel_totalDegree P).trans (Nat.mul_le_mul_left 2 hP)
  have hdiag (a : {z // z ∈ P}) :
      (distanceKernel P).eval (pairCoordinates (x a) (x a)) =
        distanceKernelDiagonal P := by
    simpa using eval_distanceKernel_eq_ite P a a
  have hoffdiag (a b : {z // z ∈ P}) (hab : a ≠ b) :
      (distanceKernel P).eval (pairCoordinates (x a) (x b)) = 0 := by
    simpa [hab] using eval_distanceKernel_eq_ite P a b
  have hcard := card_le_choose_of_polynomial_kernel x (distanceKernel P) hdeg
    (distanceKernelDiagonal P) (distanceKernelDiagonal_pos P) hdiag hoffdiag
  simpa [Fintype.card_coe] using hcard

/-! ## The genuine minimal forcing number -/

lemma forcesDistances_upper (d n : ℕ) :
    ForcesDistances d n ((d + n - 1).choose (n - 1) + 1) := by
  intro P hP
  by_cases hn : n = 0
  · subst n
    exact Nat.zero_le _
  by_contra hbad
  have hcount : distanceCount P ≤ n - 1 := by omega
  have hcard := card_le_choose_of_distanceCount P hcount
  have hd : d + n - 1 = d + (n - 1) := by omega
  rw [hd] at hP
  rw [hP] at hcard
  omega

lemma exists_forcesDistances (d n : ℕ) : ∃ m, ForcesDistances d n m :=
  ⟨(d + n - 1).choose (n - 1) + 1, forcesDistances_upper d n⟩

/-- The least number of points that forces at least `n` distinct nonzero
distances in `ℝ^d`. -/
noncomputable def g (d n : ℕ) : ℕ :=
  sInf {m : ℕ | ForcesDistances d n m}

theorem g_spec (d n : ℕ) : ForcesDistances d n (g d n) :=
  csInf_mem (exists_forcesDistances d n)

theorem g_minimal {d n m : ℕ} (hm : m < g d n) : ¬ForcesDistances d n m :=
  fun h ↦ (not_le_of_gt hm) (csInf_le' h)

theorem g_le_of_forcesDistances {d n m : ℕ} (hm : ForcesDistances d n m) :
    g d n ≤ m :=
  csInf_le' hm

theorem g_upper_bound (d n : ℕ) :
    g d n ≤ (d + n - 1).choose (n - 1) + 1 :=
  g_le_of_forcesDistances (forcesDistances_upper d n)

theorem g_one (d : ℕ) : g d 1 = 2 := by
  have hu : g d 1 ≤ 2 := by
    simpa using g_upper_bound d 1
  have hne0 : g d 1 ≠ 0 := by
    intro hzero
    have hforce := g_spec d 1 (∅ : Finset (Point d)) (by simp [hzero])
    simp [distanceCount, distanceFinset] at hforce
  have hne1 : g d 1 ≠ 1 := by
    intro hone
    have hforce := g_spec d 1 ({0} : Finset (Point d)) (by simp [hone])
    simp [distanceCount, distanceFinset] at hforce
  omega

/-! ## The constant-weight lower construction -/

/-- Sum of the coordinates in `ℝ^(d+1)`. -/
def coordinateSum (d : ℕ) : Point (d + 1) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, x i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

lemma coordinateSum_surjective (d : ℕ) : Function.Surjective (coordinateSum d) := by
  intro r
  refine ⟨EuclideanSpace.single (0 : Fin (d + 1)) r, ?_⟩
  simp [coordinateSum]

lemma coordinateSum_ker_finrank (d : ℕ) :
    Module.finrank ℝ (coordinateSum d).ker = d := by
  have hrange : LinearMap.range (coordinateSum d) = ⊤ :=
    LinearMap.range_eq_top.mpr (coordinateSum_surjective d)
  have h := (coordinateSum d).finrank_range_add_finrank_ker
  rw [hrange, finrank_top] at h
  have hpoint : Module.finrank ℝ (Point (d + 1)) = d + 1 := by
    simp [Point]
  rw [hpoint] at h
  simp only [Module.finrank_self] at h
  omega

/-- A choice of an isometry from the coordinate-sum-zero hyperplane to
`ℝ^d`. -/
noncomputable def hyperplaneIsometry (d : ℕ) :
    (coordinateSum d).ker ≃ₗᵢ[ℝ] Point d :=
  ((stdOrthonormalBasis ℝ (coordinateSum d).ker).reindex
    (finCongr (coordinateSum_ker_finrank d))).repr

/-- The `0`--`1` indicator vector of a finset of coordinates. -/
def indicatorVector {d : ℕ} (I : Finset (Fin (d + 1))) : Point (d + 1) :=
  WithLp.toLp 2 fun i => if i ∈ I then (1 : ℝ) else 0

@[simp] lemma indicatorVector_apply {d : ℕ} (I : Finset (Fin (d + 1)))
    (i : Fin (d + 1)) :
    indicatorVector I i = if i ∈ I then (1 : ℝ) else 0 := rfl

/-- An integral scaling of the centered indicator vector. -/
def centeredIndicator (d s : ℕ) (I : Finset (Fin (d + 1))) : Point (d + 1) :=
  (d + 1 : ℝ) • indicatorVector I -
    (s : ℝ) • WithLp.toLp 2 (fun _ : Fin (d + 1) => (1 : ℝ))

lemma coordinateSum_centeredIndicator {d s : ℕ} {I : Finset (Fin (d + 1))}
    (hI : I.card = s) : coordinateSum d (centeredIndicator d s I) = 0 := by
  classical
  simp only [coordinateSum, LinearMap.coe_mk, AddHom.coe_mk, centeredIndicator,
    PiLp.sub_apply, PiLp.smul_apply, indicatorVector_apply]
  rw [Finset.sum_sub_distrib]
  simp [hI]
  ring

/-- The centered indicator bundled into the sum-zero hyperplane. -/
def centeredSubsetPoint (d s : ℕ)
    (I : {I // I ∈ (Finset.univ : Finset (Fin (d + 1))).powersetCard s}) :
    (coordinateSum d).ker :=
  ⟨centeredIndicator d s I.1,
    coordinateSum_centeredIndicator (Finset.mem_powersetCard.mp I.2).2⟩

/-- The point of `ℝ^d` associated to a constant-weight subset. -/
noncomputable def constantWeightPoint (d s : ℕ)
    (I : {I // I ∈ (Finset.univ : Finset (Fin (d + 1))).powersetCard s}) :
    Point d :=
  hyperplaneIsometry d (centeredSubsetPoint d s I)

lemma constantWeightPoint_injective (d s : ℕ) :
    Function.Injective (constantWeightPoint d s) := by
  classical
  intro I J hIJ
  have hcenter : centeredSubsetPoint d s I = centeredSubsetPoint d s J :=
    (hyperplaneIsometry d).injective hIJ
  apply Subtype.ext
  apply Finset.ext
  intro i
  constructor
  · intro hi
    by_contra hj
    have hcoord := congrArg
      (fun z : (coordinateSum d).ker => (z.1 : Point (d + 1)) i) hcenter
    simp [centeredSubsetPoint, centeredIndicator, hi, hj] at hcoord
    have hd : (0 : ℝ) < d + 1 := by positivity
    linarith
  · intro hj
    by_contra hi
    have hcoord := congrArg
      (fun z : (coordinateSum d).ker => (z.1 : Point (d + 1)) i) hcenter
    simp [centeredSubsetPoint, centeredIndicator, hi, hj] at hcoord
    have hd : (0 : ℝ) < d + 1 := by positivity
    linarith

/-- The constant-weight configuration in `ℝ^d`. -/
noncomputable def constantWeightConfiguration (d s : ℕ) : Finset (Point d) :=
  open scoped Classical in
  Finset.univ.image (constantWeightPoint d s)

lemma card_constantWeightConfiguration (d s : ℕ) :
    (constantWeightConfiguration d s).card = (d + 1).choose s := by
  classical
  rw [constantWeightConfiguration, Finset.card_image_of_injective _
    (constantWeightPoint_injective d s)]
  simp

private lemma indicator_sum {d : ℕ} (I : Finset (Fin (d + 1))) :
    ∑ i : Fin (d + 1), (if i ∈ I then (1 : ℝ) else 0) = I.card := by
  classical
  simp

private lemma indicator_diff_sq_sum {d : ℕ} (I J : Finset (Fin (d + 1))) :
    ∑ i : Fin (d + 1),
        ((if i ∈ I then (1 : ℝ) else 0) - (if i ∈ J then 1 else 0)) ^ 2 =
      (I.card : ℝ) + J.card - 2 * (I ∩ J).card := by
  classical
  calc
    _ = ∑ i : Fin (d + 1),
        ((if i ∈ I then (1 : ℝ) else 0) + (if i ∈ J then 1 else 0) -
          2 * ((if i ∈ I then (1 : ℝ) else 0) *
            (if i ∈ J then 1 else 0))) := by
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> norm_num
    _ = (I.card : ℝ) + J.card - 2 * (I ∩ J).card := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      simp [Finset.inter_comm]
      ring

lemma constantWeightPoint_dist_sq
    {d s : ℕ}
    (I J : {I // I ∈ (Finset.univ : Finset (Fin (d + 1))).powersetCard s}) :
    dist (constantWeightPoint d s I) (constantWeightPoint d s J) ^ 2 =
      (d + 1 : ℝ) ^ 2 * (2 * (s - (I.1 ∩ J.1).card) : ℕ) := by
  classical
  simp only [constantWeightPoint]
  rw [(hyperplaneIsometry d).isometry.dist_eq,
    Subtype.dist_eq, EuclideanSpace.dist_sq_eq]
  simp only [centeredSubsetPoint, centeredIndicator, PiLp.sub_apply, PiLp.smul_apply,
    indicatorVector_apply, Real.dist_eq, sq_abs, smul_eq_mul, mul_one]
  have hI := (Finset.mem_powersetCard.mp I.2).2
  have hJ := (Finset.mem_powersetCard.mp J.2).2
  rw [show (∑ i : Fin (d + 1),
      (((d + 1 : ℝ) * (if i ∈ I.1 then 1 else 0) - s) -
        ((d + 1 : ℝ) * (if i ∈ J.1 then 1 else 0) - s)) ^ 2) =
      (d + 1 : ℝ) ^ 2 * ∑ i : Fin (d + 1),
        ((if i ∈ I.1 then (1 : ℝ) else 0) -
          (if i ∈ J.1 then 1 else 0)) ^ 2 by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring]
  rw [indicator_diff_sq_sum, hI, hJ]
  have hinter : (I.1 ∩ J.1).card ≤ s := by
    calc
      (I.1 ∩ J.1).card ≤ I.1.card :=
        Finset.card_le_card Finset.inter_subset_left
      _ = s := hI
  rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hinter]
  ring

lemma distanceCount_constantWeightConfiguration (d s : ℕ) :
    distanceCount (constantWeightConfiguration d s) ≤ s := by
  classical
  let values : Finset ℝ := (Finset.Icc 1 s).image fun k =>
    Real.sqrt ((d + 1 : ℝ) ^ 2 * (2 * k : ℕ))
  have hsub : distanceFinset (constantWeightConfiguration d s) ⊆ values := by
    intro r hr
    obtain ⟨x, hx, y, hy, hxy, rfl⟩ := mem_distanceFinset_iff.mp hr
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hy
    have hIJ : I ≠ J := by
      intro h
      apply hxy
      exact congrArg (constantWeightPoint d s) h
    let k := s - (I.1 ∩ J.1).card
    have hk_le : k ≤ s := Nat.sub_le _ _
    have hinter_lt : (I.1 ∩ J.1).card < s := by
      have hIcard := (Finset.mem_powersetCard.mp I.2).2
      have hJcard := (Finset.mem_powersetCard.mp J.2).2
      have hinter_le : (I.1 ∩ J.1).card ≤ I.1.card :=
        Finset.card_le_card Finset.inter_subset_left
      calc
        (I.1 ∩ J.1).card < I.1.card := by
          apply lt_of_le_of_ne hinter_le
          intro heq
          have hinterI : I.1 ∩ J.1 = I.1 :=
            Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
          have hsubIJ : I.1 ⊆ J.1 := by
            intro z hz
            have : z ∈ I.1 ∩ J.1 := by simpa [hinterI] using hz
            exact (Finset.mem_inter.mp this).2
          have hEq : I.1 = J.1 :=
            Finset.eq_of_subset_of_card_le hsubIJ (by omega)
          exact hIJ (Subtype.ext hEq)
        _ = s := hIcard
    have hk_pos : 1 ≤ k := by omega
    apply Finset.mem_image.mpr
    refine ⟨k, Finset.mem_Icc.mpr ⟨hk_pos, hk_le⟩, ?_⟩
    symm
    apply (sq_eq_sq₀ dist_nonneg (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt]
    · exact constantWeightPoint_dist_sq I J
    · positivity
  calc
    distanceCount (constantWeightConfiguration d s) =
        (distanceFinset (constantWeightConfiguration d s)).card := rfl
    _ ≤ values.card := Finset.card_le_card hsub
    _ ≤ (Finset.Icc 1 s).card := Finset.card_image_le
    _ = s := by simp

theorem g_lower_bound {d n : ℕ} (hn : 2 ≤ n) :
    (d + 1).choose (n - 1) + 1 ≤ g d n := by
  let P := constantWeightConfiguration d (n - 1)
  have hcard : P.card = (d + 1).choose (n - 1) :=
    card_constantWeightConfiguration d (n - 1)
  have hcount : distanceCount P ≤ n - 1 :=
    distanceCount_constantWeightConfiguration d (n - 1)
  by_contra hbad
  have hle : g d n ≤ P.card := by omega
  obtain ⟨Q, hQP, hQcard⟩ := Finset.exists_subset_card_eq hle
  have hforce := g_spec d n Q hQcard
  have hdistSub : distanceFinset Q ⊆ distanceFinset P := by
    intro r hr
    obtain ⟨x, hx, y, hy, hxy, rfl⟩ := mem_distanceFinset_iff.mp hr
    exact mem_distanceFinset_iff.mpr ⟨x, hQP hx, y, hQP hy, hxy, rfl⟩
  have hQcount : distanceCount Q ≤ distanceCount P :=
    Finset.card_le_card hdistSub
  omega

/-! ## The fixed-`n` asymptotic -/

/-- For fixed `k` and fixed shift `c`, the shifted binomial coefficient has
the expected leading term `d^k / k!`. -/
lemma tendsto_choose_shift_div_pow (k c : ℕ) :
    Tendsto (fun d : ℕ => ((Nat.choose (d + c) k : ℕ) : ℝ) / (d : ℝ) ^ k)
      atTop (𝓝 ((1 : ℝ) / k.factorial)) := by
  have hshift := (isEquivalent_choose k).comp_tendsto (tendsto_add_atTop_nat c)
  have hequiv := hshift.div
    (IsEquivalent.refl :
      (fun d : ℕ => ((d : ℝ) ^ k)) ~[atTop] (fun d : ℕ => ((d : ℝ) ^ k)))
  have hratio :
      Tendsto (fun d : ℕ => (((d + c : ℕ) : ℝ) / (d : ℝ))) atTop (𝓝 1) := by
    simpa [Nat.cast_add, add_comm, add_left_comm, add_assoc] using
      (tendsto_add_mul_div_add_mul_atTop_nhds (c : ℝ) 0 1
        (by norm_num : (1 : ℝ) ≠ 0))
  have href :
      Tendsto (fun d : ℕ =>
        (((((d + c : ℕ) : ℝ) / (d : ℝ)) ^ k) / (k.factorial : ℝ)))
        atTop (𝓝 ((1 : ℝ) / k.factorial)) := by
    simpa using (hratio.pow k).div_const (k.factorial : ℝ)
  apply (IsEquivalent.tendsto_nhds_iff hequiv).2
  refine href.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with d hd
  dsimp
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  rw [div_pow]
  field_simp

lemma tendsto_one_div_pow {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun d : ℕ => (1 : ℝ) / (d : ℝ) ^ k) atTop (𝓝 0) := by
  have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).pow k
  have hk0 : k ≠ 0 := Nat.ne_of_gt hk
  simpa [div_pow, hk0] using h

lemma tendsto_choose_shift_add_one_div_pow (k c : ℕ) (hk : 1 ≤ k) :
    Tendsto
      (fun d : ℕ => (((Nat.choose (d + c) k + 1 : ℕ) : ℝ) / (d : ℝ) ^ k))
      atTop (𝓝 ((1 : ℝ) / k.factorial)) := by
  convert (tendsto_choose_shift_div_pow k c).add (tendsto_one_div_pow hk) using 1
  · funext d
    push_cast
    ring
  · ring

/-- The established two-sided estimate for Kelly's forcing number. -/
theorem g_bounds (n : ℕ) (hn : 2 ≤ n) (d : ℕ) :
    (d + 1).choose (n - 1) + 1 ≤ g d n ∧
      g d n ≤ (d + n - 1).choose (n - 1) + 1 :=
  ⟨g_lower_bound hn, g_upper_bound d n⟩

/-- For every fixed `n ≥ 2`, Kelly's forcing number has leading constant
`1 / (n-1)!`. -/
theorem g_limit (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1))
      atTop (𝓝 ((1 : ℝ) / (n - 1).factorial)) := by
  have hk : 1 ≤ n - 1 := by omega
  have hl := tendsto_choose_shift_add_one_div_pow (n - 1) 1 hk
  have hu := tendsto_choose_shift_add_one_div_pow (n - 1) (n - 1) hk
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards with d
    apply div_le_div_of_nonneg_right _ (pow_nonneg (Nat.cast_nonneg d) _)
    exact_mod_cast (g_lower_bound (d := d) hn)
  · filter_upwards with d
    apply div_le_div_of_nonneg_right _ (pow_nonneg (Nat.cast_nonneg d) _)
    have hg := g_upper_bound d n
    have hd : d + n - 1 = d + (n - 1) := by omega
    rw [hd] at hg
    exact_mod_cast hg

/-- Erdős Problem 1089: the exact polynomial-order estimate and the resulting
fixed-`n` limit. -/
theorem erdos_1089 (n : ℕ) (hn : 2 ≤ n) :
    (∀ d, (d + 1).choose (n - 1) + 1 ≤ g d n ∧
      g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
    Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1))
      atTop (𝓝 ((1 : ℝ) / (n - 1).factorial)) :=
  ⟨g_bounds n hn, g_limit n hn⟩

end Erdos1089

#print axioms Erdos1089.erdos_1089
