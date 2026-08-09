import Arxiv.Arxiv2407_19026.BookCor

/-!
# Optimizing descent to a candidate

This file formalizes the discrete descent mechanism in Section 4.  The
paper's compactness and computer-verified analytic inputs are represented
by explicit certificate structures; the combinatorial induction below
checks those inputs without adding axioms.
-/

noncomputable section

open Finset

namespace Arxiv2407_19026

/-- Uniform meaning of `R(k,l) ≤ exp(F(l/k) k + o(k))` in the range
`1 ≤ l ≤ k`. -/
def HasRamseyExponent (F : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ K : ℕ, ∀ k l : ℕ, K ≤ k → 1 ≤ l → l ≤ k →
      (ramseyNumber k l : ℝ) ≤
        Real.exp ((F ((l : ℝ) / k) + ε) * k)

/-- Integer threshold corresponding to equation `e:epsBound`. -/
def exponentThreshold (F : ℝ → ℝ) (ε : ℝ) (k l : ℕ) : ℕ :=
  ⌊Real.exp ((F ((l : ℝ) / k) + ε) * k)⌋₊

lemma exponentThreshold_le_exp (F : ℝ → ℝ) (ε : ℝ) (k l : ℕ) :
    (exponentThreshold F ε k l : ℝ) ≤
      Real.exp ((F ((l : ℝ) / k) + ε) * k) := by
  exact Nat.floor_le (Real.exp_nonneg _)

/-- Once the exponential is at least two, taking its natural-number floor
loses at most a factor of two. -/
lemma half_exp_le_exponentThreshold
    {F : ℝ → ℝ} {ε : ℝ} {k l : ℕ}
    (hlarge :
      2 ≤ Real.exp ((F ((l : ℝ) / k) + ε) * k)) :
    Real.exp ((F ((l : ℝ) / k) + ε) * k) / 2 ≤
      (exponentThreshold F ε k l : ℝ) := by
  have hfloor :
      Real.exp ((F ((l : ℝ) / k) + ε) * k) - 1 <
        (exponentThreshold F ε k l : ℝ) := by
    exact Nat.sub_one_lt_floor _
  linarith

/-- After reserving one vertex for the blue-neighborhood step, the floor
still loses at most a factor of two once the exponential is at least four. -/
lemma half_exp_le_exponentThreshold_sub_one
    {F : ℝ → ℝ} {ε : ℝ} {k l : ℕ}
    (hlarge :
      4 ≤ Real.exp ((F ((l : ℝ) / k) + ε) * k)) :
    Real.exp ((F ((l : ℝ) / k) + ε) * k) / 2 ≤
      (exponentThreshold F ε k l : ℝ) - 1 := by
  let E :=
    Real.exp ((F ((l : ℝ) / k) + ε) * k)
  have hfloor : E - 1 < (exponentThreshold F ε k l : ℝ) := by
    exact Nat.sub_one_lt_floor _
  dsimp [E] at hfloor hlarge ⊢
  linarith

/-- The loss from flooring and then reserving one vertex can be made an
arbitrary fixed fraction of the exponential.  This is the form needed by
the blue-neighborhood recurrence: unlike a factor of two, the factor `q`
can be chosen as close to one as the strict analytic margin permits. -/
lemma fraction_exp_le_exponentThreshold_sub_one
    {F : ℝ → ℝ} {ε q : ℝ} {k l : ℕ}
    (hq1 : q < 1)
    (hlarge :
      2 / (1 - q) ≤
        Real.exp ((F ((l : ℝ) / k) + ε) * k)) :
    q * Real.exp ((F ((l : ℝ) / k) + ε) * k) ≤
      (exponentThreshold F ε k l : ℝ) - 1 := by
  let E :=
    Real.exp ((F ((l : ℝ) / k) + ε) * k)
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  have hgap : 2 ≤ (1 - q) * E := by
    have := (div_le_iff₀ hden).1 (by simpa [E] using hlarge)
    change
      2 ≤ (1 - q) *
        Real.exp ((F ((l : ℝ) / k) + ε) * k)
    simpa [mul_comm] using this
  have hfloor : E - 1 < (exponentThreshold F ε k l : ℝ) := by
    exact Nat.sub_one_lt_floor _
  dsimp [E] at hgap hfloor ⊢
  linarith

/-- A real exponential inequality implies the exact floored blue-step
inequality used by `DescentCertificate`.  This packages all rounding loss. -/
lemma exponentThreshold_blue_step_of_exp
    {F : ℝ → ℝ} {ε p : ℝ} {k l : ℕ}
    (hp : 0 ≤ 1 - p)
    (hlarge :
      4 ≤ Real.exp ((F ((l : ℝ) / k) + ε) * k))
    (hstep :
      Real.exp ((F (((l - 1 : ℕ) : ℝ) / k) + ε) * k) ≤
        (1 - p) *
          (Real.exp ((F ((l : ℝ) / k) + ε) * k) / 2)) :
    (exponentThreshold F ε k (l - 1) : ℝ) ≤
      (1 - p) * (exponentThreshold F ε k l - 1) := by
  calc
    (exponentThreshold F ε k (l - 1) : ℝ) ≤
        Real.exp ((F (((l - 1 : ℕ) : ℝ) / k) + ε) * k) :=
      exponentThreshold_le_exp F ε k (l - 1)
    _ ≤ (1 - p) *
        (Real.exp ((F ((l : ℝ) / k) + ε) * k) / 2) := hstep
    _ ≤ (1 - p) * (exponentThreshold F ε k l - 1) := by
      exact mul_le_mul_of_nonneg_left
        (half_exp_le_exponentThreshold_sub_one hlarge) hp

/-- A real lower bound by half of the target exponential is enough for the
exact vertex threshold required by the dense book branch. -/
lemma bookGraphThreshold_le_exponentThreshold_of_le_half_exp
    {F : ℝ → ℝ} {ε x y μ : ℝ} {k l : ℕ}
    (hlarge :
      2 ≤ Real.exp ((F ((l : ℝ) / k) + ε) * k))
    (hbook :
      bookGraphThreshold x y μ k l ≤
        Real.exp ((F ((l : ℝ) / k) + ε) * k) / 2) :
    bookGraphThreshold x y μ k l ≤
      exponentThreshold F ε k l := by
  exact hbook.trans (half_exp_le_exponentThreshold hlarge)

/-- Every fixed real constant is eventually dominated by
`exp (ε k)` when `ε > 0`. -/
lemma eventually_const_le_exp_nat_mul (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in Filter.atTop,
      A ≤ Real.exp (ε * k) := by
  have hb : 1 < Real.exp ε := Real.one_lt_exp_iff.2 hε
  have hevent :=
    (tendsto_pow_atTop_atTop_of_one_lt hb).eventually
      (Filter.eventually_ge_atTop A)
  filter_upwards [hevent] with k hk
  simpa [← Real.exp_nat_mul, mul_comm] using hk

/-- If a target exponent is nonnegative on `[0,1]`, its `+ ε k`
slack eventually dominates the standard polynomial Ramsey bound for every
fixed finite range of the second parameter. -/
lemma exists_small_l_base_cutoff
    {F : ℝ → ℝ}
    (hF :
      ∀ z ∈ Set.Icc (0 : ℝ) 1, 0 ≤ F z)
    {ε : ℝ} (hε : 0 < ε) (L : ℕ) :
    ∃ K : ℕ, ∀ k l : ℕ, K ≤ k → 1 ≤ l → l ≤ k → l < L →
      RamseyProperty k l (exponentThreshold F ε k l) := by
  let b : ℝ := Real.exp (ε / 2)
  have hb : 1 < b := by
    dsimp [b]
    rw [Real.one_lt_exp_iff]
    linarith
  have hC : 0 < (2 : ℝ) ^ L := by positivity
  obtain ⟨K₀, hK₀⟩ := Filter.eventually_atTop.1
    (eventually_const_mul_nat_pow_le_pow
      (C := (2 : ℝ) ^ L) (b := b) hC hb)
  refine ⟨max K₀ 1, ?_⟩
  intro k l hk hl hlk hlL
  have hkK₀ : K₀ ≤ k := (le_max_left K₀ 1).trans hk
  have hk1 : 1 ≤ k := (le_max_right K₀ 1).trans hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
  have hz0 : (0 : ℝ) ≤ (l : ℝ) / k := by positivity
  have hz1 : (l : ℝ) / k ≤ 1 := by
    rw [div_le_one hkR]
    exact_mod_cast hlk
  have hF0 : 0 ≤ F ((l : ℝ) / k) :=
    hF _ ⟨hz0, hz1⟩
  have hpoly := hK₀ k hkK₀
  have hpowNat :
      (k + l) ^ l ≤ (2 * k) ^ L := by
    calc
      (k + l) ^ l ≤ (2 * k) ^ l :=
        Nat.pow_le_pow_left (by omega) l
      _ ≤ (2 * k) ^ L :=
        Nat.pow_le_pow_right (by omega) (by omega)
  have hpowReal :
      (((k + l) ^ l : ℕ) : ℝ) ≤
        (2 : ℝ) ^ L * (k : ℝ) ^ L := by
    calc
      (((k + l) ^ l : ℕ) : ℝ) ≤
          (((2 * k) ^ L : ℕ) : ℝ) := by exact_mod_cast hpowNat
      _ = (2 : ℝ) ^ L * (k : ℝ) ^ L := by
        push_cast
        rw [mul_pow]
  have hhalf :
      b ^ k = Real.exp ((ε / 2) * k) := by
    dsimp [b]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hslack :
      b ^ k ≤
        Real.exp ((F ((l : ℝ) / k) + ε) * k) := by
    rw [hhalf]
    exact Real.exp_le_exp_of_le (by
      have hk0 : (0 : ℝ) ≤ k := hkR.le
      nlinarith)
  have hfloor :
      (k + l) ^ l ≤ exponentThreshold F ε k l := by
    apply Nat.le_floor
    exact hpowReal.trans (hpoly.trans hslack)
  have hR :
      ramseyNumber k l ≤ exponentThreshold F ε k l :=
    (ramseyNumber_le_add_pow hk1 hl).trans hfloor
  exact Ramsey.ramseyProperty_mono_vertices hR
    (Ramsey.ramseyNumber_spec k l)

lemma sum_blueDegrees_add_redEdges {V : Type*}
    [Fintype V] (G : SimpleGraph V) :
    (∑ v : V, (blueNeighborsIn G v Finset.univ).card) +
        redEdgesBetween G Finset.univ Finset.univ =
      Fintype.card V * (Fintype.card V - 1) := by
  classical
  have hpoint :
      ∀ v : V,
        (blueNeighborsIn G v Finset.univ).card +
            (redNeighborsIn G v Finset.univ).card =
          Fintype.card V - 1 := by
    intro v
    have h := card_redNeighbors_add_card_blueNeighbors G v
    omega
  calc
    (∑ v : V, (blueNeighborsIn G v Finset.univ).card) +
          redEdgesBetween G Finset.univ Finset.univ =
        ∑ v : V,
          ((blueNeighborsIn G v Finset.univ).card +
            (redNeighborsIn G v Finset.univ).card) := by
      rw [redEdgesBetween_eq_sum_card]
      simp [sum_add_distrib]
    _ = ∑ _v : V, (Fintype.card V - 1) := by
      apply Finset.sum_congr rfl
      intro v _
      exact hpoint v
    _ = Fintype.card V * (Fintype.card V - 1) := by simp

/-- If the red density is below `p`, some vertex has more than the
complementary average blue degree. -/
lemma exists_large_blueDegree_of_globalRedDensity_lt
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) {p : ℝ}
    (hn : 2 ≤ Fintype.card V)
    (hp : globalRedDensity G < p) :
    ∃ v : V,
      (1 - p) * (Fintype.card V - 1) <
        (blueNeighborsIn G v Finset.univ).card := by
  classical
  let n := Fintype.card V
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) * (n - 1) := by
    have : 0 < (n : ℝ) - 1 := by linarith
    positivity
  have hred :
      (redEdgesBetween G Finset.univ Finset.univ : ℝ) <
        p * (n : ℝ) * (n - 1) := by
    have hp' :
        (redEdgesBetween G Finset.univ Finset.univ : ℝ) /
            ((n : ℝ) * (n - 1)) < p := by
      simpa [globalRedDensity, n] using hp
    simpa [mul_assoc] using (div_lt_iff₀ hden).1 hp'
  by_contra hnone
  push Not at hnone
  have hsumBlue :
      (∑ v : V, ((blueNeighborsIn G v Finset.univ).card : ℝ)) ≤
        (n : ℝ) * ((1 - p) * (n - 1)) := by
    calc
      (∑ v : V, ((blueNeighborsIn G v Finset.univ).card : ℝ)) ≤
          ∑ _v : V, (1 - p) * (n - 1) := by
        exact Finset.sum_le_sum fun v _ ↦ hnone v
      _ = (n : ℝ) * ((1 - p) * (n - 1)) := by
        simp [n, mul_comm]
  have hidentity :
      (∑ v : V, ((blueNeighborsIn G v Finset.univ).card : ℝ)) +
          redEdgesBetween G Finset.univ Finset.univ =
        (n : ℝ) * (n - 1) := by
    have hNat := congrArg (fun z : ℕ ↦ (z : ℝ))
      (sum_blueDegrees_add_redEdges G)
    simpa [n, Nat.cast_sub (by omega : 1 ≤ n)] using hNat
  nlinarith

/-- Data needed for one fully uniform application of the descent
argument. `active k l` is the range handled by the dense book branch;
the complementary range is supplied by `base`. -/
structure DescentCertificate
    (F : ℝ → ℝ) (ε : ℝ) where
  active : ℕ → ℕ → Prop
  p : ℕ → ℕ → ℝ
  cutoff : ℕ
  active_two :
    ∀ k l, cutoff ≤ k → 1 ≤ l → l ≤ k →
      active k l → 2 ≤ l
  threshold_two :
    ∀ k l, cutoff ≤ k → 1 ≤ l → l ≤ k →
      active k l → 2 ≤ exponentThreshold F ε k l
  p_bounds :
    ∀ k l, cutoff ≤ k → 1 ≤ l → l ≤ k →
      active k l → 0 < p k l ∧ p k l < 1
  base :
    ∀ k l, cutoff ≤ k → 1 ≤ l → l ≤ k →
      ¬active k l →
      RamseyProperty k l (exponentThreshold F ε k l)
  dense :
    ∀ k l, cutoff ≤ k → 1 ≤ l → l ≤ k →
      active k l →
      ∀ G : SimpleGraph (Fin (exponentThreshold F ε k l)),
        p k l ≤ globalRedDensity G →
        ¬(G.CliqueFree k ∧ G.IndepSetFree l)
  blue_step :
    ∀ k l, cutoff ≤ k → 1 ≤ l → l ≤ k →
      active k l →
      (exponentThreshold F ε k (l - 1) : ℝ) ≤
        (1 - p k l) *
          (exponentThreshold F ε k l - 1)

/-- One cell in a finite, piecewise-constant implementation of the book
branch.  The analytic hypotheses of `graph_good_bookCor` have already been
discharged, leaving only its uniform integer threshold and conclusion. -/
structure BookDescentCell where
  x : ℝ
  y : ℝ
  μ : ℝ
  p : ℝ
  p_pos : 0 < p
  p_lt_one : p < 1
  level : ℕ
  good :
    ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (k l : ℕ),
      1 ≤ k → 1 ≤ l → level ≤ l →
      p ≤ globalRedDensity G →
      bookGraphThreshold x y μ k l ≤ Fintype.card V →
      (∃ K : Finset V, G.IsNClique k K) ∨
        ∃ K : Finset V, G.IsNIndepSet l K

/-- Package an application of `graph_good_bookCor` as a finite-descent
cell.  This is the only place where the cell-specific book threshold is
chosen. -/
theorem exists_bookDescentCell
    {x y μ p : ℝ}
    (hx : 0 < x) (hx1 : x < 1)
    (hy : 0 < y) (hy1 : y < 1)
    (hμ : 0 < μ) (hμ1 : μ < 1)
    (hp : 0 < p) (hp1 : p < 1)
    (hlimit :
      x < p ^ ((1 : ℝ) / (1 - μ)) * (1 - μ))
    (hregion : (x, y) ∈ ramseyRegionInterior) :
    ∃ C : BookDescentCell,
      C.x = x ∧ C.y = y ∧ C.μ = μ ∧ C.p = p := by
  obtain ⟨L, hL⟩ := graph_good_bookCor
    hx hx1 hy hy1 hμ hμ1 hp hp1 hlimit hregion
  let C : BookDescentCell :=
    { x := x
      y := y
      μ := μ
      p := p
      p_pos := hp
      p_lt_one := hp1
      level := L
      good := hL }
  exact ⟨C, rfl, rfl, rfl, rfl⟩

/-- All pointwise hypotheses needed to turn four real parameters into a
uniform book-descent cell. -/
structure AdmissibleBookCellData where
  x : ℝ
  y : ℝ
  μ : ℝ
  p : ℝ
  x_pos : 0 < x
  x_lt_one : x < 1
  y_pos : 0 < y
  y_lt_one : y < 1
  μ_pos : 0 < μ
  μ_lt_one : μ < 1
  p_pos : 0 < p
  p_lt_one : p < 1
  limit :
    x < p ^ ((1 : ℝ) / (1 - μ)) * (1 - μ)
  region : (x, y) ∈ ramseyRegionInterior

/-- The noncomputable choice of the uniform integer level supplied by the
book theorem. -/
noncomputable def AdmissibleBookCellData.toCell
    (D : AdmissibleBookCellData) : BookDescentCell.{0} :=
  (exists_bookDescentCell
    D.x_pos D.x_lt_one D.y_pos D.y_lt_one
    D.μ_pos D.μ_lt_one D.p_pos D.p_lt_one
    D.limit D.region).choose

@[simp] lemma AdmissibleBookCellData.toCell_x
    (D : AdmissibleBookCellData) :
    D.toCell.x = D.x :=
  (exists_bookDescentCell
    D.x_pos D.x_lt_one D.y_pos D.y_lt_one
    D.μ_pos D.μ_lt_one D.p_pos D.p_lt_one
    D.limit D.region).choose_spec.1

@[simp] lemma AdmissibleBookCellData.toCell_y
    (D : AdmissibleBookCellData) :
    D.toCell.y = D.y :=
  (exists_bookDescentCell
    D.x_pos D.x_lt_one D.y_pos D.y_lt_one
    D.μ_pos D.μ_lt_one D.p_pos D.p_lt_one
    D.limit D.region).choose_spec.2.1

@[simp] lemma AdmissibleBookCellData.toCell_μ
    (D : AdmissibleBookCellData) :
    D.toCell.μ = D.μ :=
  (exists_bookDescentCell
    D.x_pos D.x_lt_one D.y_pos D.y_lt_one
    D.μ_pos D.μ_lt_one D.p_pos D.p_lt_one
    D.limit D.region).choose_spec.2.2.1

@[simp] lemma AdmissibleBookCellData.toCell_p
    (D : AdmissibleBookCellData) :
    D.toCell.p = D.p :=
  (exists_bookDescentCell
    D.x_pos D.x_lt_one D.y_pos D.y_lt_one
    D.μ_pos D.μ_lt_one D.p_pos D.p_lt_one
    D.limit D.region).choose_spec.2.2.2

private lemma exp_neg_nat_mul_log_opt
    {x : ℝ} (hx : 0 < x) (m : ℕ) :
    Real.exp (-(m : ℝ) * Real.log x) = x⁻¹ ^ m := by
  rw [show -(m : ℝ) * Real.log x =
      (m : ℕ) * (-Real.log x) by norm_num,
    Real.exp_nat_mul, Real.exp_neg, Real.exp_log hx]

/-- The logarithmic inequality used in the numerical optimization implies
the exact square-root book-threshold inequality. -/
lemma bookGraphThreshold_le_exp_of_log
    {F : ℝ → ℝ} {x y μ : ℝ} {k l : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hμ : 0 < μ)
    (hk : 1 ≤ k)
    (hlog :
      -(Real.log x +
          ((l : ℝ) / k) * Real.log μ +
          ((l : ℝ) / k) * Real.log y) / 2 ≤
        F ((l : ℝ) / k)) :
    bookGraphThreshold x y μ k l ≤
      Real.exp (F ((l : ℝ) / k) * k) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hscaled :
      -(k : ℝ) * Real.log x -
          (l : ℝ) * Real.log y -
          (l : ℝ) * Real.log μ ≤
        2 * F ((l : ℝ) / k) * k := by
    have := mul_le_mul_of_nonneg_right hlog
      (show (0 : ℝ) ≤ 2 * k by positivity)
    field_simp [hkR.ne'] at this
    nlinarith
  have hweight :
      bookWeight x y μ k l l =
        Real.exp
          (-(k : ℝ) * Real.log x -
            (l : ℝ) * Real.log y -
            (l : ℝ) * Real.log μ) := by
    rw [bookWeight,
      ← exp_neg_nat_mul_log_opt hx k,
      ← exp_neg_nat_mul_log_opt hy l,
      ← exp_neg_nat_mul_log_opt hμ l,
      ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [bookGraphThreshold, hweight]
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · rw [pow_two, ← Real.exp_add]
    exact Real.exp_le_exp_of_le (by
      convert hscaled using 1
      all_goals ring)

/-- A common active level for a finite family of book cells.  The extra two
also make the predecessor `l - 1` used by the blue step nontrivial. -/
def bookDescentLevel {ι : Type*} [Fintype ι]
    (cells : ι → BookDescentCell) : ℕ :=
  2 + Finset.univ.sup fun i ↦ (cells i).level

lemma BookDescentCell.level_le_bookDescentLevel
    {ι : Type*} [Fintype ι]
    (cells : ι → BookDescentCell) (i : ι) :
    (cells i).level ≤ bookDescentLevel cells := by
  have hsup :
      (cells i).level ≤ Finset.univ.sup fun j ↦ (cells j).level :=
    Finset.le_sup (f := fun j ↦ (cells j).level)
      (Finset.mem_univ i)
  dsimp [bookDescentLevel]
  omega

lemma two_le_bookDescentLevel
    {ι : Type*} [Fintype ι]
    (cells : ι → BookDescentCell) :
    2 ≤ bookDescentLevel cells := by
  dsimp [bookDescentLevel]
  omega

/-- Build a `DescentCertificate` from finitely many book cells.  All
graph-theoretic work, including uniformity of the dense branch, is handled
here.  The remaining four hypotheses are exact arithmetic obligations:
the small-`l` base case, target size, book size, and blue step. -/
def descentCertificateOfBookCells
    {F : ℝ → ℝ} {ε : ℝ} {ι : Type*} [Fintype ι]
    (cells : ι → BookDescentCell)
    (select : ℕ → ℕ → ι)
    (cutoff : ℕ)
    (hthreshold :
      ∀ k l, cutoff ≤ k → 1 ≤ l → l ≤ k →
        bookDescentLevel cells ≤ l →
        2 ≤ exponentThreshold F ε k l)
    (hbase :
      ∀ k l, cutoff ≤ k → 1 ≤ l → l ≤ k →
        ¬bookDescentLevel cells ≤ l →
        RamseyProperty k l (exponentThreshold F ε k l))
    (hbook :
      ∀ k l, cutoff ≤ k → 1 ≤ l → l ≤ k →
        bookDescentLevel cells ≤ l →
        bookGraphThreshold
            (cells (select k l)).x
            (cells (select k l)).y
            (cells (select k l)).μ k l ≤
          exponentThreshold F ε k l)
    (hblue :
      ∀ k l, cutoff ≤ k → 1 ≤ l → l ≤ k →
        bookDescentLevel cells ≤ l →
        (exponentThreshold F ε k (l - 1) : ℝ) ≤
          (1 - (cells (select k l)).p) *
            (exponentThreshold F ε k l - 1)) :
    DescentCertificate F ε where
  active k l := bookDescentLevel cells ≤ l
  p k l := (cells (select k l)).p
  cutoff := cutoff
  active_two k l _hk _hl _hlk hactive :=
    (two_le_bookDescentLevel cells).trans hactive
  threshold_two := hthreshold
  p_bounds k l _hk _hl _hlk _hactive :=
    ⟨(cells (select k l)).p_pos,
      (cells (select k l)).p_lt_one⟩
  base := hbase
  dense := by
    intro k l _hk hl _hlk hactive G hdensity hbad
    let C := cells (select k l)
    have hlevel : C.level ≤ l :=
      (BookDescentCell.level_le_bookDescentLevel
        cells (select k l)).trans hactive
    have hcard :
        bookGraphThreshold C.x C.y C.μ k l ≤
          Fintype.card
            (Fin (exponentThreshold F ε k l)) := by
      simpa [C] using hbook k l _hk hl _hlk hactive
    rcases C.good (Fin (exponentThreshold F ε k l))
        G k l (by omega) hl hlevel hdensity hcard with
      hred | hblue
    · obtain ⟨K, hK⟩ := hred
      exact hbad.1 K hK
    · obtain ⟨K, hK⟩ := hblue
      exact hbad.2 K hK
  blue_step := hblue

/-- Variant of `descentCertificateOfBookCells` with an arbitrary active
range.  This is the exact form used in the paper: the book cells handle
`l/k` bounded away from zero, while the complementary small-ratio range is
the entropy base case. -/
def descentCertificateOfBookCellsOn
    {F : ℝ → ℝ} {ε : ℝ} {ι : Type*} [Fintype ι]
    (cells : ι → BookDescentCell.{0})
    (select : ℕ → ℕ → ι)
    (active : ℕ → ℕ → Prop)
    (cutoff : ℕ)
    (hlevel :
      ∀ k l, cutoff ≤ k → 1 ≤ l → l ≤ k →
        active k l → bookDescentLevel cells ≤ l)
    (hthreshold :
      ∀ k l, cutoff ≤ k → 1 ≤ l → l ≤ k →
        active k l →
        2 ≤ exponentThreshold F ε k l)
    (hbase :
      ∀ k l, cutoff ≤ k → 1 ≤ l → l ≤ k →
        ¬active k l →
        RamseyProperty k l (exponentThreshold F ε k l))
    (hbook :
      ∀ k l, cutoff ≤ k → 1 ≤ l → l ≤ k →
        active k l →
        bookGraphThreshold
            (cells (select k l)).x
            (cells (select k l)).y
            (cells (select k l)).μ k l ≤
          exponentThreshold F ε k l)
    (hblue :
      ∀ k l, cutoff ≤ k → 1 ≤ l → l ≤ k →
        active k l →
        (exponentThreshold F ε k (l - 1) : ℝ) ≤
          (1 - (cells (select k l)).p) *
            (exponentThreshold F ε k l - 1)) :
    DescentCertificate F ε where
  active := active
  p k l := (cells (select k l)).p
  cutoff := cutoff
  active_two k l hk hl hlk hactive :=
    (two_le_bookDescentLevel cells).trans
      (hlevel k l hk hl hlk hactive)
  threshold_two := hthreshold
  p_bounds k l _hk _hl _hlk _hactive :=
    ⟨(cells (select k l)).p_pos,
      (cells (select k l)).p_lt_one⟩
  base := hbase
  dense := by
    intro k l hk hl hlk hactive G hdensity hbad
    let C := cells (select k l)
    have hcellLevel : C.level ≤ l :=
      (BookDescentCell.level_le_bookDescentLevel
        cells (select k l)).trans
        (hlevel k l hk hl hlk hactive)
    have hcard :
        bookGraphThreshold C.x C.y C.μ k l ≤
          Fintype.card
            (Fin (exponentThreshold F ε k l)) := by
      simpa [C] using hbook k l hk hl hlk hactive
    rcases C.good (Fin (exponentThreshold F ε k l))
        G k l (by omega) hl hcellLevel hdensity hcard with
      hred | hblue
    · obtain ⟨K, hK⟩ := hred
      exact hbad.1 K hK
    · obtain ⟨K, hK⟩ := hblue
      exact hbad.2 K hK
  blue_step := hblue

/-- The certified form of the induction in Theorem `t:general`. -/
theorem ramseyProperty_exponentThreshold_of_certificate
    {F : ℝ → ℝ} {ε : ℝ}
    (C : DescentCertificate F ε) :
    ∀ k l : ℕ, C.cutoff ≤ k → 1 ≤ l → l ≤ k →
      RamseyProperty k l (exponentThreshold F ε k l) := by
  intro k l
  induction l using Nat.strong_induction_on with
  | h l ih =>
      intro hk hl hlk
      by_cases hactive : C.active k l
      · intro G hbad
        by_cases hdense : C.p k l ≤ globalRedDensity G
        · exact C.dense k l hk hl hlk hactive G hdense hbad
        · have hlt : globalRedDensity G < C.p k l :=
            lt_of_not_ge hdense
          have hn :
              2 ≤ exponentThreshold F ε k l :=
            C.threshold_two k l hk hl hlk hactive
          obtain ⟨v, hv⟩ :=
            exists_large_blueDegree_of_globalRedDensity_lt
              G (by simpa using hn) hlt
          let B := blueNeighborsIn G v Finset.univ
          have hBcard :
              exponentThreshold F ε k (l - 1) ≤ B.card := by
            have hstep := C.blue_step k l hk hl hlk hactive
            have hv' :
                (exponentThreshold F ε k (l - 1) : ℝ) <
                  B.card := hstep.trans_lt (by simpa [B] using hv)
            exact_mod_cast hv'.le
          have hl2 : 2 ≤ l :=
            C.active_two k l hk hl hlk hactive
          have hprev :
              RamseyProperty k (l - 1)
                (exponentThreshold F ε k (l - 1)) :=
            ih (l - 1) (by omega) hk (by omega) (by omega)
          have hpropB : RamseyProperty k (l - 1) B.card :=
            Ramsey.ramseyProperty_mono_vertices hBcard hprev
          rcases red_or_blue_of_ramseyProperty B hpropB with
            ⟨K, hKB, hK⟩ | ⟨K, hKB, hK⟩
          · exact hbad.1 K hK
          · have hKcompl : Gᶜ.IsNClique (l - 1) K := by
              simpa using hK
            have hinsCompl : Gᶜ.IsNClique l (insert v K) := by
              simpa [Nat.sub_add_cancel (by omega : 1 ≤ l)] using
                hKcompl.insert (fun u hu ↦ by
                  have huB : u ∈ B := hKB hu
                  exact (mem_redNeighborsIn Gᶜ v u Finset.univ).1
                    (by simpa [B, blueNeighborsIn] using huB) |>.2)
            have hins : G.IsNIndepSet l (insert v K) := by
              simpa using hinsCompl
            exact hbad.2 (insert v K) hins
      · exact C.base k l hk hl hlk hactive

/-- A family of certificates for every error tolerance proves the
uniform `o(k)` exponent statement. -/
theorem hasRamseyExponent_of_certificates
    {F : ℝ → ℝ}
    (hcert :
      ∀ ε : ℝ, 0 < ε →
        Nonempty (DescentCertificate F ε)) :
    HasRamseyExponent F := by
  intro ε hε
  obtain ⟨C⟩ := hcert ε hε
  refine ⟨C.cutoff, ?_⟩
  intro k l hk hl hlk
  have hprop :=
    ramseyProperty_exponentThreshold_of_certificate C k l hk hl hlk
  have hR :
      ramseyNumber k l ≤ exponentThreshold F ε k l :=
    Ramsey.ramseyNumber_le_of_property hprop
  have hR' :
      (ramseyNumber k l : ℝ) ≤ exponentThreshold F ε k l := by
    exact_mod_cast hR
  exact hR'.trans (exponentThreshold_le_exp F ε k l)

/-- Convert scale-free book and blue-step estimates on an arbitrary active
range into one exact floored descent certificate.  `K₀` may encode the
Lebesgue number of a finite cover as well as the small-ratio base case. -/
theorem nonempty_descentCertificate_of_bookCellsOn
    {F : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    {ι : Type*} [Fintype ι]
    (cells : ι → BookDescentCell.{0})
    (select : ℕ → ℕ → ι)
    (active : ℕ → ℕ → Prop)
    {q : ℝ} (hq1 : q < 1)
    (hF :
      ∀ z ∈ Set.Icc (0 : ℝ) 1, 0 ≤ F z)
    (K₀ : ℕ)
    (hlevel :
      ∀ k l, K₀ ≤ k → 1 ≤ l → l ≤ k →
        active k l → bookDescentLevel cells ≤ l)
    (hbase :
      ∀ k l, K₀ ≤ k → 1 ≤ l → l ≤ k →
        ¬active k l →
        RamseyProperty k l (exponentThreshold F ε k l))
    (hbook :
      ∀ k l, K₀ ≤ k → 1 ≤ l → l ≤ k →
        active k l →
        bookGraphThreshold
            (cells (select k l)).x
            (cells (select k l)).y
            (cells (select k l)).μ k l ≤
          Real.exp (F ((l : ℝ) / k) * k))
    (hblue :
      ∀ k l, K₀ ≤ k → 1 ≤ l → l ≤ k →
        active k l →
        Real.exp (F (((l - 1 : ℕ) : ℝ) / k) * k) ≤
          q * (1 - (cells (select k l)).p) *
            Real.exp (F ((l : ℝ) / k) * k)) :
    Nonempty (DescentCertificate F ε) := by
  let A : ℝ := max 2 (2 / (1 - q))
  obtain ⟨Kscale, hKscale⟩ := Filter.eventually_atTop.1
    (eventually_const_le_exp_nat_mul A hε)
  let cutoff := max (max Kscale K₀) 1
  have hcutScale : Kscale ≤ cutoff :=
    le_trans (le_max_left Kscale K₀)
      (le_max_left (max Kscale K₀) 1)
  have hcut₀ : K₀ ≤ cutoff :=
    le_trans (le_max_right Kscale K₀)
      (le_max_left (max Kscale K₀) 1)
  have hcutOne : 1 ≤ cutoff :=
    le_max_right (max Kscale K₀) 1
  refine ⟨descentCertificateOfBookCellsOn
    cells select active cutoff ?_ ?_ ?_ ?_ ?_⟩
  · intro k l hk hl hlk hactive
    exact hlevel k l (hcut₀.trans hk) hl hlk hactive
  · intro k l hk hl hlk hactive
    have hk1 : 1 ≤ k := hcutOne.trans hk
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
    have hz0 : (0 : ℝ) ≤ (l : ℝ) / k := by positivity
    have hz1 : (l : ℝ) / k ≤ 1 := by
      rw [div_le_one hkR]
      exact_mod_cast hlk
    have hF0 : 0 ≤ F ((l : ℝ) / k) :=
      hF _ ⟨hz0, hz1⟩
    have hscale :
        A ≤ Real.exp (ε * k) :=
      hKscale k (hcutScale.trans hk)
    have htwo : 2 ≤ Real.exp (ε * k) :=
      (le_max_left _ _).trans hscale
    have hEF :
        1 ≤ Real.exp (F ((l : ℝ) / k) * k) :=
      Real.one_le_exp (mul_nonneg hF0 (by positivity))
    have hE :
        (2 : ℝ) ≤
          Real.exp ((F ((l : ℝ) / k) + ε) * k) := by
      rw [show (F ((l : ℝ) / k) + ε) * (k : ℝ) =
          F ((l : ℝ) / k) * k + ε * k by ring,
        Real.exp_add]
      nlinarith [Real.exp_pos (F ((l : ℝ) / k) * k),
        Real.exp_pos (ε * k)]
    exact Nat.le_floor hE
  · intro k l hk hl hlk hinactive
    exact hbase k l (hcut₀.trans hk) hl hlk hinactive
  · intro k l hk hl hlk hactive
    have hk1 : 1 ≤ k := hcutOne.trans hk
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
    have hz0 : (0 : ℝ) ≤ (l : ℝ) / k := by positivity
    have hz1 : (l : ℝ) / k ≤ 1 := by
      rw [div_le_one hkR]
      exact_mod_cast hlk
    have hF0 : 0 ≤ F ((l : ℝ) / k) :=
      hF _ ⟨hz0, hz1⟩
    have hscale :
        A ≤ Real.exp (ε * k) :=
      hKscale k (hcutScale.trans hk)
    have htwo : 2 ≤ Real.exp (ε * k) :=
      (le_max_left _ _).trans hscale
    have hEF :
        1 ≤ Real.exp (F ((l : ℝ) / k) * k) :=
      Real.one_le_exp (mul_nonneg hF0 (by positivity))
    have hE :
        (2 : ℝ) ≤
          Real.exp ((F ((l : ℝ) / k) + ε) * k) := by
      rw [show (F ((l : ℝ) / k) + ε) * (k : ℝ) =
          F ((l : ℝ) / k) * k + ε * k by ring,
        Real.exp_add]
      nlinarith [Real.exp_pos (F ((l : ℝ) / k) * k),
        Real.exp_pos (ε * k)]
    apply bookGraphThreshold_le_exponentThreshold_of_le_half_exp hE
    calc
      bookGraphThreshold
            (cells (select k l)).x
            (cells (select k l)).y
            (cells (select k l)).μ k l ≤
          Real.exp (F ((l : ℝ) / k) * k) :=
        hbook k l (hcut₀.trans hk) hl hlk hactive
      _ ≤ Real.exp ((F ((l : ℝ) / k) + ε) * k) / 2 := by
        rw [show (F ((l : ℝ) / k) + ε) * (k : ℝ) =
            F ((l : ℝ) / k) * k + ε * k by ring,
          Real.exp_add]
        have hpos := Real.exp_pos (F ((l : ℝ) / k) * k)
        nlinarith
  · intro k l hk hl hlk hactive
    have hk1 : 1 ≤ k := hcutOne.trans hk
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
    have hz0 : (0 : ℝ) ≤ (l : ℝ) / k := by positivity
    have hz1 : (l : ℝ) / k ≤ 1 := by
      rw [div_le_one hkR]
      exact_mod_cast hlk
    have hF0 : 0 ≤ F ((l : ℝ) / k) :=
      hF _ ⟨hz0, hz1⟩
    have hscale :
        A ≤ Real.exp (ε * k) :=
      hKscale k (hcutScale.trans hk)
    have hratio :
        2 / (1 - q) ≤ Real.exp (ε * k) :=
      (le_max_right _ _).trans hscale
    have hEF :
        1 ≤ Real.exp (F ((l : ℝ) / k) * k) :=
      Real.one_le_exp (mul_nonneg hF0 (by positivity))
    have hlarge :
        2 / (1 - q) ≤
          Real.exp ((F ((l : ℝ) / k) + ε) * k) := by
      rw [show (F ((l : ℝ) / k) + ε) * (k : ℝ) =
          F ((l : ℝ) / k) * k + ε * k by ring,
        Real.exp_add]
      calc
        2 / (1 - q) ≤ Real.exp (ε * k) := hratio
        _ = 1 * Real.exp (ε * k) := by ring
        _ ≤ Real.exp (F ((l : ℝ) / k) * k) *
            Real.exp (ε * k) := by
          exact mul_le_mul_of_nonneg_right hEF (Real.exp_nonneg _)
    have hfraction :=
      fraction_exp_le_exponentThreshold_sub_one
        (F := F) (ε := ε) (q := q) (k := k) (l := l)
        hq1 hlarge
    have hanalytic :=
      hblue k l (hcut₀.trans hk) hl hlk hactive
    calc
      (exponentThreshold F ε k (l - 1) : ℝ) ≤
          Real.exp
            ((F (((l - 1 : ℕ) : ℝ) / k) + ε) * k) :=
        exponentThreshold_le_exp F ε k (l - 1)
      _ = Real.exp (F (((l - 1 : ℕ) : ℝ) / k) * k) *
            Real.exp (ε * k) := by
        rw [show
          (F (((l - 1 : ℕ) : ℝ) / k) + ε) * (k : ℝ) =
            F (((l - 1 : ℕ) : ℝ) / k) * k + ε * k by ring,
          Real.exp_add]
      _ ≤
          (q * (1 - (cells (select k l)).p) *
              Real.exp (F ((l : ℝ) / k) * k)) *
            Real.exp (ε * k) :=
        mul_le_mul_of_nonneg_right hanalytic (Real.exp_nonneg _)
      _ = (1 - (cells (select k l)).p) *
          (q * (Real.exp (F ((l : ℝ) / k) * k) *
            Real.exp (ε * k))) := by ring
      _ ≤ (1 - (cells (select k l)).p) *
          (exponentThreshold F ε k l - 1) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa [show (F ((l : ℝ) / k) + ε) * (k : ℝ) =
              F ((l : ℝ) / k) * k + ε * k by ring,
            Real.exp_add] using hfraction)
          (sub_nonneg.mpr (cells (select k l)).p_lt_one.le)

/-- A finite family of book cells proves an exponent bound once two exact
analytic inequalities are available:

* the book threshold is at most `exp (F(l/k) k)`;
* one blue step loses at most `q (1-p)`, for a fixed `q < 1`.

The theorem absorbs every constant, every natural-number floor, and the
finite small-`l` range into the `+ ε k` slack.  Thus subsequent numerical
files only have to certify the two scale-free inequalities. -/
theorem hasRamseyExponent_of_bookCells
    {F : ℝ → ℝ} {ι : Type*} [Fintype ι]
    (cells : ι → BookDescentCell.{0})
    (select : ℕ → ℕ → ι)
    {q : ℝ} (hq1 : q < 1)
    (hF :
      ∀ z ∈ Set.Icc (0 : ℝ) 1, 0 ≤ F z)
    (hbook :
      ∀ k l : ℕ, 1 ≤ k → 1 ≤ l → l ≤ k →
        bookDescentLevel cells ≤ l →
        bookGraphThreshold
            (cells (select k l)).x
            (cells (select k l)).y
            (cells (select k l)).μ k l ≤
          Real.exp (F ((l : ℝ) / k) * k))
    (hblue :
      ∀ k l : ℕ, 1 ≤ k → 1 ≤ l → l ≤ k →
        bookDescentLevel cells ≤ l →
        Real.exp (F (((l - 1 : ℕ) : ℝ) / k) * k) ≤
          q * (1 - (cells (select k l)).p) *
            Real.exp (F ((l : ℝ) / k) * k)) :
    HasRamseyExponent F := by
  apply hasRamseyExponent_of_certificates
  intro ε hε
  let A : ℝ := max 2 (2 / (1 - q))
  obtain ⟨Kscale, hKscale⟩ := Filter.eventually_atTop.1
    (eventually_const_le_exp_nat_mul A hε)
  obtain ⟨Kbase, hKbase⟩ :=
    exists_small_l_base_cutoff hF hε (bookDescentLevel cells)
  let cutoff := max (max Kscale Kbase) 1
  have hcutScale : Kscale ≤ cutoff :=
    le_trans (le_max_left Kscale Kbase)
      (le_max_left (max Kscale Kbase) 1)
  have hcutBase : Kbase ≤ cutoff :=
    le_trans (le_max_right Kscale Kbase)
      (le_max_left (max Kscale Kbase) 1)
  have hcutOne : 1 ≤ cutoff :=
    le_max_right (max Kscale Kbase) 1
  refine ⟨descentCertificateOfBookCells
    cells select cutoff ?_ ?_ ?_ ?_⟩
  · intro k l hk hl hlk hactive
    have hk1 : 1 ≤ k := hcutOne.trans hk
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
    have hz0 : (0 : ℝ) ≤ (l : ℝ) / k := by positivity
    have hz1 : (l : ℝ) / k ≤ 1 := by
      rw [div_le_one hkR]
      exact_mod_cast hlk
    have hF0 : 0 ≤ F ((l : ℝ) / k) :=
      hF _ ⟨hz0, hz1⟩
    have hscale :
        A ≤ Real.exp (ε * k) :=
      hKscale k (hcutScale.trans hk)
    have htwo : 2 ≤ Real.exp (ε * k) :=
      (le_max_left _ _).trans hscale
    have hEF :
        1 ≤ Real.exp (F ((l : ℝ) / k) * k) :=
      Real.one_le_exp (mul_nonneg hF0 (by positivity))
    have hE :
        (2 : ℝ) ≤
          Real.exp ((F ((l : ℝ) / k) + ε) * k) := by
      rw [show (F ((l : ℝ) / k) + ε) * (k : ℝ) =
          F ((l : ℝ) / k) * k + ε * k by ring,
        Real.exp_add]
      nlinarith [Real.exp_pos (F ((l : ℝ) / k) * k),
        Real.exp_pos (ε * k)]
    exact Nat.le_floor hE
  · intro k l hk hl hlk hinactive
    exact hKbase k l (hcutBase.trans hk) hl hlk (by omega)
  · intro k l hk hl hlk hactive
    have hk1 : 1 ≤ k := hcutOne.trans hk
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
    have hz0 : (0 : ℝ) ≤ (l : ℝ) / k := by positivity
    have hz1 : (l : ℝ) / k ≤ 1 := by
      rw [div_le_one hkR]
      exact_mod_cast hlk
    have hF0 : 0 ≤ F ((l : ℝ) / k) :=
      hF _ ⟨hz0, hz1⟩
    have hscale :
        A ≤ Real.exp (ε * k) :=
      hKscale k (hcutScale.trans hk)
    have htwo : 2 ≤ Real.exp (ε * k) :=
      (le_max_left _ _).trans hscale
    have hEF :
        1 ≤ Real.exp (F ((l : ℝ) / k) * k) :=
      Real.one_le_exp (mul_nonneg hF0 (by positivity))
    have hE :
        (2 : ℝ) ≤
          Real.exp ((F ((l : ℝ) / k) + ε) * k) := by
      rw [show (F ((l : ℝ) / k) + ε) * (k : ℝ) =
          F ((l : ℝ) / k) * k + ε * k by ring,
        Real.exp_add]
      nlinarith [Real.exp_pos (F ((l : ℝ) / k) * k),
        Real.exp_pos (ε * k)]
    apply bookGraphThreshold_le_exponentThreshold_of_le_half_exp hE
    calc
      bookGraphThreshold
            (cells (select k l)).x
            (cells (select k l)).y
            (cells (select k l)).μ k l ≤
          Real.exp (F ((l : ℝ) / k) * k) :=
        hbook k l hk1 hl hlk hactive
      _ ≤ Real.exp ((F ((l : ℝ) / k) + ε) * k) / 2 := by
        rw [show (F ((l : ℝ) / k) + ε) * (k : ℝ) =
            F ((l : ℝ) / k) * k + ε * k by ring,
          Real.exp_add]
        have hpos := Real.exp_pos (F ((l : ℝ) / k) * k)
        nlinarith
  · intro k l hk hl hlk hactive
    have hk1 : 1 ≤ k := hcutOne.trans hk
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
    have hz0 : (0 : ℝ) ≤ (l : ℝ) / k := by positivity
    have hz1 : (l : ℝ) / k ≤ 1 := by
      rw [div_le_one hkR]
      exact_mod_cast hlk
    have hF0 : 0 ≤ F ((l : ℝ) / k) :=
      hF _ ⟨hz0, hz1⟩
    have hscale :
        A ≤ Real.exp (ε * k) :=
      hKscale k (hcutScale.trans hk)
    have hratio :
        2 / (1 - q) ≤ Real.exp (ε * k) :=
      (le_max_right _ _).trans hscale
    have hEF :
        1 ≤ Real.exp (F ((l : ℝ) / k) * k) :=
      Real.one_le_exp (mul_nonneg hF0 (by positivity))
    have hlarge :
        2 / (1 - q) ≤
          Real.exp ((F ((l : ℝ) / k) + ε) * k) := by
      rw [show (F ((l : ℝ) / k) + ε) * (k : ℝ) =
          F ((l : ℝ) / k) * k + ε * k by ring,
        Real.exp_add]
      calc
        2 / (1 - q) ≤ Real.exp (ε * k) := hratio
        _ = 1 * Real.exp (ε * k) := by ring
        _ ≤ Real.exp (F ((l : ℝ) / k) * k) *
            Real.exp (ε * k) := by
          exact mul_le_mul_of_nonneg_right hEF (Real.exp_nonneg _)
    have hfraction :=
      fraction_exp_le_exponentThreshold_sub_one
        (F := F) (ε := ε) (q := q) (k := k) (l := l)
        hq1 hlarge
    have hanalytic :=
      hblue k l hk1 hl hlk hactive
    calc
      (exponentThreshold F ε k (l - 1) : ℝ) ≤
          Real.exp
            ((F (((l - 1 : ℕ) : ℝ) / k) + ε) * k) :=
        exponentThreshold_le_exp F ε k (l - 1)
      _ = Real.exp (F (((l - 1 : ℕ) : ℝ) / k) * k) *
            Real.exp (ε * k) := by
        rw [show
          (F (((l - 1 : ℕ) : ℝ) / k) + ε) * (k : ℝ) =
            F (((l - 1 : ℕ) : ℝ) / k) * k + ε * k by ring,
          Real.exp_add]
      _ ≤
          (q * (1 - (cells (select k l)).p) *
              Real.exp (F ((l : ℝ) / k) * k)) *
            Real.exp (ε * k) :=
        mul_le_mul_of_nonneg_right hanalytic (Real.exp_nonneg _)
      _ = (1 - (cells (select k l)).p) *
          (q * (Real.exp (F ((l : ℝ) / k) * k) *
            Real.exp (ε * k))) := by ring
      _ ≤ (1 - (cells (select k l)).p) *
          (exponentThreshold F ε k l - 1) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa [show (F ((l : ℝ) / k) + ε) * (k : ℝ) =
              F ((l : ℝ) / k) * k + ε * k by ring,
            Real.exp_add] using hfraction)
          (sub_nonneg.mpr (cells (select k l)).p_lt_one.le)

end Arxiv2407_19026
