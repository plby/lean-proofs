/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos182.Elementary
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Combinatorics.SimpleGraph.Regularity.Equitabilise
import Mathlib.Data.Set.PowersetCard
import Mathlib.Tactic

/-!
# Erdős Problem 1021

For `k ≥ 3`, the graph `cliqueSubdivision k` is the one-subdivision of `K_k`.
This file proves Janzer's bound

`ex(n, cliqueSubdivision k) = O(n ^ (3 / 2 - 1 / (4 * k - 6)))`.

The complete mathematical proof and a map from its lemmas to this development
are in `tex/1021.tex`.
-/

open Filter
open Asymptotics
open scoped BigOperators Classical SimpleGraph

namespace Erdos1021

set_option autoImplicit false

/-! ## The exact forbidden graph -/

/-- The unordered pairs of a `k`-element type. -/
abbrev CliquePair (k : ℕ) := Set.powersetCard (Fin k) 2

@[simp] theorem card_cliquePair (k : ℕ) :
    Fintype.card (CliquePair k) = k.choose 2 := by
  change Fintype.card (Set.powersetCard (Fin k) 2) = k.choose 2
  rw [Fintype.card_eq_nat_card, Set.powersetCard.card]
  simp

/-- The vertices of the one-subdivision of `K_k`: old vertices on the left,
and one new vertex for every unordered pair on the right. -/
abbrev CliqueSubdivisionVertex (k : ℕ) := Fin k ⊕ CliquePair k

/-- The incidence graph between the vertices and two-element subsets of `Fin k`.
This is exactly the graph `G_k` in Erdős Problem 1021. -/
def cliqueSubdivision (k : ℕ) : SimpleGraph (CliqueSubdivisionVertex k) where
  Adj x y :=
    match x, y with
    | Sum.inl i, Sum.inr p => i ∈ (p : Finset (Fin k))
    | Sum.inr p, Sum.inl i => i ∈ (p : Finset (Fin k))
    | _, _ => False
  symm := by
    constructor
    intro x y h
    cases x <;> cases y <;> simpa using h
  loopless := by
    constructor
    intro x
    cases x <;> simp

instance cliqueSubdivision.instDecidableAdj (k : ℕ) :
    DecidableRel (cliqueSubdivision k).Adj := by
  intro x y
  cases x <;> cases y <;> simp only [cliqueSubdivision] <;> infer_instance

theorem cliqueSubdivision_isBipartite (k : ℕ) :
    (cliqueSubdivision k).IsBipartite := by
  let c : (cliqueSubdivision k).Coloring Bool :=
    { toFun := fun x => Sum.elim (fun _ => false) (fun _ => true) x
      map_rel' := by
        intro x y h
        cases x <;> cases y <;> simp_all [cliqueSubdivision] }
  exact c.colorable

/-- A convenient introduction rule for a concrete copy of the subdivision. -/
theorem cliqueSubdivision_isContained_of_maps
    {k : ℕ} {V : Type*} (G : SimpleGraph V)
    (branch : Fin k → V) (middle : CliquePair k → V)
    (hbranch : Function.Injective branch)
    (hmiddle : Function.Injective middle)
    (hdisjoint : ∀ (i : Fin k) (p : CliquePair k), branch i ≠ middle p)
    (hadj : ∀ (i : Fin k) (p : CliquePair k),
      i ∈ (p : Finset (Fin k)) → G.Adj (branch i) (middle p)) :
    cliqueSubdivision k ⊑ G := by
  let f : cliqueSubdivision k →g G :=
    { toFun := Sum.elim branch middle
      map_rel' := by
        intro x y hxy
        cases x with
        | inl i =>
            cases y with
            | inl j => simp [cliqueSubdivision] at hxy
            | inr p => exact hadj i p hxy
        | inr p =>
            cases y with
            | inl i => exact (hadj i p hxy).symm
            | inr q => simp [cliqueSubdivision] at hxy }
  refine ⟨f, ?_⟩
  intro x y hxy
  cases x with
  | inl i =>
      cases y with
      | inl j => exact congrArg Sum.inl (hbranch (by simpa [f] using hxy))
      | inr p => exact (hdisjoint i p (by simpa [f] using hxy)).elim
  | inr p =>
      cases y with
      | inl i => exact (hdisjoint i p (by simpa [f] using hxy.symm)).elim
      | inr q => exact congrArg Sum.inr (hmiddle (by simpa [f] using hxy))

/-! ## Extremal and asymptotic notation -/

/-- The real-valued extremal-number function of a fixed graph. -/
noncomputable def extremalGrowth {W : Type*} (H : SimpleGraph W) (n : ℕ) : ℝ :=
  SimpleGraph.extremalNumber n H

/-- Real powers on natural-number inputs. -/
noncomputable def polynomialGrowth (a : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ a

/-- Janzer's power-saving exponent. -/
noncomputable def janzerSaving (k : ℕ) : ℝ :=
  1 / (4 * (k : ℝ) - 6)

/-- The exponent above the linear term in Janzer's estimate. -/
noncomputable def janzerAlpha (k : ℕ) : ℝ :=
  ((k : ℝ) - 2) / (2 * k - 3)

theorem janzerSaving_pos {k : ℕ} (hk : 3 ≤ k) : 0 < janzerSaving k := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  unfold janzerSaving
  rw [one_div_pos]
  linarith

theorem janzerAlpha_pos {k : ℕ} (hk : 3 ≤ k) : 0 < janzerAlpha k := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  unfold janzerAlpha
  exact div_pos (by linarith) (by linarith)

theorem janzerAlpha_lt_one {k : ℕ} (hk : 3 ≤ k) : janzerAlpha k < 1 := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  unfold janzerAlpha
  apply (div_lt_one (by linarith)).mpr
  linarith

/-- The fixed arity used in the finite density-regularization recursion. -/
def regularizationParts : ℕ := 2 ^ 24

theorem regularizationParts_eq : regularizationParts = 16777216 := by
  native_decide

theorem janzerAlpha_ge_quarter {k : ℕ} (hk : 3 ≤ k) :
    (4 : ℝ)⁻¹ ≤ janzerAlpha k := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hden : 0 < 2 * (k : ℝ) - 3 := by linarith
  unfold janzerAlpha
  apply (le_div_iff₀ hden).2
  nlinarith

theorem one_add_janzerAlpha_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < 1 + janzerAlpha k := by
  linarith [janzerAlpha_pos hk]

theorem one_add_janzerAlpha_le_two {k : ℕ} (hk : 3 ≤ k) :
    1 + janzerAlpha k ≤ 2 := by
  linarith [janzerAlpha_lt_one hk]

theorem sixtyFour_le_regularizationParts_rpow {k : ℕ} (hk : 3 ≤ k) :
    (64 : ℝ) ≤ (regularizationParts : ℝ) ^ janzerAlpha k := by
  have hbase : (1 : ℝ) ≤ regularizationParts := by
    norm_num [regularizationParts]
  calc
    (64 : ℝ) = (regularizationParts : ℝ) ^ ((4 : ℝ)⁻¹) := by
      apply (pow_left_inj₀ (by positivity : (0 : ℝ) ≤ 64)
        (Real.rpow_nonneg (by positivity) _) (by norm_num : (4 : ℕ) ≠ 0)).mp
      have hroot := Real.rpow_inv_natCast_pow
        (x := (regularizationParts : ℝ)) (n := 4)
        (by positivity) (by norm_num)
      calc
        (64 : ℝ) ^ (4 : ℕ) = regularizationParts := by
          norm_num [regularizationParts]
        _ = ((regularizationParts : ℝ) ^ ((4 : ℝ)⁻¹)) ^ (4 : ℕ) :=
          hroot.symm
    _ ≤ (regularizationParts : ℝ) ^ janzerAlpha k :=
      Real.rpow_le_rpow_of_exponent_le hbase (janzerAlpha_ge_quarter hk)

/-- The numerical inequality that pays for one high-degree branch of the
regularization recursion. -/
theorem regularization_rpow_contraction {k m n : ℕ} (hk : 3 ≤ k)
    (hsize : regularizationParts * m ≤ 4 * n) :
    (4 * regularizationParts : ℝ) * (m : ℝ) ^ (1 + janzerAlpha k) ≤
      (n : ℝ) ^ (1 + janzerAlpha k) := by
  let p := 1 + janzerAlpha k
  have hp : 0 < p := one_add_janzerAlpha_pos hk
  have hp2 : p ≤ 2 := one_add_janzerAlpha_le_two hk
  have hsizeR : (regularizationParts : ℝ) * m ≤ 4 * n := by
    exact_mod_cast hsize
  have hpowSize : ((regularizationParts : ℝ) * m) ^ p ≤
      ((4 : ℝ) * n) ^ p :=
    Real.rpow_le_rpow (by positivity) hsizeR hp.le
  have hfour : (4 : ℝ) ^ p ≤ 16 := by
    calc
      (4 : ℝ) ^ p ≤ (4 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hp2
      _ = 16 := by norm_num
  have hM : (64 : ℝ) * regularizationParts ≤
      (regularizationParts : ℝ) ^ p := by
    rw [show p = 1 + janzerAlpha k by rfl,
      Real.rpow_add (by norm_num [regularizationParts]), Real.rpow_one]
    have := sixtyFour_le_regularizationParts_rpow hk
    nlinarith [show (0 : ℝ) < regularizationParts by
      norm_num [regularizationParts]]
  have hchain : (64 : ℝ) * regularizationParts * (m : ℝ) ^ p ≤
      16 * (n : ℝ) ^ p := by
    calc
      (64 : ℝ) * regularizationParts * (m : ℝ) ^ p ≤
          (regularizationParts : ℝ) ^ p * (m : ℝ) ^ p := by gcongr
      _ = ((regularizationParts : ℝ) * m) ^ p := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
      _ ≤ ((4 : ℝ) * n) ^ p := hpowSize
      _ = (4 : ℝ) ^ p * (n : ℝ) ^ p := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
      _ ≤ 16 * (n : ℝ) ^ p := by gcongr
  nlinarith

theorem janzerExponent_eq {k : ℕ} (hk : 3 ≤ k) :
    1 + janzerAlpha k = 3 / 2 - janzerSaving k := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have h₁ : (2 * (k : ℝ) - 3) ≠ 0 := by linarith
  unfold janzerSaving janzerAlpha
  rw [show 4 * (k : ℝ) - 6 = 2 * (2 * (k : ℝ) - 3) by ring]
  have hi := mul_inv_cancel₀ h₁
  norm_num [div_eq_mul_inv] at hi ⊢
  nlinarith

theorem natCast_pow_le_janzerAlpha_average
    {k i N : ℕ} (hk : 3 ≤ k) (hi : i < k - 1) (hN : 1 ≤ N) :
    (N : ℝ) ^ i ≤ ((N : ℝ) ^ janzerAlpha k) ^ (2 * i + 1) := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hiNat : i ≤ k - 2 := by omega
  have hi' : (i : ℝ) ≤ k - 2 := by
    have hiCast : (i : ℝ) ≤ (k - 2 : ℕ) := by exact_mod_cast hiNat
    simpa [Nat.cast_sub (by omega : 2 ≤ k)] using hiCast
  have hden : 0 < 2 * (k : ℝ) - 3 := by linarith
  have hexp : (i : ℝ) ≤ janzerAlpha k * (2 * (i : ℝ) + 1) := by
    unfold janzerAlpha
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hden).2
    nlinarith
  have hbase : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hnonneg : (0 : ℝ) ≤ N := by positivity
  calc
    (N : ℝ) ^ i = (N : ℝ) ^ (i : ℝ) := (Real.rpow_natCast _ i).symm
    _ ≤ (N : ℝ) ^ (janzerAlpha k * (2 * (i : ℝ) + 1)) :=
      Real.rpow_le_rpow_of_exponent_le hbase hexp
    _ = ((N : ℝ) ^ janzerAlpha k) ^ (2 * i + 1) := by
      rw [show 2 * (i : ℝ) + 1 = ((2 * i + 1 : ℕ) : ℝ) by norm_num,
        Real.rpow_mul hnonneg, Real.rpow_natCast]

theorem natCast_pow_le_janzerAlpha_room
    {k i N : ℕ} (hk : 3 ≤ k) (hi : i < k) (hi₀ : 0 < i) (hN : 1 ≤ N) :
    (N : ℝ) ^ i ≤
      (N : ℝ) * ((N : ℝ) ^ janzerAlpha k) ^ (2 * i - 1) := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hiNat : i ≤ k - 1 := by omega
  have hi' : (i : ℝ) ≤ k - 1 := by
    have hiCast : (i : ℝ) ≤ (k - 1 : ℕ) := by exact_mod_cast hiNat
    simpa [Nat.cast_sub (by omega : 1 ≤ k)] using hiCast
  have hden : 0 < 2 * (k : ℝ) - 3 := by linarith
  have hexp : (i : ℝ) ≤
      1 + janzerAlpha k * (2 * (i : ℝ) - 1) := by
    unfold janzerAlpha
    rw [div_mul_eq_mul_div]
    have hsub : (i : ℝ) - 1 ≤
        ((k : ℝ) - 2) * (2 * (i : ℝ) - 1) / (2 * k - 3) := by
      apply (le_div_iff₀ hden).2
      nlinarith
    linarith
  have hbase : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hnonneg : (0 : ℝ) ≤ N := hpos.le
  have hsubcast : ((2 * i - 1 : ℕ) : ℝ) = 2 * (i : ℝ) - 1 := by
    norm_num [Nat.cast_sub (by omega : 1 ≤ 2 * i)]
  calc
    (N : ℝ) ^ i = (N : ℝ) ^ (i : ℝ) := (Real.rpow_natCast _ i).symm
    _ ≤ (N : ℝ) ^ (1 + janzerAlpha k * (2 * (i : ℝ) - 1)) :=
      Real.rpow_le_rpow_of_exponent_le hbase hexp
    _ = (N : ℝ) *
        (N : ℝ) ^ (janzerAlpha k * (2 * (i : ℝ) - 1)) := by
      rw [Real.rpow_add hpos]
      rw [Real.rpow_one]
    _ = (N : ℝ) * ((N : ℝ) ^ janzerAlpha k) ^ (2 * i - 1) := by
      rw [← hsubcast, Real.rpow_mul hnonneg, Real.rpow_natCast]

/-! ## Codegrees and light/heavy pairs -/

section FiniteHost

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The common-neighbour finset of two vertices. -/
def commonNeighbors (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : Finset V :=
  G.neighborFinset u ∩ G.neighborFinset v

@[simp] theorem mem_commonNeighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v x : V) : x ∈ commonNeighbors G u v ↔ G.Adj u x ∧ G.Adj v x := by
  simp [commonNeighbors]

/-- The codegree of two vertices. -/
def codegree (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : ℕ :=
  (commonNeighbors G u v).card

theorem codegree_comm (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    codegree G u v = codegree G v u := by
  simp [codegree, commonNeighbors, Finset.inter_comm]

/-- Common neighbours of all branch vertices indexed by a two-element set. -/
def pairCommonNeighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (branch : Fin k → V) (p : CliquePair k) : Finset V :=
  Finset.univ.filter fun x ↦ ∀ i ∈ (p.1 : Finset (Fin k)), G.Adj (branch i) x

@[simp] theorem mem_pairCommonNeighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (branch : Fin k → V) (p : CliquePair k) (x : V) :
    x ∈ pairCommonNeighbors G branch p ↔
      ∀ i ∈ (p.1 : Finset (Fin k)), G.Adj (branch i) x := by
  simp [pairCommonNeighbors]

theorem pairCommonNeighbors_eq_commonNeighbors (G : SimpleGraph V)
    [DecidableRel G.Adj] {k : ℕ} (branch : Fin k → V) (p : CliquePair k)
    {i j : Fin k} (hp : (p.1 : Finset (Fin k)) = {i, j}) :
    pairCommonNeighbors G branch p = commonNeighbors G (branch i) (branch j) := by
  ext x
  simp [pairCommonNeighbors, commonNeighbors, hp, and_comm]

/-- If the common-neighbour sets belonging to distinct branch pairs are
nonempty, pairwise disjoint, and avoid the branch vertices, choosing one
point from every set gives the required subdivision copy. -/
theorem cliqueSubdivision_isContained_of_disjoint_pairCommon
    {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (branch : Fin k → V) (hbranch : Function.Injective branch)
    (hnonempty : ∀ p : CliquePair k,
      (pairCommonNeighbors G branch p).Nonempty)
    (hpairDisjoint : ∀ p q : CliquePair k, p ≠ q →
      Disjoint (pairCommonNeighbors G branch p)
        (pairCommonNeighbors G branch q))
    (havoid : ∀ (i : Fin k) (p : CliquePair k),
      branch i ∉ pairCommonNeighbors G branch p) :
    cliqueSubdivision k ⊑ G := by
  classical
  let middle : CliquePair k → V := fun p ↦ (hnonempty p).choose
  have hmiddle_mem (p : CliquePair k) :
      middle p ∈ pairCommonNeighbors G branch p := by
    exact Classical.choose_spec (hnonempty p)
  have hmiddle : Function.Injective middle := by
    intro p q hpq
    by_contra hpq'
    have hd := Finset.disjoint_left.mp (hpairDisjoint p q hpq')
    exact hd (hmiddle_mem p) (by simpa [hpq] using hmiddle_mem q)
  refine cliqueSubdivision_isContained_of_maps G branch middle hbranch hmiddle ?_ ?_
  · intro i p hip
    exact havoid i p (hip ▸ hmiddle_mem p)
  · intro i p hip
    exact (mem_pairCommonNeighbors G branch p (middle p)).mp
      (hmiddle_mem p) i hip

/-- A pair has at least one, but fewer than `r`, common neighbours. -/
def IsLight (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (u v : V) : Prop :=
  u ≠ v ∧ 0 < codegree G u v ∧ codegree G u v < r

/-- A pair has at least `r` common neighbours. -/
def IsHeavy (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (u v : V) : Prop :=
  u ≠ v ∧ r ≤ codegree G u v

theorem isLight_comm (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (u v : V) :
    IsLight G r u v ↔ IsLight G r v u := by
  constructor
  · rintro ⟨huv, hpos, hlt⟩
    exact ⟨huv.symm, by rwa [codegree_comm G], by rwa [codegree_comm G]⟩
  · rintro ⟨hvu, hpos, hlt⟩
    exact ⟨hvu.symm, by rwa [codegree_comm G], by rwa [codegree_comm G]⟩

/-- The three invariants required of the eventual branch map. -/
def IsIndependentBranchMap (G : SimpleGraph V) {k : ℕ}
    (branch : Fin k → V) : Prop :=
  ∀ i j, i ≠ j → ¬ G.Adj (branch i) (branch j)

def IsLightBranchMap (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) {k : ℕ} (branch : Fin k → V) : Prop :=
  ∀ i j, i ≠ j → IsLight G r (branch i) (branch j)

def HasNoTripleCommonNeighbor (G : SimpleGraph V) {k : ℕ}
    (branch : Fin k → V) : Prop :=
  ∀ i j l, i ≠ j → i ≠ l → j ≠ l → ∀ x,
    ¬ (G.Adj (branch i) x ∧ G.Adj (branch j) x ∧
      G.Adj (branch l) x)

/-- Independent, pairwise light branch vertices with no triple common
neighbour already form a copy of the one-subdivision. -/
theorem cliqueSubdivision_isContained_of_goodBranchMap
    {k r : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (branch : Fin k → V) (hbranch : Function.Injective branch)
    (hind : IsIndependentBranchMap G branch)
    (hlight : IsLightBranchMap G r branch)
    (htriple : HasNoTripleCommonNeighbor G branch) :
    cliqueSubdivision k ⊑ G := by
  classical
  apply cliqueSubdivision_isContained_of_disjoint_pairCommon G branch hbranch
  · intro p
    obtain ⟨i, j, hij, hp⟩ := Finset.card_eq_two.mp (Set.powersetCard.card_eq p)
    rw [pairCommonNeighbors_eq_commonNeighbors G branch p hp]
    exact Finset.card_pos.mp (by
      simpa [codegree] using (hlight i j hij).2.1)
  · intro p q hpq
    obtain ⟨i, j, hij, hp⟩ := Finset.card_eq_two.mp (Set.powersetCard.card_eq p)
    let P : Finset (Fin k) := p.1
    let Q : Finset (Fin k) := q.1
    have hPQ : P ≠ Q := by
      intro heq
      apply hpq
      apply Subtype.ext
      dsimp only [P, Q] at heq
      exact heq
    have hQnsubP : ¬ Q ⊆ P := by
      intro hsub
      have heq : Q = P := Finset.eq_of_subset_of_card_le hsub (by
        dsimp only [P, Q]
        rw [Set.powersetCard.card_eq p, Set.powersetCard.card_eq q])
      exact hPQ heq.symm
    obtain ⟨l, hlQ, hlP⟩ := Finset.not_subset.mp hQnsubP
    rw [Finset.disjoint_left]
    intro x hxp hxq
    have hiP : i ∈ P := by simp [P, hp]
    have hjP : j ∈ P := by simp [P, hp]
    have hil : i ≠ l := by
      intro hil
      apply hlP
      simpa [hil] using hiP
    have hjl : j ≠ l := by
      intro hjl
      apply hlP
      simpa [hjl] using hjP
    have hxi : G.Adj (branch i) x :=
      (mem_pairCommonNeighbors G branch p x).mp hxp i (by simpa [P] using hiP)
    have hxj : G.Adj (branch j) x :=
      (mem_pairCommonNeighbors G branch p x).mp hxp j (by simpa [P] using hjP)
    have hxl : G.Adj (branch l) x :=
      (mem_pairCommonNeighbors G branch q x).mp hxq l (by simpa [Q] using hlQ)
    exact htriple i j l hij hil hjl x ⟨hxi, hxj, hxl⟩
  · intro l p hlp
    obtain ⟨i, j, hij, hp⟩ := Finset.card_eq_two.mp (Set.powersetCard.card_eq p)
    have hli : G.Adj (branch i) (branch l) :=
      (mem_pairCommonNeighbors G branch p (branch l)).mp hlp i (by simp [hp])
    by_cases hil : i = l
    · subst l
      exact G.loopless.irrefl _ hli
    · exact hind i l hil hli

theorem isHeavy_comm (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (u v : V) :
    IsHeavy G r u v ↔ IsHeavy G r v u := by
  constructor
  · rintro ⟨huv, hle⟩
    exact ⟨huv.symm, by rwa [codegree_comm G]⟩
  · rintro ⟨hvu, hle⟩
    exact ⟨hvu.symm, by rwa [codegree_comm G]⟩

/-- The simple graph whose edges are the heavy pairs. -/
def heavyGraph (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) : SimpleGraph V where
  Adj := IsHeavy G r
  symm := by
    constructor
    intro u v h
    exact (isHeavy_comm G r u v).mp h
  loopless := by
    constructor
    intro u h
    exact h.1 rfl

instance heavyGraph.instDecidableAdj (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) :
    DecidableRel (heavyGraph G r).Adj := by
  intro u v
  dsimp only [heavyGraph, IsHeavy]
  infer_instance

/-- We reserve enough common neighbours to avoid all branch vertices and
still apply Hall to the `k.choose 2` internal vertices. -/
def subdivisionThreshold (k : ℕ) : ℕ := k + k.choose 2

/-- A `k`-clique in the heavy-pair graph gives a genuine subdivision copy.
The extra `k` in `subdivisionThreshold` lets Hall's representatives avoid the
branch vertices themselves. -/
theorem cliqueSubdivision_isContained_of_heavy_copy
    {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : SimpleGraph.Copy (SimpleGraph.completeGraph (Fin k))
      (heavyGraph G (subdivisionThreshold k))) :
    cliqueSubdivision k ⊑ G := by
  classical
  let branch : Fin k → V := f.toHom.toFun
  have hbranch : Function.Injective branch := f.injective'
  let branchVertices : Finset V := Finset.univ.image branch
  let candidates : CliquePair k → Finset V := fun p ↦
    pairCommonNeighbors G branch p \ branchVertices
  have hbranchVertices : branchVertices.card = k := by
    simp [branchVertices, Finset.card_image_of_injective _ hbranch]
  have hcandidates : ∀ p, k.choose 2 ≤ (candidates p).card := by
    intro p
    obtain ⟨i, j, hij, hp⟩ := Finset.card_eq_two.mp (Set.powersetCard.card_eq p)
    have hcomplete : (SimpleGraph.completeGraph (Fin k)).Adj i j := by
      simpa [SimpleGraph.completeGraph] using hij
    have hheavy : IsHeavy G (subdivisionThreshold k) (branch i) (branch j) :=
      f.toHom.map_rel' hcomplete
    have hcommon : subdivisionThreshold k ≤
        (pairCommonNeighbors G branch p).card := by
      rw [pairCommonNeighbors_eq_commonNeighbors G branch p hp]
      exact hheavy.2
    have hdiff := Finset.le_card_sdiff branchVertices
      (pairCommonNeighbors G branch p)
    dsimp only [candidates]
    dsimp only [subdivisionThreshold] at hcommon
    omega
  have hHall : ∀ s : Finset (CliquePair k),
      s.card ≤ (s.biUnion candidates).card := by
    intro s
    by_cases hs : s = ∅
    · simp [hs]
    · obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hs
      have hsub : candidates p ⊆ s.biUnion candidates := by
        intro x hx
        exact Finset.mem_biUnion.mpr ⟨p, hp, hx⟩
      calc
        s.card ≤ Fintype.card (CliquePair k) := Finset.card_le_univ s
        _ = k.choose 2 := card_cliquePair k
        _ ≤ (candidates p).card := hcandidates p
        _ ≤ (s.biUnion candidates).card := Finset.card_le_card hsub
  obtain ⟨middle, hmiddle, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' candidates).mp hHall
  refine cliqueSubdivision_isContained_of_maps G branch middle hbranch hmiddle ?_ ?_
  · intro i p hip
    have hbi : branch i ∈ branchVertices := by
      simp [branchVertices]
    have hnot : middle p ∉ branchVertices :=
      (Finset.mem_sdiff.mp (hmem p)).2
    apply hnot
    rw [← hip]
    exact hbi
  · intro i p hip
    exact (mem_pairCommonNeighbors G branch p (middle p)).mp
      (Finset.mem_sdiff.mp (hmem p)).1 i hip

theorem heavyGraph_cliqueFree_of_free
    {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : (cliqueSubdivision k).Free G) :
    (heavyGraph G (subdivisionThreshold k)).CliqueFree k := by
  rw [SimpleGraph.cliqueFree_iff]
  constructor
  intro f
  exact hfree (cliqueSubdivision_isContained_of_heavy_copy G f)

/-! ## The quantitative light-pair count -/

/-- Ordered pairs of distinct vertices that are not edges of a graph. -/
def orderedNonedges (H : SimpleGraph V) [DecidableRel H.Adj] : Finset (V × V) :=
  (Finset.univ.offDiag).filter fun e ↦ ¬ H.Adj e.1 e.2

/-- A convenient cross-multiplied consequence of Turán's theorem: if a
`K_k`-free graph has at least `2(k-1)` vertices, a definite fraction of its
ordered pairs are nonedges. -/
theorem sq_card_le_orderedNonedges
    {k : ℕ} (hk : 3 ≤ k) (H : SimpleGraph V) [DecidableRel H.Adj]
    (hfree : H.CliqueFree k)
    (hcard : 2 * (k - 1) ≤ Fintype.card V) :
    (Fintype.card V) ^ 2 ≤
      2 * (k - 1) * (orderedNonedges H).card := by
  classical
  let n := Fintype.card V
  let r := k - 1
  have hr : 0 < r := by dsimp [r]; omega
  have hkr : r + 1 = k := by dsimp [r]; omega
  have hfree' : H.CliqueFree (r + 1) := by simpa [hkr] using hfree
  have hedge : H.edgeFinset.card ≤
      (SimpleGraph.turanGraph n r).edgeFinset.card := by
    simpa [SimpleGraph.card_edgeFinset_turanGraph] using
      (SimpleGraph.CliqueFree.card_edgeFinset_le hfree')
  have hturan := SimpleGraph.mul_card_edgeFinset_turanGraph_le (n := n) (r := r)
  have hadj :
      (Finset.univ.filter fun e : V × V ↦ H.Adj e.1 e.2).card =
        2 * H.edgeFinset.card := H.two_mul_card_edgeFinset.symm
  have hadjOff :
      ((Finset.univ : Finset V).offDiag.filter fun e ↦ H.Adj e.1 e.2).card =
        2 * H.edgeFinset.card := by
    rw [← hadj]
    congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_offDiag]
    by_cases he : H.Adj e.1 e.2
    · simp [he, H.ne_of_adj he]
    · simp [he]
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset V).offDiag)
    (p := fun e ↦ H.Adj e.1 e.2)
  have hoffcard : ((Finset.univ : Finset V).offDiag).card = n ^ 2 - n := by
    simp [Finset.offDiag_card, n, pow_two]
  have hn : 0 < n := by dsimp [n, r] at hcard ⊢; omega
  have htotal :
      2 * H.edgeFinset.card + (orderedNonedges H).card + n = n ^ 2 := by
    simp only [orderedNonedges]
    rw [← hadjOff, hpartition]
    rw [hoffcard, Nat.sub_add_cancel]
    nlinarith
  have hheavy : r * (2 * H.edgeFinset.card) ≤ (r - 1) * n ^ 2 := by
    calc
      r * (2 * H.edgeFinset.card) = 2 * r * H.edgeFinset.card := by ring
      _ ≤ 2 * r * (SimpleGraph.turanGraph n r).edgeFinset.card := by
        gcongr
      _ ≤ (r - 1) * n ^ 2 := hturan
  change 2 * r ≤ n at hcard
  change n ^ 2 ≤ 2 * r * (orderedNonedges H).card
  have hrpred : r - 1 + 1 = r := by omega
  nlinarith

/-- Neighbours of `x` that lie in a prescribed candidate set. -/
def neighborsIn (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (x : V) : Finset V :=
  U.filter fun u ↦ G.Adj u x

@[simp] theorem mem_neighborsIn (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (x u : V) :
    u ∈ neighborsIn G U x ↔ u ∈ U ∧ G.Adj u x := by
  simp [neighborsIn]

/-- Ordered light pairs inside `N(x) ∩ U`, retaining the subtype witnesses so
that Turán's theorem applies without a cardinality transport. -/
noncomputable def localLightPairs (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (U : Finset V) (x : V) :
    Finset (↥(neighborsIn G U x) × ↥(neighborsIn G U x)) :=
  Finset.univ.filter fun e ↦ IsLight G r e.1.1 e.2.1

/-- Turán applied in one common neighbourhood.  A nonedge of the induced
heavy graph is exactly a light pair because `x` witnesses positive codegree. -/
theorem sq_neighborsIn_card_le_localLightPairs
    {k : ℕ} (hk : 3 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : (cliqueSubdivision k).Free G) (U : Finset V) (x : V)
    (hlarge : 2 * (k - 1) ≤ (neighborsIn G U x).card) :
    (neighborsIn G U x).card ^ 2 ≤
      2 * (k - 1) *
        (localLightPairs G (subdivisionThreshold k) U x).card := by
  classical
  let S := neighborsIn G U x
  let K := (heavyGraph G (subdivisionThreshold k)).induce (↑S : Set V)
  let eS : ↥(↑S : Set V) ≃ ↥S :=
    { toFun := fun v ↦ ⟨v.1, v.2⟩
      invFun := fun v ↦ ⟨v.1, v.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hScard : Fintype.card ↥(↑S : Set V) = S.card := by
    rw [Fintype.card_congr eS, Fintype.card_coe]
  have hKfree : K.CliqueFree k := by
    rw [SimpleGraph.cliqueFree_induce_iff]
    exact (heavyGraph_cliqueFree_of_free G hfree).cliqueFreeOn
  have hKcard : 2 * (k - 1) ≤ Fintype.card ↥(↑S : Set V) := by
    rw [hScard]
    simpa [S] using hlarge
  have ht := sq_card_le_orderedNonedges hk K hKfree hKcard
  have heq : orderedNonedges K =
      localLightPairs G (subdivisionThreshold k) U x := by
    ext e
    rcases e with ⟨a, b⟩
    have hapos : 0 < codegree G a.1 b.1 := by
      rw [codegree, Finset.card_pos]
      refine ⟨x, ?_⟩
      rw [mem_commonNeighbors]
      exact ⟨(mem_neighborsIn G U x a.1).mp a.2 |>.2,
        (mem_neighborsIn G U x b.1).mp b.2 |>.2⟩
    simp only [orderedNonedges, localLightPairs, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_offDiag]
    change (a ≠ b ∧ ¬ IsHeavy G (subdivisionThreshold k) a.1 b.1) ↔
      IsLight G (subdivisionThreshold k) a.1 b.1
    constructor
    · rintro ⟨hab, hnot⟩
      have hab' : a.1 ≠ b.1 := by
        intro h
        exact hab (Subtype.ext h)
      exact ⟨hab', hapos, Nat.lt_of_not_ge (fun hle ↦ hnot ⟨hab', hle⟩)⟩
    · rintro ⟨hab, _, hlt⟩
      refine ⟨fun h ↦ hab (congrArg Subtype.val h), ?_⟩
      exact fun hheavy ↦ (Nat.not_le_of_lt hlt) hheavy.2
  rw [← heq]
  rw [hScard] at ht
  simpa [S, K] using ht

/-- Ordered light pairs contained in `U`. -/
noncomputable def lightPairsOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (U : Finset V) : Finset (↥U × ↥U) :=
  Finset.univ.filter fun e ↦ IsLight G r e.1.1 e.2.1

/-- Light neighbours of `u` that lie in `U`. -/
noncomputable def lightNeighborsOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (U : Finset V) (u : V) : Finset V :=
  U.filter fun v ↦ IsLight G r u v

@[simp] theorem mem_lightNeighborsOn (G : SimpleGraph V)
    [DecidableRel G.Adj] (r : ℕ) (U : Finset V) (u v : V) :
    v ∈ lightNeighborsOn G r U u ↔ v ∈ U ∧ IsLight G r u v := by
  simp [lightNeighborsOn]

/-- Both orientations are retained, so the sum of the restricted light
degrees is exactly the cardinality of `lightPairsOn`. -/
theorem sum_lightNeighborsOn_card (G : SimpleGraph V)
    [DecidableRel G.Adj] (r : ℕ) (U : Finset V) :
    (∑ u : ↥U, (lightNeighborsOn G r U u.1).card) =
      (lightPairsOn G r U).card := by
  classical
  let A := Σ u : ↥U, ↥(lightNeighborsOn G r U u.1)
  let B := ↥(lightPairsOn G r U)
  let e : A ≃ B :=
    { toFun := fun z ↦ by
        rcases z with ⟨u, ⟨v, hv⟩⟩
        refine ⟨(u, ⟨v, (mem_lightNeighborsOn G r U u.1 v).mp hv |>.1⟩), ?_⟩
        simpa [lightPairsOn] using
          (mem_lightNeighborsOn G r U u.1 v).mp hv |>.2
      invFun := fun z ↦ by
        rcases z with ⟨⟨u, v⟩, huv⟩
        refine ⟨u, ⟨v.1, ?_⟩⟩
        exact (mem_lightNeighborsOn G r U u.1 v.1).mpr ⟨v.2, by
          simpa [lightPairsOn] using huv⟩
      left_inv := by
        rintro ⟨u, ⟨v, hv⟩⟩
        rfl
      right_inv := by
        rintro ⟨⟨u, v⟩, huv⟩
        rfl }
  have hcard := Fintype.card_congr e
  simp only [A, B, Fintype.card_sigma, Fintype.card_coe] at hcard
  exact hcard

/-- The number of light-pair/common-neighbour incidences, grouped by the
light pair. -/
noncomputable def lightIncidenceWeight (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (U : Finset V) : ℕ :=
  ∑ p : ↥(lightPairsOn G r U), codegree G p.1.1.1 p.1.2.1

theorem sum_localLightPairs_eq_lightIncidenceWeight
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (U : Finset V) :
    (∑ x : V, (localLightPairs G r U x).card) =
      lightIncidenceWeight G r U := by
  classical
  have hcommonCard (u v : V) :
      Fintype.card {x : V // G.Adj u x ∧ G.Adj v x} =
        (commonNeighbors G u v).card := by
    let e : {x : V // G.Adj u x ∧ G.Adj v x} ≃
        ↥(commonNeighbors G u v) :=
      { toFun := fun x ↦ ⟨x.1, (mem_commonNeighbors G u v x.1).mpr x.2⟩
        invFun := fun x ↦ ⟨x.1, (mem_commonNeighbors G u v x.1).mp x.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    rw [Fintype.card_congr e, Fintype.card_coe]
  let A := Σ x : V, ↥(localLightPairs G r U x)
  let B := Σ p : ↥(lightPairsOn G r U),
    ↥(commonNeighbors G p.1.1.1 p.1.2.1)
  let e : A ≃ B :=
    { toFun := fun z ↦ by
        rcases z with ⟨x, ⟨p, hp⟩⟩
        rcases p with ⟨a, b⟩
        let u : ↥U := ⟨a.1, (mem_neighborsIn G U x a.1).mp a.2 |>.1⟩
        let v : ↥U := ⟨b.1, (mem_neighborsIn G U x b.1).mp b.2 |>.1⟩
        have hpLight : IsLight G r u.1 v.1 := by
          simpa [localLightPairs, u, v] using hp
        let q : ↥(lightPairsOn G r U) := ⟨(u, v), by
          simp [lightPairsOn, hpLight]⟩
        refine ⟨q, ⟨x, ?_⟩⟩
        rw [mem_commonNeighbors]
        exact ⟨(mem_neighborsIn G U x a.1).mp a.2 |>.2,
          (mem_neighborsIn G U x b.1).mp b.2 |>.2⟩
      invFun := fun z ↦ by
        rcases z with ⟨⟨p, hp⟩, ⟨x, hx⟩⟩
        rcases p with ⟨u, v⟩
        have hx' := (mem_commonNeighbors G u.1 v.1 x).mp hx
        let a : ↥(neighborsIn G U x) := ⟨u.1,
          (mem_neighborsIn G U x u.1).mpr ⟨u.2, hx'.1⟩⟩
        let b : ↥(neighborsIn G U x) := ⟨v.1,
          (mem_neighborsIn G U x v.1).mpr ⟨v.2, hx'.2⟩⟩
        refine ⟨x, ⟨(a, b), ?_⟩⟩
        simpa [localLightPairs, lightPairsOn, a, b] using hp
      left_inv := by
        rintro ⟨x, ⟨⟨a, b⟩, hp⟩⟩
        rfl
      right_inv := by
        rintro ⟨⟨⟨u, v⟩, hp⟩, ⟨x, hx⟩⟩
        rfl }
  have hcard := Fintype.card_congr e
  simp only [A, B, Fintype.card_sigma, Fintype.card_coe] at hcard
  simpa [lightIncidenceWeight, codegree] using hcard

theorem lightIncidenceWeight_le
    (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ} (U : Finset V) :
    lightIncidenceWeight G r U ≤
      (r - 1) * (lightPairsOn G r U).card := by
  classical
  unfold lightIncidenceWeight
  calc
    (∑ p : ↥(lightPairsOn G r U), codegree G p.1.1.1 p.1.2.1) ≤
        ∑ _p : ↥(lightPairsOn G r U), (r - 1) := by
      apply Finset.sum_le_sum
      intro p hp
      have hlight : IsLight G r p.1.1.1 p.1.2.1 := by
        simpa [lightPairsOn] using p.2
      exact Nat.le_sub_one_of_lt hlight.2.2
    _ = (r - 1) * (lightPairsOn G r U).card := by
      simp [mul_comm]

theorem sum_neighborsIn_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) :
    (∑ x : V, (neighborsIn G U x).card) = ∑ u ∈ U, G.degree u := by
  classical
  have h := Finset.sum_comm (s := (Finset.univ : Finset V)) (t := U)
    (f := fun x u ↦ if G.Adj u x then 1 else 0)
  calc
    (∑ x : V, (neighborsIn G U x).card) =
        ∑ x : V, ∑ u ∈ U, if G.Adj u x then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      change (U.filter fun u ↦ G.Adj u x).card =
        ∑ u ∈ U, if G.Adj u x then 1 else 0
      exact Finset.natCast_card_filter _ _
    _ = ∑ u ∈ U, ∑ x : V, if G.Adj u x then 1 else 0 := h
    _ = ∑ u ∈ U, G.degree u := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
      change (∑ x : V, if G.Adj u x then 1 else 0) =
        ((Finset.univ : Finset V).filter fun x ↦ G.Adj u x).card
      exact (Finset.natCast_card_filter (R := ℕ)
        (fun x : V ↦ G.Adj u x) Finset.univ).symm

/-- The number of oriented incidences from `A` to `B`. -/
def crossIncidence (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : ℕ :=
  ∑ x ∈ B, (neighborsIn G A x).card

/-- Oriented incidences inject into darts of the graph retaining edges
between the two indicated sets.  The factor two is the handshaking identity. -/
theorem crossIncidence_le_twice_between_edges
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    crossIncidence G A B ≤
      2 * (G.between (A : Set V) (B : Set V)).edgeFinset.card := by
  classical
  let J := G.between (A : Set V) (B : Set V)
  have hpoint : ∀ x ∈ B, (neighborsIn G A x).card ≤ J.degree x := by
    intro x hx
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro a ha
    have ha' := (mem_neighborsIn G A x a).mp ha
    rw [J.mem_neighborFinset, SimpleGraph.between_adj]
    exact ⟨ha'.2.symm, Or.inr ⟨hx, ha'.1⟩⟩
  calc
    crossIncidence G A B ≤ ∑ x ∈ B, J.degree x := by
      exact Finset.sum_le_sum hpoint
    _ ≤ ∑ x : V, J.degree x :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ B)
    _ = 2 * J.edgeFinset.card := J.sum_degrees_eq_twice_card_edges

/-- Summing oriented incidences over all parts of a finite partition counts
every edge-end at a vertex of `A` exactly once. -/
theorem sum_crossIncidence_parts
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    (P : Finpartition (Finset.univ : Finset V)) :
    (∑ B ∈ P.parts, crossIncidence G A B) = ∑ a ∈ A, G.degree a := by
  classical
  rw [show (∑ B ∈ P.parts, crossIncidence G A B) =
      ∑ B ∈ P.parts, ∑ x ∈ B, (neighborsIn G A x).card by
        simp [crossIncidence]]
  have hparts := Finset.sum_biUnion
    (f := fun x : V ↦ (neighborsIn G A x).card) P.disjoint
  rw [P.biUnion_parts] at hparts
  calc
    (∑ B ∈ P.parts, ∑ x ∈ B, (neighborsIn G A x).card) =
        ∑ x : V, (neighborsIn G A x).card := hparts.symm
    _ = ∑ a ∈ A, G.degree a := sum_neighborsIn_card G A

theorem sum_crossIncidence_support_parts
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    (P : Finpartition G.support.toFinset) :
    (∑ B ∈ P.parts, crossIncidence G A B) = ∑ a ∈ A, G.degree a := by
  classical
  have hparts := Finset.sum_biUnion
    (f := fun x : V ↦ (neighborsIn G A x).card) P.disjoint
  rw [P.biUnion_parts] at hparts
  have hsupp : (∑ x ∈ G.support.toFinset, (neighborsIn G A x).card) =
      ∑ x : V, (neighborsIn G A x).card := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x hxuniv hx
    have hxnot : x ∉ G.support := by simpa using hx
    rw [Finset.card_eq_zero]
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hne
    obtain ⟨a, ha⟩ := hne
    have hadj := (mem_neighborsIn G A x a).mp ha |>.2
    exact hxnot (G.mem_support.mpr ⟨a, hadj.symm⟩)
  calc
    (∑ B ∈ P.parts, crossIncidence G A B) =
        ∑ B ∈ P.parts, ∑ x ∈ B, (neighborsIn G A x).card := by
          simp [crossIncidence]
    _ = ∑ x ∈ G.support.toFinset, (neighborsIn G A x).card := hparts.symm
    _ = ∑ x : V, (neighborsIn G A x).card := hsupp
    _ = ∑ a ∈ A, G.degree a := sum_neighborsIn_card G A

/-- Edges having at least one endpoint in a specified finite set. -/
def edgesMeeting (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e ↦ ∃ v ∈ e.toFinset, v ∈ A

@[simp] theorem mem_edgesMeeting (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V)
    (e : Sym2 V) :
    e ∈ edgesMeeting G A ↔
      e ∈ G.edgeFinset ∧ ∃ v ∈ e.toFinset, v ∈ A := by
  simp [edgesMeeting]

theorem card_edgesMeeting_le_sum_degree
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) :
    (edgesMeeting G A).card ≤ ∑ v ∈ A, G.degree v := by
  classical
  have hsub : edgesMeeting G A ⊆
      A.biUnion fun v ↦ G.incidenceFinset v := by
    intro e he
    obtain ⟨heG, v, hve, hvA⟩ := mem_edgesMeeting G A e |>.mp he
    apply Finset.mem_biUnion.mpr
    refine ⟨v, hvA, ?_⟩
    rw [SimpleGraph.mem_incidenceFinset]
    exact ⟨SimpleGraph.mem_edgeFinset.mp heG, by simpa using hve⟩
  calc
    (edgesMeeting G A).card ≤
        (A.biUnion fun v ↦ G.incidenceFinset v).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ v ∈ A, (G.incidenceFinset v).card := Finset.card_biUnion_le
    _ = ∑ v ∈ A, G.degree v := by simp

/-- Deleting all vertices of `A` loses at most the sum of their degrees. -/
theorem edge_count_le_induce_compl_add_degree_sum
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) :
    G.edgeFinset.card ≤ (G.induce (↑Aᶜ : Set V)).edgeFinset.card +
      ∑ v ∈ A, G.degree v := by
  classical
  let inside := {e ∈ G.edgeFinset | e.toFinset ⊆ Aᶜ}
  let outside := G.edgeFinset \ inside
  have hinside : inside ⊆ G.edgeFinset := by
    intro e he
    exact (Finset.mem_filter.mp he).1
  have houtside : outside ⊆ edgesMeeting G A := by
    intro e he
    have he' := Finset.mem_sdiff.mp he
    have hnsub : ¬ e.toFinset ⊆ Aᶜ := by
      intro hsub
      exact he'.2 (Finset.mem_filter.mpr ⟨he'.1, hsub⟩)
    rw [Finset.not_subset] at hnsub
    obtain ⟨v, hve, hv⟩ := hnsub
    apply mem_edgesMeeting G A e |>.mpr
    exact ⟨he'.1, v, hve, by simpa using hv⟩
  have houtsideCard : outside.card ≤ ∑ v ∈ A, G.degree v :=
    (Finset.card_le_card houtside).trans (card_edgesMeeting_le_sum_degree G A)
  have hdecomp : outside.card + inside.card = G.edgeFinset.card := by
    simpa [outside] using Finset.card_sdiff_add_card_eq_card hinside
  have hinsideCard : inside.card = (G.induce (↑Aᶜ : Set V)).edgeFinset.card := by
    simpa [inside] using G.card_filter_edgeFinset_toFinset_subset Aᶜ
  omega

theorem edge_count_le_deleteEdgesMeeting_add_degree_sum
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) :
    G.edgeFinset.card ≤
      (G.deleteEdges (edgesMeeting G A : Set (Sym2 V))).edgeFinset.card +
        ∑ v ∈ A, G.degree v := by
  classical
  let M := edgesMeeting G A
  have hM : M ⊆ G.edgeFinset := by
    intro e he
    exact (mem_edgesMeeting G A e).mp he |>.1
  have hcardM : M.card ≤ ∑ v ∈ A, G.degree v :=
    card_edgesMeeting_le_sum_degree G A
  have hdecomp : (G.edgeFinset \ M).card + M.card = G.edgeFinset.card :=
    Finset.card_sdiff_add_card_eq_card hM
  have hdelete :
      (G.deleteEdges (M : Set (Sym2 V))).edgeFinset = G.edgeFinset \ M := by
    simpa using G.edgeFinset_deleteEdges M
  rw [hdelete]
  omega

theorem support_deleteEdgesMeeting_not_mem
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    {v : V} (hv : v ∈ (G.deleteEdges
      (edgesMeeting G A : Set (Sym2 V))).support) : v ∉ A := by
  classical
  intro hvA
  obtain ⟨w, hvw⟩ := (G.deleteEdges
    (edgesMeeting G A : Set (Sym2 V))).mem_support.mp hv
  have hnot := (SimpleGraph.deleteEdges_adj.mp hvw).2
  apply hnot
  apply mem_edgesMeeting G A s(v, w) |>.mpr
  exact ⟨SimpleGraph.mem_edgeFinset.mpr (SimpleGraph.deleteEdges_adj.mp hvw).1,
    ⟨v, by simp, hvA⟩⟩

/-- Centers whose restricted neighbourhood is large enough for the local
Turán estimate. -/
def goodCenters (k : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) : Finset V :=
  Finset.univ.filter fun x ↦ 2 * (k - 1) ≤ (neighborsIn G U x).card

@[simp] theorem mem_goodCenters (k : ℕ) (G : SimpleGraph V)
    [DecidableRel G.Adj] (U : Finset V) (x : V) :
    x ∈ goodCenters k G U ↔ 2 * (k - 1) ≤ (neighborsIn G U x).card := by
  simp [goodCenters]

/-- Janzer's many-light-pairs estimate in a division-free ordered-pair form. -/
theorem many_light_pairs
    {k δ : ℕ} (hk : 3 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : (cliqueSubdivision k).Free G)
    (hmin : ∀ v, δ ≤ G.degree v) (U : Finset V)
    (hsize : 4 * k * Fintype.card V ≤ δ * U.card) :
    (δ * U.card) ^ 2 ≤
      4 * (k - 1) * (subdivisionThreshold k - 1) * Fintype.card V *
        (lightPairsOn G (subdivisionThreshold k) U).card := by
  classical
  let n := Fintype.card V
  let t := 2 * (k - 1)
  let d : V → ℕ := fun x ↦ (neighborsIn G U x).card
  let Good := goodCenters k G U
  let Bad := (Finset.univ : Finset V) \ Good
  let goodSum := ∑ x ∈ Good, d x ^ 2
  let badSum := ∑ x ∈ Bad, d x ^ 2
  let allSum := ∑ x : V, d x ^ 2
  have hsumLower : δ * U.card ≤ ∑ x : V, d x := by
    calc
      δ * U.card = ∑ _u ∈ U, δ := by simp [Nat.mul_comm]
      _ ≤ ∑ u ∈ U, G.degree u := by
        apply Finset.sum_le_sum
        intro u hu
        exact hmin u
      _ = ∑ x : V, d x := by
        simpa [d] using (sum_neighborsIn_card G U).symm
  have hcs : (∑ x : V, d x) ^ 2 ≤ n * allSum := by
    simpa [n, allSum] using
      (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset V)) (f := d))
  have hlower : (δ * U.card) ^ 2 ≤ n * allSum := by
    exact (Nat.pow_le_pow_left hsumLower 2).trans hcs
  have hpartition : goodSum + badSum = allSum := by
    dsimp only [goodSum, badSum, allSum, Bad]
    rw [← Finset.sum_union]
    · congr 1
      exact Finset.union_sdiff_of_subset (Finset.subset_univ Good)
    · exact Finset.disjoint_sdiff
  have hbadPoint : ∀ x ∈ Bad, d x ^ 2 ≤ t ^ 2 := by
    intro x hx
    have hxnot : x ∉ Good := (Finset.mem_sdiff.mp hx).2
    have hlt : d x < t := by
      simpa [Good, goodCenters, d, t] using hxnot
    exact Nat.pow_le_pow_left hlt.le 2
  have hbad : badSum ≤ n * t ^ 2 := by
    calc
      badSum ≤ ∑ _x ∈ Bad, t ^ 2 := by
        apply Finset.sum_le_sum
        exact hbadPoint
      _ = Bad.card * t ^ 2 := by simp
      _ ≤ n * t ^ 2 := by
        gcongr
        exact Finset.card_le_univ Bad
  have hsize' : 2 * t * n ≤ δ * U.card := by
    calc
      2 * t * n = 4 * (k - 1) * n := by
        dsimp only [t]
        ring
      _ ≤ 4 * k * n := by
        exact Nat.mul_le_mul (Nat.mul_le_mul_left 4 (Nat.sub_le k 1)) le_rfl
      _ ≤ δ * U.card := hsize
  have hbadA : 4 * n * badSum ≤ (δ * U.card) ^ 2 := by
    calc
      4 * n * badSum ≤ 4 * n * (n * t ^ 2) := by gcongr
      _ = (2 * t * n) ^ 2 := by ring
      _ ≤ (δ * U.card) ^ 2 := Nat.pow_le_pow_left hsize' 2
  have hlower' : (δ * U.card) ^ 2 ≤ n * goodSum + n * badSum := by
    calc
      (δ * U.card) ^ 2 ≤ n * allSum := hlower
      _ = n * goodSum + n * badSum := by rw [← hpartition]; ring
  have hbadA' : 4 * (n * badSum) ≤ (δ * U.card) ^ 2 := by
    simpa [mul_assoc] using hbadA
  have hgoodLower' : (δ * U.card) ^ 2 ≤ 2 * (n * goodSum) := by
    omega
  have hgoodLower : (δ * U.card) ^ 2 ≤ 2 * n * goodSum := by
    simpa [mul_assoc] using hgoodLower'
  have hgoodLocal : goodSum ≤
      2 * (k - 1) * ∑ x : V,
        (localLightPairs G (subdivisionThreshold k) U x).card := by
    calc
      goodSum ≤ ∑ x ∈ Good,
          2 * (k - 1) *
            (localLightPairs G (subdivisionThreshold k) U x).card := by
        apply Finset.sum_le_sum
        intro x hx
        apply sq_neighborsIn_card_le_localLightPairs hk G hfree U x
        exact (mem_goodCenters k G U x).mp hx
      _ ≤ ∑ x : V,
          2 * (k - 1) *
            (localLightPairs G (subdivisionThreshold k) U x).card := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Good)
          (fun _ _ _ ↦ by positivity)
      _ = 2 * (k - 1) * ∑ x : V,
          (localLightPairs G (subdivisionThreshold k) U x).card := by
        rw [Finset.mul_sum]
  have hincidence : (δ * U.card) ^ 2 ≤
      4 * (k - 1) * n *
        lightIncidenceWeight G (subdivisionThreshold k) U := by
    rw [sum_localLightPairs_eq_lightIncidenceWeight] at hgoodLocal
    calc
      (δ * U.card) ^ 2 ≤ 2 * n * goodSum := hgoodLower
      _ ≤ 2 * n * (2 * (k - 1) *
          lightIncidenceWeight G (subdivisionThreshold k) U) := by gcongr
      _ = 4 * (k - 1) * n *
          lightIncidenceWeight G (subdivisionThreshold k) U := by ring
  have hweight := lightIncidenceWeight_le G
    (r := subdivisionThreshold k) U
  calc
    (δ * U.card) ^ 2 ≤ 4 * (k - 1) * n *
        lightIncidenceWeight G (subdivisionThreshold k) U := hincidence
    _ ≤ 4 * (k - 1) * n * ((subdivisionThreshold k - 1) *
        (lightPairsOn G (subdivisionThreshold k) U).card) := by gcongr
    _ = 4 * (k - 1) * (subdivisionThreshold k - 1) * Fintype.card V *
        (lightPairsOn G (subdivisionThreshold k) U).card := by simp [n]; ring

/-- Averaging the ordered light-pair estimate produces a vertex with many
light neighbours in the current candidate set.  The statement is kept
division-free for later iteration. -/
theorem exists_many_lightNeighbors
    {k δ : ℕ} (hk : 3 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : (cliqueSubdivision k).Free G)
    (hmin : ∀ v, δ ≤ G.degree v) (U : Finset V) (hU : U.Nonempty)
    (hsize : 4 * k * Fintype.card V ≤ δ * U.card) :
    ∃ u ∈ U, δ ^ 2 * U.card ≤
      (4 * (k - 1) * (subdivisionThreshold k - 1) * Fintype.card V) *
        (lightNeighborsOn G (subdivisionThreshold k) U u).card := by
  classical
  let f : ↥U → ℕ := fun u ↦
    (lightNeighborsOn G (subdivisionThreshold k) U u.1).card
  have hUcard : 0 < U.card := Finset.card_pos.mpr hU
  obtain ⟨u₀, hu₀⟩ := hU
  let u₀' : ↥U := ⟨u₀, hu₀⟩
  have huniv : (Finset.univ : Finset ↥U).Nonempty :=
    ⟨u₀', Finset.mem_univ u₀'⟩
  obtain ⟨u, _hu, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset ↥U) f huniv
  refine ⟨u.1, u.2, ?_⟩
  let A := 4 * (k - 1) * (subdivisionThreshold k - 1) * Fintype.card V
  have hsum : (lightPairsOn G (subdivisionThreshold k) U).card ≤
      U.card * f u := by
    rw [← sum_lightNeighborsOn_card]
    calc
      (∑ v : ↥U, f v) ≤ ∑ _v : ↥U, f u := by
        apply Finset.sum_le_sum
        intro v hv
        exact hmax v (Finset.mem_univ v)
      _ = U.card * f u := by simp
  have hmany := many_light_pairs hk G hfree hmin U hsize
  have hchain : (δ * U.card) ^ 2 ≤ A * (U.card * f u) := by
    exact hmany.trans (Nat.mul_le_mul_left A hsum)
  have hfactor : (δ ^ 2 * U.card) * U.card ≤
      (A * f u) * U.card := by
    calc
      (δ ^ 2 * U.card) * U.card = (δ * U.card) ^ 2 := by ring
      _ ≤ A * (U.card * f u) := hchain
      _ = (A * f u) * U.card := by ring
  have havg : δ ^ 2 * U.card ≤ A * f u :=
    Nat.le_of_mul_le_mul_right hfactor hUcard
  simpa [A, f] using havg

/-! ## Forbidden vertices for the greedy embedding -/

/-- Vertices adjacent to one of the already chosen branch vertices. -/
noncomputable def ordinaryBranchForbidden (G : SimpleGraph V)
    [DecidableRel G.Adj] {i : ℕ} (branch : Fin i → V) : Finset V :=
  (Finset.univ : Finset (Fin i)).biUnion fun j ↦ G.neighborFinset (branch j)

/-- Vertices adjacent to a common neighbour of an already chosen branch
pair.  Removing these is what preserves the no-triple invariant. -/
noncomputable def tripleBranchForbidden (G : SimpleGraph V)
    [DecidableRel G.Adj] {i : ℕ} (branch : Fin i → V) : Finset V :=
  (Finset.univ : Finset (CliquePair i)).biUnion fun p ↦
    (pairCommonNeighbors G branch p).biUnion fun x ↦ G.neighborFinset x

noncomputable def branchForbidden (G : SimpleGraph V)
    [DecidableRel G.Adj] {i : ℕ} (branch : Fin i → V) : Finset V :=
  ordinaryBranchForbidden G branch ∪ tripleBranchForbidden G branch

noncomputable def safeBranchCandidates (G : SimpleGraph V)
    [DecidableRel G.Adj] {i : ℕ} (branch : Fin i → V)
    (U : Finset V) : Finset V :=
  U \ branchForbidden G branch

theorem mem_safeBranchCandidates (G : SimpleGraph V)
    [DecidableRel G.Adj] {i : ℕ} (branch : Fin i → V)
    (U : Finset V) (v : V) :
    v ∈ safeBranchCandidates G branch U ↔
      v ∈ U ∧ (∀ j, ¬ G.Adj (branch j) v) ∧
        (∀ (p : CliquePair i) (x : V),
          x ∈ pairCommonNeighbors G branch p → ¬ G.Adj x v) := by
  classical
  simp only [safeBranchCandidates, branchForbidden, Finset.mem_sdiff,
    Finset.mem_union, not_or, ordinaryBranchForbidden,
    tripleBranchForbidden, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hvU, hord, htriple⟩
    refine ⟨hvU, ?_, ?_⟩
    · intro j hj
      exact hord ⟨j, by simpa using hj⟩
    · intro p x hxp hxv
      exact htriple ⟨p, x, hxp, by simpa using hxv⟩
  · rintro ⟨hvU, hord, htriple⟩
    refine ⟨hvU, ?_, ?_⟩
    · rintro ⟨j, hj⟩
      exact hord j (by simpa using hj)
    · rintro ⟨p, x, hxp, hxv⟩
      exact htriple p x hxp (by simpa using hxv)

/-- In a graph of maximum degree at most `Δ`, the two families of
forbidden vertices have the expected union-bound size. -/
theorem card_branchForbidden_le
    {i r Δ : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (branch : Fin i → V) (hmax : ∀ v, G.degree v ≤ Δ)
    (hlight : IsLightBranchMap G r branch) :
    (branchForbidden G branch).card ≤
      (i + i.choose 2 * (r - 1)) * Δ := by
  classical
  have hord : (ordinaryBranchForbidden G branch).card ≤ i * Δ := by
    calc
      (ordinaryBranchForbidden G branch).card ≤
          ∑ j : Fin i, (G.neighborFinset (branch j)).card := by
        exact Finset.card_biUnion_le
      _ ≤ ∑ _j : Fin i, Δ := by
        apply Finset.sum_le_sum
        intro j hj
        simpa [SimpleGraph.card_neighborFinset_eq_degree] using hmax (branch j)
      _ = i * Δ := by simp
  have hpairCommon (p : CliquePair i) :
      (pairCommonNeighbors G branch p).card ≤ r - 1 := by
    obtain ⟨a, b, hab, hp⟩ := Finset.card_eq_two.mp (Set.powersetCard.card_eq p)
    rw [pairCommonNeighbors_eq_commonNeighbors G branch p hp]
    exact Nat.le_sub_one_of_lt (hlight a b hab).2.2
  have hinner (p : CliquePair i) :
      ((pairCommonNeighbors G branch p).biUnion fun x ↦
        G.neighborFinset x).card ≤ (r - 1) * Δ := by
    calc
      ((pairCommonNeighbors G branch p).biUnion fun x ↦
          G.neighborFinset x).card ≤
          ∑ x ∈ pairCommonNeighbors G branch p,
            (G.neighborFinset x).card := Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ pairCommonNeighbors G branch p, Δ := by
        apply Finset.sum_le_sum
        intro x hx
        simpa [SimpleGraph.card_neighborFinset_eq_degree] using hmax x
      _ = (pairCommonNeighbors G branch p).card * Δ := by simp
      _ ≤ (r - 1) * Δ := Nat.mul_le_mul_right Δ (hpairCommon p)
  have htriple : (tripleBranchForbidden G branch).card ≤
      i.choose 2 * ((r - 1) * Δ) := by
    calc
      (tripleBranchForbidden G branch).card ≤
          ∑ p : CliquePair i,
            ((pairCommonNeighbors G branch p).biUnion fun x ↦
              G.neighborFinset x).card := Finset.card_biUnion_le
      _ ≤ ∑ _p : CliquePair i, (r - 1) * Δ := by
        apply Finset.sum_le_sum
        intro p hp
        exact hinner p
      _ = Fintype.card (CliquePair i) * ((r - 1) * Δ) := by simp
      _ = i.choose 2 * ((r - 1) * Δ) := by rw [card_cliquePair]
  calc
    (branchForbidden G branch).card ≤
        (ordinaryBranchForbidden G branch).card +
          (tripleBranchForbidden G branch).card :=
      Finset.card_union_le _ _
    _ ≤ i * Δ + i.choose 2 * ((r - 1) * Δ) :=
      Nat.add_le_add hord htriple
    _ = (i + i.choose 2 * (r - 1)) * Δ := by ring

theorem card_le_safe_add_forbidden (G : SimpleGraph V)
    [DecidableRel G.Adj] {i : ℕ} (branch : Fin i → V) (U : Finset V) :
    U.card ≤ (safeBranchCandidates G branch U).card +
      (branchForbidden G branch).card := by
  classical
  have hsplit := Finset.card_sdiff_add_card_inter U (branchForbidden G branch)
  have hinter : (U ∩ branchForbidden G branch).card ≤
      (branchForbidden G branch).card :=
    Finset.card_le_card Finset.inter_subset_right
  dsimp only [safeBranchCandidates]
  omega

theorem fin_snoc_injective {i : ℕ} {branch : Fin i → V} {u : V}
    (hbranch : Function.Injective branch) (hu : ∀ j, branch j ≠ u) :
    Function.Injective (Fin.snoc branch u) := by
  intro a b hab
  rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last b with ⟨b, rfl⟩ | rfl
    · simpa using hbranch (by simpa using hab)
    · exact (hu a (by simpa using hab)).elim
  · rcases Fin.eq_castSucc_or_eq_last b with ⟨b, rfl⟩ | rfl
    · exact (hu b (by simpa using hab.symm)).elim
    · rfl

theorem fin_snoc_pairwise {i : ℕ} {R : V → V → Prop}
    (hsymm : Symmetric R) {branch : Fin i → V} {u : V}
    (hold : ∀ a b, a ≠ b → R (branch a) (branch b))
    (hnew : ∀ a, R (branch a) u) :
    ∀ a b, a ≠ b →
      R ((Fin.snoc branch u : Fin (i + 1) → V) a)
        ((Fin.snoc branch u : Fin (i + 1) → V) b) := by
  intro a b hab
  rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last b with ⟨b, rfl⟩ | rfl
    · simpa using hold a b (by
        intro hab'
        apply hab
        simpa [hab'])
    · simpa using hnew a
  · rcases Fin.eq_castSucc_or_eq_last b with ⟨b, rfl⟩ | rfl
    · simpa using hsymm (hnew b)
    · exact (hab rfl).elim

theorem fin_snoc_noTriple {i : ℕ} (G : SimpleGraph V)
    {branch : Fin i → V} {u : V}
    (hold : HasNoTripleCommonNeighbor G branch)
    (hsafe : ∀ a b, a ≠ b → ∀ x,
      G.Adj (branch a) x → G.Adj (branch b) x → ¬ G.Adj x u) :
    HasNoTripleCommonNeighbor G (Fin.snoc branch u) := by
  intro a b l hab hal hbl x hx
  rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last b with ⟨b, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last l with ⟨l, rfl⟩ | rfl
      · apply hold a b l (by simpa using hab) (by simpa using hal)
          (by simpa using hbl) x
        simpa using hx
      · have hs := hsafe a b (by simpa using hab) x
            (by simpa using hx.1) (by simpa using hx.2.1)
        exact hs (by simpa using hx.2.2.symm)
    · rcases Fin.eq_castSucc_or_eq_last l with ⟨l, rfl⟩ | rfl
      · have hs := hsafe a l (by simpa using hal) x
            (by simpa using hx.1) (by simpa using hx.2.2)
        exact hs (by simpa using hx.2.1.symm)
      · exact (hbl rfl).elim
  · rcases Fin.eq_castSucc_or_eq_last b with ⟨b, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last l with ⟨l, rfl⟩ | rfl
      · have hs := hsafe b l (by simpa using hbl) x
            (by simpa using hx.2.1) (by simpa using hx.2.2)
        exact hs (by simpa using hx.1.symm)
      · exact (hal rfl).elim
    · exact (hab rfl).elim

/-- State used in the finite greedy embedding.  Candidate vertices are light
to every chosen branch; ordinary and triple conflicts are removed immediately
before the next branch is selected. -/
structure GreedyState (G : SimpleGraph V) [DecidableRel G.Adj]
    (r i : ℕ) where
  branch : Fin i → V
  injective : Function.Injective branch
  independent : IsIndependentBranchMap G branch
  light : IsLightBranchMap G r branch
  noTriple : HasNoTripleCommonNeighbor G branch
  candidates : Finset V
  candidate_light : ∀ v ∈ candidates, ∀ j, IsLight G r (branch j) v

noncomputable def initialGreedyState (G : SimpleGraph V)
    [DecidableRel G.Adj] (r : ℕ) : GreedyState G r 0 where
  branch := Fin.elim0
  injective := fun i ↦ Fin.elim0 i
  independent := fun i ↦ Fin.elim0 i
  light := fun i ↦ Fin.elim0 i
  noTriple := fun i ↦ Fin.elim0 i
  candidates := Finset.univ
  candidate_light := fun _ _ j ↦ Fin.elim0 j

/-- One step of the greedy construction.  Its final inequality is the exact
cross-multiplied recurrence used in the power induction. -/
theorem GreedyState.extend
    {k i δ Δ : ℕ} (hk : 3 ≤ k) (G : SimpleGraph V)
    [Nonempty V] [DecidableRel G.Adj] (hfree : (cliqueSubdivision k).Free G)
    (hmin : ∀ v, δ ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ Δ)
    (s : GreedyState G (subdivisionThreshold k) i)
    (hroom : 2 * ((i + i.choose 2 * (subdivisionThreshold k - 1)) * Δ) ≤
      s.candidates.card)
    (hsize : 4 * k * Fintype.card V ≤ δ *
      (safeBranchCandidates G s.branch s.candidates).card) :
    ∃ s' : GreedyState G (subdivisionThreshold k) (i + 1),
      δ ^ 2 * s.candidates.card ≤
        (8 * (k - 1) * (subdivisionThreshold k - 1) * Fintype.card V) *
          s'.candidates.card := by
  classical
  let Safe := safeBranchCandidates G s.branch s.candidates
  have hforbidden : (branchForbidden G s.branch).card ≤
      (i + i.choose 2 * (subdivisionThreshold k - 1)) * Δ :=
    card_branchForbidden_le G s.branch hmax s.light
  have hcover : s.candidates.card ≤ Safe.card +
      (branchForbidden G s.branch).card := by
    simpa [Safe] using card_le_safe_add_forbidden G s.branch s.candidates
  have hhalf : s.candidates.card ≤ 2 * Safe.card := by omega
  have hVpos : 0 < Fintype.card V := Fintype.card_pos
  have hSafepos : 0 < Safe.card := by
    have hkpos : 0 < k := by omega
    have hleft : 0 < 4 * k * Fintype.card V := by positivity
    by_contra hn
    have hz : Safe.card = 0 := Nat.eq_zero_of_not_pos hn
    rw [hz, mul_zero] at hsize
    omega
  have hSafe : Safe.Nonempty := Finset.card_pos.mp hSafepos
  obtain ⟨u, huSafe, huLarge⟩ := exists_many_lightNeighbors hk G hfree hmin Safe
    hSafe (by simpa [Safe] using hsize)
  let newBranch : Fin (i + 1) → V := Fin.snoc s.branch u
  let newCandidates : Finset V :=
    lightNeighborsOn G (subdivisionThreshold k) Safe u
  have huData := (mem_safeBranchCandidates G s.branch s.candidates u).mp
    (by simpa [Safe] using huSafe)
  have huOldLight (j : Fin i) :
      IsLight G (subdivisionThreshold k) (s.branch j) u :=
    s.candidate_light u huData.1 j
  have huOldNe (j : Fin i) : s.branch j ≠ u := (huOldLight j).1
  have hnewInjective : Function.Injective newBranch := by
    exact fin_snoc_injective s.injective huOldNe
  have hnewIndependent : IsIndependentBranchMap G newBranch := by
    simpa [IsIndependentBranchMap, newBranch] using
      (fin_snoc_pairwise
        (R := fun a b ↦ ¬ G.Adj a b)
        (fun _a _b hab hba ↦ hab hba.symm)
        s.independent huData.2.1)
  have hnewLight : IsLightBranchMap G (subdivisionThreshold k) newBranch := by
    simpa [IsLightBranchMap, newBranch] using
      (fin_snoc_pairwise
        (R := IsLight G (subdivisionThreshold k))
        (fun a b hab ↦
          (isLight_comm G (subdivisionThreshold k) a b).mp hab)
        s.light huOldLight)
  have huTripleSafe : ∀ a b, a ≠ b → ∀ x,
      G.Adj (s.branch a) x → G.Adj (s.branch b) x → ¬ G.Adj x u := by
    intro a b hab x hax hbx
    let p : CliquePair i := ⟨{a, b}, by simp [hab]⟩
    apply huData.2.2 p x
    simp [pairCommonNeighbors, p, hax, hbx]
  have hnewNoTriple : HasNoTripleCommonNeighbor G newBranch := by
    exact fin_snoc_noTriple G s.noTriple huTripleSafe
  have hnewCandidateLight : ∀ v ∈ newCandidates, ∀ j,
      IsLight G (subdivisionThreshold k) (newBranch j) v := by
    intro v hv j
    have hvData := (mem_lightNeighborsOn G (subdivisionThreshold k) Safe u v).mp
      (by simpa [newCandidates] using hv)
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
    · have hvOld : v ∈ s.candidates :=
        (mem_safeBranchCandidates G s.branch s.candidates v).mp hvData.1 |>.1
      simpa [newBranch] using s.candidate_light v hvOld j
    · simpa [newBranch] using hvData.2
  let s' : GreedyState G (subdivisionThreshold k) (i + 1) :=
    { branch := newBranch
      injective := hnewInjective
      independent := hnewIndependent
      light := hnewLight
      noTriple := hnewNoTriple
      candidates := newCandidates
      candidate_light := hnewCandidateLight }
  refine ⟨s', ?_⟩
  have havg : δ ^ 2 * Safe.card ≤
      (4 * (k - 1) * (subdivisionThreshold k - 1) * Fintype.card V) *
        newCandidates.card := by
    simpa [newCandidates] using huLarge
  calc
    δ ^ 2 * s.candidates.card ≤ δ ^ 2 * (2 * Safe.card) := by gcongr
    _ = 2 * (δ ^ 2 * Safe.card) := by ring
    _ ≤ 2 * ((4 * (k - 1) * (subdivisionThreshold k - 1) *
        Fintype.card V) * newCandidates.card) := by gcongr
    _ = (8 * (k - 1) * (subdivisionThreshold k - 1) * Fintype.card V) *
        s'.candidates.card := by simp [s', newCandidates]; ring

/-- The last branch vertex needs no further averaging: any safe remaining
candidate completes the good branch map. -/
theorem GreedyState.finish
    {r i : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : GreedyState G r i)
    (hSafe : (safeBranchCandidates G s.branch s.candidates).Nonempty) :
    cliqueSubdivision (i + 1) ⊑ G := by
  classical
  obtain ⟨u, huSafe⟩ := hSafe
  let newBranch : Fin (i + 1) → V := Fin.snoc s.branch u
  have huData := (mem_safeBranchCandidates G s.branch s.candidates u).mp huSafe
  have huOldLight (j : Fin i) : IsLight G r (s.branch j) u :=
    s.candidate_light u huData.1 j
  have hnewInjective : Function.Injective newBranch := by
    exact fin_snoc_injective s.injective (fun j ↦ (huOldLight j).1)
  have hnewIndependent : IsIndependentBranchMap G newBranch := by
    simpa [IsIndependentBranchMap, newBranch] using
      (fin_snoc_pairwise
        (R := fun a b ↦ ¬ G.Adj a b)
        (fun _a _b hab hba ↦ hab hba.symm)
        s.independent huData.2.1)
  have hnewLight : IsLightBranchMap G r newBranch := by
    simpa [IsLightBranchMap, newBranch] using
      (fin_snoc_pairwise
        (R := IsLight G r)
        (fun a b hab ↦ (isLight_comm G r a b).mp hab)
        s.light huOldLight)
  have huTripleSafe : ∀ a b, a ≠ b → ∀ x,
      G.Adj (s.branch a) x → G.Adj (s.branch b) x → ¬ G.Adj x u := by
    intro a b hab x hax hbx
    let p : CliquePair i := ⟨{a, b}, by simp [hab]⟩
    apply huData.2.2 p x
    simp [pairCommonNeighbors, p, hax, hbx]
  have hnewNoTriple : HasNoTripleCommonNeighbor G newBranch :=
    fin_snoc_noTriple G s.noTriple huTripleSafe
  exact cliqueSubdivision_isContained_of_goodBranchMap G newBranch
    hnewInjective hnewIndependent hnewLight hnewNoTriple

/-- The loss factor in one averaged greedy step. -/
def greedyFactor (k : ℕ) : ℕ :=
  8 * (k - 1) * (subdivisionThreshold k - 1)

theorem greedyFactor_pos {k : ℕ} (hk : 3 ≤ k) : 0 < greedyFactor k := by
  have hkpred : 0 < k - 1 := by omega
  have hr : 0 < subdivisionThreshold k - 1 := by
    dsimp [subdivisionThreshold]
    omega
  dsimp [greedyFactor]
  positivity

def greedyRoomMax (k : ℕ) : ℕ :=
  k + k.choose 2 * (subdivisionThreshold k - 1)

/-- A generous integral scale that simultaneously absorbs every constant in
the finitely many greedy stages. -/
def localEmbeddingScale (k K : ℕ) : ℕ :=
  greedyFactor k ^ k * (2 * greedyRoomMax k * K + 8 * k + 1)

theorem localEmbeddingScale_pos {k K : ℕ} (hk : 3 ≤ k) :
    0 < localEmbeddingScale k K := by
  dsimp [localEmbeddingScale]
  exact mul_pos (pow_pos (greedyFactor_pos hk) k) (by omega)

theorem averageConstant_le_localEmbeddingScale
    {k i K : ℕ} (hk : 3 ≤ k) (hi : i < k) :
    greedyFactor k ^ i * (8 * k) ≤ localEmbeddingScale k K := by
  have hpow : greedyFactor k ^ i ≤ greedyFactor k ^ k :=
    Nat.pow_le_pow_right (greedyFactor_pos hk) hi.le
  calc
    greedyFactor k ^ i * (8 * k) ≤ greedyFactor k ^ k * (8 * k) := by
      gcongr
    _ ≤ greedyFactor k ^ k *
        (2 * greedyRoomMax k * K + 8 * k + 1) := by gcongr; omega
    _ = localEmbeddingScale k K := rfl

theorem roomConstant_le_localEmbeddingScale
    {k i K : ℕ} (hk : 3 ≤ k) (hi : i < k) :
    greedyFactor k ^ i *
        (2 * (i + i.choose 2 * (subdivisionThreshold k - 1)) * K) ≤
      localEmbeddingScale k K := by
  have hik : i ≤ k := hi.le
  have hchoose : i.choose 2 ≤ k.choose 2 := Nat.choose_le_choose 2 hik
  have hroom : i + i.choose 2 * (subdivisionThreshold k - 1) ≤
      greedyRoomMax k := by
    dsimp [greedyRoomMax]
    gcongr
  have hpow : greedyFactor k ^ i ≤ greedyFactor k ^ k :=
    Nat.pow_le_pow_right (greedyFactor_pos hk) hik
  calc
    greedyFactor k ^ i *
        (2 * (i + i.choose 2 * (subdivisionThreshold k - 1)) * K) ≤
        greedyFactor k ^ k * (2 * greedyRoomMax k * K) := by gcongr
    _ ≤ greedyFactor k ^ k *
        (2 * greedyRoomMax k * K + 8 * k + 1) := by gcongr; omega
    _ = localEmbeddingScale k K := rfl

theorem localEmbeddingScale_le_pow {k K p : ℕ}
    (hk : 3 ≤ k) (hp : 0 < p) :
    localEmbeddingScale k K ≤ localEmbeddingScale k K ^ p := by
  calc
    localEmbeddingScale k K = localEmbeddingScale k K ^ 1 := by simp
    _ ≤ localEmbeddingScale k K ^ p :=
      Nat.pow_le_pow_right (localEmbeddingScale_pos hk) hp

/-- Iteration of `GreedyState.extend`.  The hypotheses are deliberately
stated as the two arithmetic obligations at each stage; the following local
embedding theorem discharges them all from one power inequality. -/
theorem exists_scaled_greedyState
    {k δ Δ m : ℕ} (hk : 3 ≤ k) (G : SimpleGraph V)
    [Nonempty V] [DecidableRel G.Adj]
    (hfree : (cliqueSubdivision k).Free G)
    (hmin : ∀ v, δ ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ Δ)
    (hstage : ∀ (i : ℕ), i < m →
      ∀ s : GreedyState G (subdivisionThreshold k) i,
        δ ^ (2 * i) * Fintype.card V ≤
            (greedyFactor k * Fintype.card V) ^ i * s.candidates.card →
        2 * ((i + i.choose 2 * (subdivisionThreshold k - 1)) * Δ) ≤
            s.candidates.card ∧
          4 * k * Fintype.card V ≤ δ *
            (safeBranchCandidates G s.branch s.candidates).card) :
    ∃ s : GreedyState G (subdivisionThreshold k) m,
      δ ^ (2 * m) * Fintype.card V ≤
        (greedyFactor k * Fintype.card V) ^ m * s.candidates.card := by
  induction m with
  | zero =>
      refine ⟨initialGreedyState G (subdivisionThreshold k), ?_⟩
      simp [initialGreedyState]
  | succ m ih =>
      obtain ⟨s, hs⟩ := ih (fun i hi ↦ hstage i (Nat.lt_trans hi (Nat.lt_succ_self m)))
      obtain ⟨hroom, hsize⟩ := hstage m (Nat.lt_succ_self m) s hs
      obtain ⟨s', hrec⟩ := s.extend hk G hfree hmin hmax hroom hsize
      refine ⟨s', ?_⟩
      have hrec' : δ ^ 2 * s.candidates.card ≤
          (greedyFactor k * Fintype.card V) * s'.candidates.card := by
        simpa [greedyFactor] using hrec
      calc
        δ ^ (2 * (m + 1)) * Fintype.card V =
            δ ^ 2 * (δ ^ (2 * m) * Fintype.card V) := by ring
        _ ≤ δ ^ 2 * ((greedyFactor k * Fintype.card V) ^ m *
            s.candidates.card) := by gcongr
        _ = (greedyFactor k * Fintype.card V) ^ m *
            (δ ^ 2 * s.candidates.card) := by ring
        _ ≤ (greedyFactor k * Fintype.card V) ^ m *
            ((greedyFactor k * Fintype.card V) * s'.candidates.card) := by
          gcongr
        _ = (greedyFactor k * Fintype.card V) ^ (m + 1) *
            s'.candidates.card := by rw [pow_succ]; ring

/-- A completely finite local embedding criterion.  The two displayed
families are exactly the room and averaging inequalities needed at stages
`0,…,k-2`; unlike a quotient recurrence, they remain valid at zero and need
no rounding conventions. -/
theorem cliqueSubdivision_isContained_of_greedyBounds
    {k δ Δ : ℕ} (hk : 3 ≤ k) (hδ : 0 < δ)
    (G : SimpleGraph V) [Nonempty V] [DecidableRel G.Adj]
    (hfree : (cliqueSubdivision k).Free G)
    (hmin : ∀ v, δ ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ Δ)
    (hroomBounds : ∀ i < k,
      (greedyFactor k * Fintype.card V) ^ i *
          (2 * ((i + i.choose 2 * (subdivisionThreshold k - 1)) * Δ)) ≤
        δ ^ (2 * i) * Fintype.card V)
    (haverageBounds : ∀ i < k - 1,
      (greedyFactor k * Fintype.card V) ^ i *
          (8 * k * Fintype.card V) ≤
        δ ^ (2 * i + 1) * Fintype.card V) :
    cliqueSubdivision k ⊑ G := by
  classical
  let N := Fintype.card V
  let Q := greedyFactor k * N
  have hN : 0 < N := by exact Fintype.card_pos
  have hQ : 0 < Q := mul_pos (greedyFactor_pos hk) hN
  have hstage : ∀ (i : ℕ), i < k - 1 →
      ∀ s : GreedyState G (subdivisionThreshold k) i,
        δ ^ (2 * i) * Fintype.card V ≤
            (greedyFactor k * Fintype.card V) ^ i * s.candidates.card →
        2 * ((i + i.choose 2 * (subdivisionThreshold k - 1)) * Δ) ≤
            s.candidates.card ∧
          4 * k * Fintype.card V ≤ δ *
            (safeBranchCandidates G s.branch s.candidates).card := by
    intro i hi s hinv
    have hik : i < k := hi.trans (by omega)
    have hQpow : 0 < Q ^ i := pow_pos hQ i
    have hroomMul : Q ^ i *
        (2 * ((i + i.choose 2 * (subdivisionThreshold k - 1)) * Δ)) ≤
        Q ^ i * s.candidates.card := by
      calc
        Q ^ i * (2 * ((i + i.choose 2 *
            (subdivisionThreshold k - 1)) * Δ)) ≤
            δ ^ (2 * i) * N := by
          simpa [Q, N] using hroomBounds i hik
        _ ≤ Q ^ i * s.candidates.card := by simpa [Q, N] using hinv
    have hroom : 2 * ((i + i.choose 2 *
        (subdivisionThreshold k - 1)) * Δ) ≤ s.candidates.card :=
      Nat.le_of_mul_le_mul_left hroomMul hQpow
    let Safe := safeBranchCandidates G s.branch s.candidates
    have hforbidden : (branchForbidden G s.branch).card ≤
        (i + i.choose 2 * (subdivisionThreshold k - 1)) * Δ :=
      card_branchForbidden_le G s.branch hmax s.light
    have hcover : s.candidates.card ≤ Safe.card +
        (branchForbidden G s.branch).card := by
      simpa [Safe] using card_le_safe_add_forbidden G s.branch s.candidates
    have hhalf : s.candidates.card ≤ 2 * Safe.card := by omega
    have hinvδ : δ ^ (2 * i + 1) * N ≤
        Q ^ i * (δ * s.candidates.card) := by
      calc
        δ ^ (2 * i + 1) * N = δ * (δ ^ (2 * i) * N) := by
          rw [pow_succ]
          ring
        _ ≤ δ * (Q ^ i * s.candidates.card) := by gcongr
        _ = Q ^ i * (δ * s.candidates.card) := by ring
    have havgMul : Q ^ i * (8 * k * N) ≤
        Q ^ i * (δ * s.candidates.card) := by
      have hbound : Q ^ i * (8 * k * N) ≤
          δ ^ (2 * i + 1) * N := by
        simpa [Q, N] using haverageBounds i hi
      exact hbound.trans hinvδ
    have havgU : 8 * k * N ≤ δ * s.candidates.card :=
      Nat.le_of_mul_le_mul_left havgMul hQpow
    have hsize : 4 * k * N ≤ δ * Safe.card := by
      have hmulHalf : δ * s.candidates.card ≤ δ * (2 * Safe.card) := by
        gcongr
      have htwice : 2 * (4 * k * N) ≤ 2 * (δ * Safe.card) := by
        calc
          2 * (4 * k * N) = 8 * k * N := by ring
          _ ≤ δ * s.candidates.card := havgU
          _ ≤ δ * (2 * Safe.card) := hmulHalf
          _ = 2 * (δ * Safe.card) := by ring
      exact Nat.le_of_mul_le_mul_left htwice (by norm_num)
    exact ⟨hroom, by simpa [N, Safe] using hsize⟩
  obtain ⟨s, hs⟩ := exists_scaled_greedyState hk G hfree hmin hmax hstage
  have hkm1k : k - 1 < k := by omega
  have hQpow : 0 < Q ^ (k - 1) := pow_pos hQ _
  have hroomMul : Q ^ (k - 1) *
      (2 * (((k - 1) + (k - 1).choose 2 *
        (subdivisionThreshold k - 1)) * Δ)) ≤
      Q ^ (k - 1) * s.candidates.card := by
    calc
      Q ^ (k - 1) * (2 * (((k - 1) + (k - 1).choose 2 *
          (subdivisionThreshold k - 1)) * Δ)) ≤
          δ ^ (2 * (k - 1)) * N := by
        simpa [Q, N] using hroomBounds (k - 1) hkm1k
      _ ≤ Q ^ (k - 1) * s.candidates.card := by simpa [Q, N] using hs
  have hroom : 2 * (((k - 1) + (k - 1).choose 2 *
      (subdivisionThreshold k - 1)) * Δ) ≤ s.candidates.card :=
    Nat.le_of_mul_le_mul_left hroomMul hQpow
  let Safe := safeBranchCandidates G s.branch s.candidates
  have hforbidden : (branchForbidden G s.branch).card ≤
      ((k - 1) + (k - 1).choose 2 * (subdivisionThreshold k - 1)) * Δ :=
    card_branchForbidden_le G s.branch hmax s.light
  have hcover : s.candidates.card ≤ Safe.card +
      (branchForbidden G s.branch).card := by
    simpa [Safe] using card_le_safe_add_forbidden G s.branch s.candidates
  have hUpos : 0 < s.candidates.card := by
    have hleft : 0 < δ ^ (2 * (k - 1)) * N := by positivity
    have hprodpos : 0 < Q ^ (k - 1) * s.candidates.card :=
      hleft.trans_le (by simpa [Q, N] using hs)
    by_contra hn
    have hz : s.candidates.card = 0 := Nat.eq_zero_of_not_pos hn
    have : 0 < 0 := by simpa [hz] using hprodpos
    omega
  have hSafepos : 0 < Safe.card := by omega
  have hfinish := s.finish G (Finset.card_pos.mp hSafepos)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at hfinish
  exact hfinish

/-- The usual almost-regular local form: minimum degree on the Janzer scale
and maximum degree at most `K` times the minimum force the subdivision. -/
theorem cliqueSubdivision_isContained_of_almostRegularScale
    {k K δ : ℕ} (hk : 3 ≤ k) (G : SimpleGraph V)
    [Nonempty V] [DecidableRel G.Adj]
    (hfree : (cliqueSubdivision k).Free G)
    (hmin : ∀ v, δ ≤ G.degree v)
    (hmax : ∀ v, G.degree v ≤ K * δ)
    (hscale : (localEmbeddingScale k K : ℝ) *
      (Fintype.card V : ℝ) ^ janzerAlpha k ≤ δ) :
    cliqueSubdivision k ⊑ G := by
  classical
  let N := Fintype.card V
  let B := greedyFactor k
  let C := localEmbeddingScale k K
  have hN : 1 ≤ N := by exact Fintype.card_pos
  have hNreal : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hCreal : (0 : ℝ) < C := by
    exact_mod_cast localEmbeddingScale_pos (K := K) hk
  have hscalePos : (0 : ℝ) <
      (C : ℝ) * (N : ℝ) ^ janzerAlpha k := by
    exact mul_pos hCreal (Real.rpow_pos_of_pos hNreal _)
  have hδreal : (0 : ℝ) < δ := hscalePos.trans_le (by simpa [C, N] using hscale)
  have hδ : 0 < δ := by exact_mod_cast hδreal
  apply cliqueSubdivision_isContained_of_greedyBounds hk hδ G hfree hmin hmax
  · intro i hi
    by_cases hi₀ : i = 0
    · subst i
      simp
    · have hipos : 0 < i := Nat.pos_of_ne_zero hi₀
      let F := i + i.choose 2 * (subdivisionThreshold k - 1)
      let p := 2 * i - 1
      have hp : 0 < p := by dsimp [p]; omega
      have hconstNat : B ^ i * (2 * F * K) ≤
          C ^ p := by
        have hbase : B ^ i * (2 * F * K) ≤ C := by
          simpa [F, B, C] using
            (roomConstant_le_localEmbeddingScale (K := K) hk hi)
        have hpower : C ≤ C ^ p := by
          simpa [C] using (localEmbeddingScale_le_pow (K := K) hk hp)
        exact hbase.trans hpower
      have hconst : ((B ^ i * (2 * F * K) : ℕ) : ℝ) ≤
          ((C ^ p : ℕ) : ℝ) := by exact_mod_cast hconstNat
      have hNpow := natCast_pow_le_janzerAlpha_room hk hi hipos hN
      have hscalePow : ((C : ℝ) * (N : ℝ) ^ janzerAlpha k) ^ p ≤
          (δ : ℝ) ^ p := by
        exact pow_le_pow_left₀ (by positivity) (by simpa [C, N] using hscale) p
      have hrearrange : (B * N) ^ i * (2 * (F * (K * δ))) =
          (B ^ i * (2 * F * K)) * N ^ i * δ := by
        rw [mul_pow]
        ring
      have hreal : (((B * N) ^ i * (2 * (F * (K * δ))) : ℕ) : ℝ) ≤
          (((δ ^ (2 * i) * N : ℕ) : ℝ)) := by
        calc
          (((B * N) ^ i * (2 * (F * (K * δ))) : ℕ) : ℝ) =
              ((B ^ i * (2 * F * K) : ℕ) : ℝ) *
                (N : ℝ) ^ i * δ := by
            rw [hrearrange]
            push_cast
            rfl
          _ ≤ ((C ^ p : ℕ) : ℝ) *
              ((N : ℝ) * ((N : ℝ) ^ janzerAlpha k) ^ p) * δ := by
            gcongr
          _ = (((C : ℝ) * (N : ℝ) ^ janzerAlpha k) ^ p) *
              (N : ℝ) * δ := by
            push_cast
            rw [mul_pow]
            ring
          _ ≤ (δ : ℝ) ^ p * (N : ℝ) * δ := by gcongr
          _ = (((δ ^ (2 * i) * N : ℕ) : ℝ)) := by
            push_cast
            have hpEq : p + 1 = 2 * i := by dsimp [p]; omega
            calc
              (δ : ℝ) ^ p * (N : ℝ) * δ =
                  ((δ : ℝ) ^ p * δ) * N := by ring
              _ = (δ : ℝ) ^ (p + 1) * N := by rw [pow_succ]
              _ = (δ : ℝ) ^ (2 * i) * N := by rw [hpEq]
      simpa [F, B, N] using (show
        (B * N) ^ i * (2 * (F * (K * δ))) ≤ δ ^ (2 * i) * N by
          exact_mod_cast hreal)
  · intro i hi
    let p := 2 * i + 1
    have hp : 0 < p := by dsimp [p]; omega
    have hik : i < k := hi.trans (by omega)
    have hconstNat : B ^ i * (8 * k) ≤ C ^ p :=
      (averageConstant_le_localEmbeddingScale hk hik).trans
        (localEmbeddingScale_le_pow hk hp)
    have hconst : (B : ℝ) ^ i * (8 * k) ≤ (C : ℝ) ^ p := by
      exact_mod_cast hconstNat
    have hNpow := natCast_pow_le_janzerAlpha_average hk hi hN
    have hscalePow : ((C : ℝ) * (N : ℝ) ^ janzerAlpha k) ^ p ≤
        (δ : ℝ) ^ p := by
      exact pow_le_pow_left₀ (by positivity) (by simpa [C, N] using hscale) p
    have hreal : ((((B * N) ^ i * (8 * k * N) : ℕ) : ℝ)) ≤
        (((δ ^ (2 * i + 1) * N : ℕ) : ℝ)) := by
      calc
        ((((B * N) ^ i * (8 * k * N) : ℕ) : ℝ)) =
            ((B : ℝ) ^ i * (8 * k)) * (N : ℝ) ^ i * (N : ℝ) := by
          push_cast
          rw [mul_pow]
          ring
        _ ≤ (C : ℝ) ^ p *
            (((N : ℝ) ^ janzerAlpha k) ^ p) * (N : ℝ) := by gcongr
        _ = (((C : ℝ) * (N : ℝ) ^ janzerAlpha k) ^ p) *
            (N : ℝ) := by rw [mul_pow]
        _ ≤ (δ : ℝ) ^ p * (N : ℝ) := by gcongr
        _ = (((δ ^ (2 * i + 1) * N : ℕ) : ℝ)) := by
          simp [p]
    exact_mod_cast hreal

/-- Support-relative form of the almost-regular embedding theorem.  Isolated
ambient vertices are discarded before applying the local theorem, so its
scale is measured using the number of vertices actually used by `H`. -/
theorem cliqueSubdivision_isContained_of_supportAlmostRegular
    {k K δ : ℕ} (hk : 3 ≤ k) (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hHG : H ≤ G) (hedge : H.edgeFinset.Nonempty)
    (hmin : ∀ v ∈ H.support, δ ≤ H.degree v)
    (hmax : ∀ v ∈ H.support, H.degree v ≤ K * δ)
    (hscale : (localEmbeddingScale k K : ℝ) *
      (H.support.ncard : ℝ) ^ janzerAlpha k ≤ δ) :
    cliqueSubdivision k ⊑ G := by
  classical
  let S := H.support
  let J := H.induce S
  have hS : S.Nonempty := Erdos182.support_nonempty_of_edgeFinset_nonempty hedge
  letI : Nonempty S := hS.to_subtype
  have hJmin : ∀ v : S, δ ≤ J.degree v := by
    intro v
    rw [show J.degree v = H.degree v by
      exact (Erdos182.induce_support_exact (G := H)).2 v]
    exact hmin v v.2
  have hJmax : ∀ v : S, J.degree v ≤ K * δ := by
    intro v
    rw [show J.degree v = H.degree v by
      exact (Erdos182.induce_support_exact (G := H)).2 v]
    exact hmax v v.2
  have hJG : J ⊑ G :=
    (SimpleGraph.Embedding.induce S).isContained.trans
      (SimpleGraph.Copy.ofLE H G hHG).isContained
  by_contra hnot
  have hJfree : (cliqueSubdivision k).Free J := by
    intro hcopy
    exact hnot (hcopy.trans hJG)
  have hJscale : (localEmbeddingScale k K : ℝ) *
      (Fintype.card S : ℝ) ^ janzerAlpha k ≤ δ := by
    rw [Set.fintypeCard_eq_ncard]
    exact hscale
  exact hJfree
    (cliqueSubdivision_isContained_of_almostRegularScale hk J hJfree
      hJmin hJmax hJscale)

/-! ## Finite density regularization and the global forcing theorem -/

def regularizationLoss : ℕ := 4 * regularizationParts

def denseForcingConstant (k : ℕ) : ℕ :=
  4 * regularizationParts ^ 2 *
    (localEmbeddingScale k regularizationLoss + 1)

theorem denseForcingConstant_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < denseForcingConstant k := by
  dsimp [denseForcingConstant, regularizationLoss, regularizationParts]
  positivity

/-- The global finite form of Janzer's theorem.  The proof is the
Erdős--Simonovits density regularization: either deleting the high-degree
vertices leaves a dense bounded-maximum-degree graph, or an equipartition
finds a smaller graph with no loss in normalized density. -/
theorem cliqueSubdivision_isContained_of_denseSupport
    {k : ℕ} (hk : 3 ≤ k) (G : SimpleGraph V)
    (hedge : G.edgeSet.Nonempty)
    (hdense : (denseForcingConstant k : ℝ) *
      (G.support.ncard : ℝ) ^ (1 + janzerAlpha k) ≤
        (G.edgeSet.ncard : ℝ)) :
    cliqueSubdivision k ⊑ G := by
  classical
  let M := regularizationParts
  let K := regularizationLoss
  let L := localEmbeddingScale k K
  let C := denseForcingConstant k
  generalize hn : G.support.ncard = n at hdense
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
      letI : DecidableRel G.Adj := Classical.decRel G.Adj
      let e := G.edgeFinset.card
      have hedgeFin : G.edgeFinset.Nonempty := by
        simpa [SimpleGraph.edgeFinset] using hedge
      have hnpos : 0 < n := by
        rw [← hn]
        exact (Set.ncard_pos (s := G.support)).mpr
          (Erdos182.support_nonempty_of_edgeFinset_nonempty hedgeFin)
      have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
      have heq : G.edgeSet.ncard = e := by
        exact Set.ncard_eq_toFinset_card' G.edgeSet
      have hdense' : (C : ℝ) * (n : ℝ) ^ (1 + janzerAlpha k) ≤ e := by
        simpa [C, heq] using hdense
      have hMn : M ≤ n := by
        by_contra hnot
        have hnM : n < M := Nat.lt_of_not_ge hnot
        have hrpowOne : (1 : ℝ) ≤
            (n : ℝ) ^ (1 + janzerAlpha k) :=
          Real.one_le_rpow (by exact_mod_cast hnpos) (one_add_janzerAlpha_pos hk).le
        have hCe : (C : ℝ) ≤ e := by
          calc
            (C : ℝ) ≤ (C : ℝ) *
                (n : ℝ) ^ (1 + janzerAlpha k) := by
              nth_rewrite 1 [← mul_one (C : ℝ)]
              gcongr
            _ ≤ e := hdense'
        have hCMM : M ^ 2 ≤ C := by
          dsimp [C, denseForcingConstant]
          calc
            M ^ 2 ≤ 4 * M ^ 2 := by omega
            _ ≤ 4 * M ^ 2 * (L + 1) := by
              nth_rewrite 1 [← mul_one (4 * M ^ 2)]
              gcongr
              exact Nat.succ_pos L
        have heN : e ≤ n ^ 2 := by
          calc
            e = (G.induce G.support).edgeFinset.card :=
              G.card_edgeFinset_induce_support.symm
            _ ≤ (Fintype.card G.support).choose 2 :=
              (G.induce G.support).card_edgeFinset_le_card_choose_two
            _ = n.choose 2 := by rw [Set.fintypeCard_eq_ncard, hn]
            _ ≤ n ^ 2 := Nat.choose_le_pow n 2
        have hNNMM : n ^ 2 < M ^ 2 := Nat.pow_lt_pow_left hnM (by norm_num)
        have hnat : C ≤ e := by exact_mod_cast hCe
        omega
      let q := e / n
      let threshold := M * (q + 1)
      let S := G.support.toFinset
      let A := S.filter fun v ↦ threshold ≤ G.degree v
      let D := ∑ v ∈ A, G.degree v
      have hScard : S.card = n := by
        dsimp [S]
        rw [← Set.ncard_eq_toFinset_card' G.support, hn]
      have hAS : A ⊆ S := Finset.filter_subset _ _
      have hthreshold : 0 < threshold := by
        dsimp [threshold]
        exact mul_pos (by norm_num [M, regularizationParts]) (Nat.succ_pos q)
      have hTD : threshold * A.card ≤ D := by
        calc
          threshold * A.card = ∑ _v ∈ A, threshold := by simp [mul_comm]
          _ ≤ ∑ v ∈ A, G.degree v := by
            apply Finset.sum_le_sum
            intro v hv
            exact (Finset.mem_filter.mp hv).2
          _ = D := rfl
      have hDtwo : D ≤ 2 * e := by
        calc
          D ≤ ∑ v ∈ S, G.degree v :=
            Finset.sum_le_sum_of_subset hAS
          _ = 2 * e := by
            simpa [S, e] using G.sum_degrees_support_eq_twice_card_edges
      have heqdiv : e < n * (q + 1) := by
        simpa [q] using Nat.lt_mul_div_succ e hnpos
      have hMeTn : M * e ≤ threshold * n := by
        have hMpos : 0 < M := by norm_num [M, regularizationParts]
        have := Nat.le_of_lt ((Nat.mul_lt_mul_left hMpos).2 heqdiv)
        simpa [threshold, mul_assoc, mul_left_comm, mul_comm] using this
      have hAcard : M * A.card ≤ 2 * n := by
        have hmul : threshold * (M * A.card) ≤ threshold * (2 * n) := by
          calc
            threshold * (M * A.card) = M * (threshold * A.card) := by ring
            _ ≤ M * (2 * e) := Nat.mul_le_mul_left M (hTD.trans hDtwo)
            _ = 2 * (M * e) := by ring
            _ ≤ 2 * (threshold * n) := Nat.mul_le_mul_left 2 hMeTn
            _ = threshold * (2 * n) := by ring
        exact Nat.le_of_mul_le_mul_left hmul hthreshold
      have hxone : (1 : ℝ) ≤ (n : ℝ) ^ janzerAlpha k :=
        Real.one_le_rpow (by exact_mod_cast hnpos) (janzerAlpha_pos hk).le
      have hpowSplit : (n : ℝ) ^ (1 + janzerAlpha k) =
          (n : ℝ) * (n : ℝ) ^ janzerAlpha k := by
        rw [Real.rpow_add hnR, Real.rpow_one]
      have hCsmall : 4 * (L + 1) ≤ C := by
        dsimp [C, denseForcingConstant]
        have hMone : 1 ≤ M ^ 2 := Nat.one_le_pow (m := M) 2
          (by norm_num [M, regularizationParts])
        calc
          4 * (L + 1) = 1 * (4 * (L + 1)) := by simp
          _ ≤ M ^ 2 * (4 * (L + 1)) := Nat.mul_le_mul_right _ hMone
          _ = 4 * M ^ 2 * (L + 1) := by ring
      have hqraw : ((4 * (L + 1) : ℕ) : ℝ) *
          (n : ℝ) ^ janzerAlpha k < (q + 1 : ℕ) := by
        have heUpperR : (e : ℝ) < (n : ℝ) * (q + 1 : ℕ) := by
          exact_mod_cast heqdiv
        have hCdense : (C : ℝ) *
            ((n : ℝ) * (n : ℝ) ^ janzerAlpha k) ≤ e := by
          simpa [hpowSplit] using hdense'
        have hsmallR : ((4 * (L + 1) : ℕ) : ℝ) ≤ C := by
          exact_mod_cast hCsmall
        have hxnonneg : (0 : ℝ) ≤ (n : ℝ) ^ janzerAlpha k := by positivity
        have := mul_le_mul_of_nonneg_right hsmallR hxnonneg
        nlinarith
      have hqhalf : q ≤ 2 * (q / 2) + 1 := by omega
      have hq2 : 2 ≤ q := by
        have hLpos : (0 : ℝ) < L := by
          exact_mod_cast localEmbeddingScale_pos (K := K) hk
        have hcoef : (4 : ℝ) ≤ (4 * (L + 1) : ℕ) := by
          push_cast
          nlinarith
        have hleft : (4 : ℝ) ≤ ((4 * (L + 1) : ℕ) : ℝ) *
            (n : ℝ) ^ janzerAlpha k := by
          calc
            (4 : ℝ) = 4 * 1 := by ring
            _ ≤ ((4 * (L + 1) : ℕ) : ℝ) *
                (n : ℝ) ^ janzerAlpha k :=
              mul_le_mul hcoef hxone (by norm_num) (by positivity)
        have hfour : (4 : ℝ) < (q + 1 : ℕ) := hleft.trans_lt hqraw
        have hfourNat : 4 < q + 1 := by exact_mod_cast hfour
        omega
      have hdeltaScale : (L : ℝ) *
          (n : ℝ) ^ janzerAlpha k ≤ (q / 2 : ℕ) := by
        have hqhalfR : (q : ℝ) ≤ 2 * (q / 2 : ℕ) + 1 := by
          exact_mod_cast hqhalf
        have hLnonneg : (0 : ℝ) ≤ L := by positivity
        have hqraw' := hqraw
        push_cast at hqraw'
        nlinarith
      by_cases hlow : 2 * D < e
      · let R := G.deleteEdges (edgesMeeting G A : Set (Sym2 V))
        have hRG : R ≤ G := SimpleGraph.deleteEdges_le _
        have hcount : e ≤ R.edgeFinset.card + D := by
          simpa [R, e, D] using
            edge_count_le_deleteEdgesMeeting_add_degree_sum G A
        have heR : e ≤ 2 * R.edgeFinset.card := by omega
        have hRnonempty : R.edgeFinset.Nonempty := by
          apply Finset.card_pos.mp
          have hepos : 0 < e := Finset.card_pos.mpr hedgeFin
          omega
        have hRsupp : R.support.ncard ≤ n := by
          have hs := Set.ncard_le_ncard (SimpleGraph.support_mono hRG) (Set.toFinite _)
          simpa [hn] using hs
        have hqdense : q * R.support.ncard ≤ 2 * R.edgeFinset.card := by
          calc
            q * R.support.ncard ≤ q * n := by gcongr
            _ ≤ e := by
              dsimp [q]
              exact Nat.div_mul_le_self e n
            _ ≤ 2 * R.edgeFinset.card := heR
        obtain ⟨H, instH, hHR, hHedge, _hHdense, hHmin⟩ :=
          Erdos182.exists_minDegree_core R q hRnonempty hqdense
        letI : DecidableRel H.Adj := instH
        have hHG : H ≤ G := hHR.trans hRG
        have hmin : ∀ v ∈ H.support, q / 2 ≤ H.degree v := by
          intro v hv
          have := hHmin v hv
          omega
        have hmax : ∀ v ∈ H.support,
            H.degree v ≤ K * (q / 2) := by
          intro v hv
          have hvR : v ∈ R.support := SimpleGraph.support_mono hHR hv
          have hvA : v ∉ A := by
            simpa [R] using support_deleteEdgesMeeting_not_mem G A hvR
          have hvG : v ∈ G.support := SimpleGraph.support_mono hRG hvR
          have hvS : v ∈ S := by simpa [S] using hvG
          have hdegG : G.degree v < threshold := by
            by_contra hnot
            exact hvA (Finset.mem_filter.mpr ⟨hvS, Nat.le_of_not_gt hnot⟩)
          have hdegHR : H.degree v ≤ R.degree v := by
            rw [SimpleGraph.degree, SimpleGraph.degree]
            apply Finset.card_le_card
            intro w hw
            exact (R.mem_neighborFinset v w).mpr
              (hHR ((H.mem_neighborFinset v w).mp hw))
          have hdegRG : R.degree v ≤ G.degree v := by
            rw [SimpleGraph.degree, SimpleGraph.degree]
            apply Finset.card_le_card
            intro w hw
            exact (G.mem_neighborFinset v w).mpr
              (hRG ((R.mem_neighborFinset v w).mp hw))
          have hqdelta : q + 1 ≤ 4 * (q / 2) := by omega
          calc
            H.degree v ≤ R.degree v := hdegHR
            _ ≤ G.degree v := hdegRG
            _ ≤ threshold := hdegG.le
            _ ≤ M * (4 * (q / 2)) := by
              dsimp [threshold]
              gcongr
            _ = K * (q / 2) := by
              simp [K, regularizationLoss]
              ring
        have hHsupp : H.support.ncard ≤ n :=
          (Set.ncard_le_ncard (SimpleGraph.support_mono hHG) (Set.toFinite _)).trans_eq hn
        have hHpow : (H.support.ncard : ℝ) ^ janzerAlpha k ≤
            (n : ℝ) ^ janzerAlpha k := by
          apply Real.rpow_le_rpow
          · positivity
          · exact_mod_cast hHsupp
          · exact (janzerAlpha_pos hk).le
        apply cliqueSubdivision_isContained_of_supportAlmostRegular hk G H
          hHG hHedge hmin hmax
        calc
          (localEmbeddingScale k K : ℝ) *
              (H.support.ncard : ℝ) ^ janzerAlpha k ≤
              (L : ℝ) * (n : ℝ) ^ janzerAlpha k := by
            dsimp [L]
            gcongr
          _ ≤ (q / 2 : ℕ) := hdeltaScale
      · have hhigh : e ≤ 2 * D := Nat.le_of_not_gt hlow
        obtain ⟨P, hPeq, hPcard⟩ :=
          Finpartition.exists_equipartition_card_eq S
            (n := M) (by norm_num [M, regularizationParts])
            (by simpa [hScard] using hMn)
        have hPnonempty : P.parts.Nonempty := by
          rw [← Finset.card_pos, hPcard]
          norm_num [M, regularizationParts]
        obtain ⟨B, hBP, hBmax⟩ :=
          Finset.exists_max_image P.parts (crossIncidence G A) hPnonempty
        have hDB : D ≤ M * crossIncidence G A B := by
          calc
            D = ∑ X ∈ P.parts, crossIncidence G A X := by
              symm
              exact sum_crossIncidence_support_parts G A P
            _ ≤ ∑ _X ∈ P.parts, crossIncidence G A B := by
              apply Finset.sum_le_sum
              intro X hXP
              exact hBmax X hXP
            _ = P.parts.card * crossIncidence G A B := by simp
            _ = M * crossIncidence G A B := by rw [hPcard]
        have hBcard : B.card ≤ n / M + 1 := by
          have := hPeq.card_part_le_average_add_one hBP
          simpa [hPcard, hScard] using this
        let J := G.between (A : Set V) (B : Set V)
        have hJG : J ≤ G := SimpleGraph.between_le
        have hcross : crossIncidence G A B ≤ 2 * J.edgeFinset.card := by
          simpa [J] using crossIncidence_le_twice_between_edges G A B
        have hedgeJ : e ≤ 4 * M * J.edgeFinset.card := by
          calc
            e ≤ 2 * D := hhigh
            _ ≤ 2 * (M * crossIncidence G A B) := by gcongr
            _ ≤ 2 * (M * (2 * J.edgeFinset.card)) := by gcongr
            _ = 4 * M * J.edgeFinset.card := by ring
        have hJsuppAB : J.support ⊆ (↑(A ∪ B) : Set V) := by
          intro v hv
          obtain ⟨w, hvw⟩ := J.mem_support.mp hv
          have hside := (SimpleGraph.between_adj.mp hvw).2
          simpa only [Finset.coe_union, Set.mem_union] using hside.elim
            (fun h ↦ Or.inl h.1) (fun h ↦ Or.inr h.1)
        have hJcard : J.support.ncard ≤ A.card + B.card := by
          calc
            J.support.ncard ≤ (↑(A ∪ B) : Set V).ncard :=
              Set.ncard_le_ncard hJsuppAB (Set.toFinite _)
            _ = (A ∪ B).card := Set.ncard_coe_finset _
            _ ≤ A.card + B.card := Finset.card_union_le A B
        have hMB : M * B.card ≤ 2 * n := by
          calc
            M * B.card ≤ M * (n / M + 1) := by gcongr
            _ = M * (n / M) + M := by ring
            _ ≤ n + M := by gcongr; exact Nat.mul_div_le n M
            _ ≤ 2 * n := by omega
        have hJsize : M * J.support.ncard ≤ 4 * n := by
          calc
            M * J.support.ncard ≤ M * (A.card + B.card) := by gcongr
            _ = M * A.card + M * B.card := by ring
            _ ≤ 2 * n + 2 * n := by gcongr
            _ = 4 * n := by ring
        have hJlt : J.support.ncard < n := by
          have hMfour : 4 < M := by norm_num [M, regularizationParts]
          nlinarith
        have hcontract := regularization_rpow_contraction
          (k := k) hk hJsize
        have hJdense : (C : ℝ) *
            (J.support.ncard : ℝ) ^ (1 + janzerAlpha k) ≤
              J.edgeFinset.card := by
          have hedgeJR : (e : ℝ) ≤
              (4 * M : ℕ) * J.edgeFinset.card := by exact_mod_cast hedgeJ
          have hCnonneg : (0 : ℝ) ≤ C := by positivity
          have hmul : (4 * M : ℝ) *
              ((C : ℝ) * (J.support.ncard : ℝ) ^
                (1 + janzerAlpha k)) ≤
              (4 * M : ℝ) * J.edgeFinset.card := by
            calc
              (4 * M : ℝ) * ((C : ℝ) *
                  (J.support.ncard : ℝ) ^ (1 + janzerAlpha k)) =
                  (C : ℝ) * ((4 * M : ℝ) *
                    (J.support.ncard : ℝ) ^ (1 + janzerAlpha k)) := by ring
              _ ≤ (C : ℝ) * (n : ℝ) ^ (1 + janzerAlpha k) := by gcongr
              _ ≤ e := hdense'
              _ ≤ (4 * M : ℝ) * J.edgeFinset.card := by
                simpa using hedgeJR
          have h4M : (0 : ℝ) < 4 * M := by
            exact_mod_cast (mul_pos (by norm_num : 0 < 4)
              (by norm_num [M, regularizationParts] : 0 < M))
          exact le_of_mul_le_mul_left hmul h4M
        have hJedge : J.edgeSet.Nonempty := by
          have hepos : 0 < e := Finset.card_pos.mpr hedgeFin
          have : 0 < J.edgeFinset.card := by
            by_contra hz
            have hz' : J.edgeFinset.card = 0 := Nat.eq_zero_of_not_pos hz
            rw [hz'] at hedgeJ
            simp at hedgeJ
            omega
          simpa [SimpleGraph.edgeFinset] using (Finset.card_pos.mp this)
        have hJcopy := ih J.support.ncard hJlt J hJedge rfl (by
          have hJeq : J.edgeSet.ncard = J.edgeFinset.card :=
            Set.ncard_eq_toFinset_card' J.edgeSet
          simpa [C, hJeq] using hJdense)
        exact hJcopy.trans (SimpleGraph.Copy.ofLE J G hJG).isContained

/-- Contrapositive packaging of the forcing theorem: every subdivision-free
finite graph has at most the asserted number of edges. -/
theorem edge_card_le_janzer_power
    {k : ℕ} (hk : 3 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : (cliqueSubdivision k).Free G) :
    (G.edgeFinset.card : ℝ) ≤ (denseForcingConstant k : ℝ) *
      (Fintype.card V : ℝ) ^ (1 + janzerAlpha k) := by
  classical
  by_contra hnot
  have hstrict : (denseForcingConstant k : ℝ) *
      (Fintype.card V : ℝ) ^ (1 + janzerAlpha k) <
        G.edgeFinset.card := lt_of_not_ge hnot
  have hedgeFin : G.edgeFinset.Nonempty := by
    apply Finset.card_pos.mp
    have hnonneg : (0 : ℝ) ≤ (denseForcingConstant k : ℝ) *
        (Fintype.card V : ℝ) ^ (1 + janzerAlpha k) := by positivity
    have : (0 : ℝ) < G.edgeFinset.card := hnonneg.trans_lt hstrict
    exact_mod_cast this
  have hedge : G.edgeSet.Nonempty := by
    simpa [SimpleGraph.edgeFinset] using hedgeFin
  have hsupp : G.support.ncard ≤ Fintype.card V := by
    have := Set.ncard_le_ncard (show G.support ⊆ Set.univ from Set.subset_univ _)
      (Set.toFinite _)
    simpa using this
  have hpow : (G.support.ncard : ℝ) ^ (1 + janzerAlpha k) ≤
      (Fintype.card V : ℝ) ^ (1 + janzerAlpha k) := by
    apply Real.rpow_le_rpow
    · positivity
    · exact_mod_cast hsupp
    · exact (one_add_janzerAlpha_pos hk).le
  have hdense : (denseForcingConstant k : ℝ) *
      (G.support.ncard : ℝ) ^ (1 + janzerAlpha k) ≤
        (G.edgeSet.ncard : ℝ) := by
    have heq : G.edgeSet.ncard = G.edgeFinset.card :=
      Set.ncard_eq_toFinset_card' G.edgeSet
    rw [heq]
    exact (mul_le_mul_of_nonneg_left hpow (by positivity)).trans hstrict.le
  exact hfree (cliqueSubdivision_isContained_of_denseSupport hk G hedge hdense)

end FiniteHost

/-! ## Extremal-number and asymptotic packaging -/

theorem cliqueSubdivision_extremal_bound {k n : ℕ} (hk : 3 ≤ k) :
    extremalGrowth (cliqueSubdivision k) n ≤
      (denseForcingConstant k : ℝ) *
        polynomialGrowth (1 + janzerAlpha k) n := by
  have hnonneg : 0 ≤ (denseForcingConstant k : ℝ) *
      polynomialGrowth (1 + janzerAlpha k) n := by
    dsimp [polynomialGrowth]
    positivity
  have hext :
      (SimpleGraph.extremalNumber (Fintype.card (Fin n))
        (cliqueSubdivision k) : ℝ) ≤
        (denseForcingConstant k : ℝ) *
          polynomialGrowth (1 + janzerAlpha k) n := by
    apply (SimpleGraph.extremalNumber_le_iff_of_nonneg
      (V := Fin n) (cliqueSubdivision k) hnonneg).2
    intro G _ hfree
    simpa only [polynomialGrowth, Fintype.card_fin] using
      edge_card_le_janzer_power hk G hfree
  simpa [extremalGrowth] using hext

/-- Janzer's sharp exponent for the one-subdivision of `K_k`. -/
theorem cliqueSubdivision_extremal_upper {k : ℕ} (hk : 3 ≤ k) :
    extremalGrowth (cliqueSubdivision k) =O[atTop]
      polynomialGrowth (3 / 2 - janzerSaving k) := by
  rw [← janzerExponent_eq hk]
  refine IsBigO.of_bound (denseForcingConstant k : ℝ) ?_
  filter_upwards [] with n
  have hf : 0 ≤ extremalGrowth (cliqueSubdivision k) n := by
    dsimp [extremalGrowth]
    positivity
  have hg : 0 ≤ polynomialGrowth (1 + janzerAlpha k) n := by
    dsimp [polynomialGrowth]
    positivity
  simpa [Real.norm_eq_abs, abs_of_nonneg hf, abs_of_nonneg hg] using
    cliqueSubdivision_extremal_bound (n := n) hk

/-- The literal assertion asked in Erdős Problem 1021. -/
def ErdosProblem1021 : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∃ c : ℝ, 0 < c ∧
    extremalGrowth (cliqueSubdivision k) =O[atTop]
      polynomialGrowth (3 / 2 - c)

/-- **Resolution of Erdős Problem 1021 (Conlon--Lee; sharp exponent due to
Janzer).**  One may take `c_k = 1 / (4k - 6)`. -/
theorem erdosProblem1021 : ErdosProblem1021 := by
  intro k hk
  exact ⟨janzerSaving k, janzerSaving_pos hk,
    cliqueSubdivision_extremal_upper hk⟩

#print axioms erdosProblem1021

end Erdos1021
