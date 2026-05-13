/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 621.
https://www.erdosproblems.com/forum/thread/621

Informal authors:
- Sergey Norin
- Yue Ru Sun

Formal authors:
- Aristotle
- Lorenzo Luccioli

URLs:
- https://www.erdosproblems.com/forum/thread/621#post-5605
- https://gist.githubusercontent.com/LorenzoLuccioli/71247a0c86fa35cb1e000160baef0bba/raw/eff1f49238af6ae9119b879ee91ff36ec6ee6b31/Erdos621.lean
-/
/-
# Triangle-independent sets vs. cuts (Norin–Sun)

Consolidated formalization of the main result from:
  Sergey Norin and Yue Ru Sun, "Triangle-independent sets vs. cuts"

**Main Theorem (Theorem 1.3):** For every finite simple graph G,
  α₁(G) + τ_B(G) ≤ |V(G)|² / 4.

**Erdős–Gallai–Tuza Conjecture:**
  α₁(G) + τ₁(G) ≤ |V(G)|² / 4.

All proofs depend only on standard Lean axioms
(`propext`, `Classical.choice`, `Quot.sound`).
-/
import Mathlib

namespace Erdos621


set_option linter.deprecated false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.longLine false
set_option linter.style.maxHeartbeats false
set_option linter.style.multiGoal false
set_option linter.style.openClassical false
set_option linter.style.refine false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Finset SimpleGraph BigOperators
open scoped Classical

noncomputable section


/-! ================================================================
    From Trigraph
    ================================================================ -/

/-
# Triangle-free Trigraphs

A triangle-free trigraph G = (V, C, S) consists of:
- A finite vertex set V
- Edge sets C ("colored") and S ("special") that are disjoint
- The triangle-free condition: if uv, uw ∈ S then vw ∉ C ∪ S

This is the main technical framework for the proof of Theorem 1.3.
-/


/-- A triangle-free trigraph on vertex type V.
    We represent it using indicator functions c, s : V → V → ℤ
    for the C-edges and S-edges respectively, with n = 1 - c - s being
    the non-edge indicator. -/
structure Trigraph (V : Type*) where
  /-- Indicator function for C-edges (the "colored" edges) -/
  c : V → V → ℤ
  /-- Indicator function for S-edges (the "special/triangle-independent" edges) -/
  s : V → V → ℤ
  /-- c takes values in {0,1} -/
  c_nonneg : ∀ u v, 0 ≤ c u v
  c_le_one : ∀ u v, c u v ≤ 1
  /-- s takes values in {0,1} -/
  s_nonneg : ∀ u v, 0 ≤ s u v
  s_le_one : ∀ u v, s u v ≤ 1
  /-- c and s are symmetric -/
  c_symm : ∀ u v, c u v = c v u
  s_symm : ∀ u v, s u v = s v u
  /-- No self-loops -/
  c_self : ∀ v, c v v = 0
  s_self : ∀ v, s v v = 0
  /-- C and S are disjoint: c(uv) + s(uv) ≤ 1 -/
  cs_disjoint : ∀ u v, c u v + s u v ≤ 1
  /-- Triangle-free condition: if uv, uw ∈ S then vw ∉ C ∪ S,
      equivalently s(uv) * s(uw) * (c(vw) + s(vw)) = 0 -/
  triangle_free : ∀ u v w, s u v * s u w * (c v w + s v w) = 0

namespace Trigraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The non-edge indicator function: n(u,v) = 1 - c(u,v) - s(u,v).
    Note n(v,v) = 1 for all v. -/
def n (G : Trigraph V) (u v : V) : ℤ := 1 - G.c u v - G.s u v

lemma n_nonneg (G : Trigraph V) (u v : V) : 0 ≤ G.n u v := by
  unfold n; linarith [G.cs_disjoint u v]

lemma n_le_one (G : Trigraph V) (u v : V) : G.n u v ≤ 1 := by
  unfold n; linarith [G.c_nonneg u v, G.s_nonneg u v]

lemma n_symm (G : Trigraph V) (u v : V) : G.n u v = G.n v u := by
  unfold n; rw [G.c_symm, G.s_symm]

lemma c_add_s_add_n (G : Trigraph V) (u v : V) :
    G.c u v + G.s u v + G.n u v = 1 := by
  unfold n; ring_nf

lemma n_self (G : Trigraph V) (v : V) : G.n v v = 1 := by
  unfold n; rw [G.c_self, G.s_self]; ring_nf

/-- Key consequence of triangle-free: s(uv)*s(vw) = s(uv)*s(vw)*n(uw) -/
lemma s_s_eq_s_s_n (G : Trigraph V) (u v w : V) :
    G.s u v * G.s v w = G.s u v * G.s v w * G.n u w := by
  have h := G.triangle_free v u w
  rw [G.s_symm v u] at h
  unfold n
  nlinarith [G.s_nonneg u v, G.s_nonneg v w, G.c_nonneg u w, G.s_nonneg u w,
             G.cs_disjoint u w,
             sq_nonneg (G.s u v * G.s v w),
             sq_nonneg (G.c u w + G.s u w)]

/-- |S| = sum of s(u,v) over ordered pairs, divided by 2 -/
def S_size (G : Trigraph V) : ℤ :=
  (∑ u : V, ∑ v : V, G.s u v) / 2

/-! ## Counting quantities from the paper -/

/-- P₄(G) = Σ_{(u,v,w,x)} s(uv)·s(vw)·s(wx)·(n(xu) + c(xu)) -/
def P4 (G : Trigraph V) : ℤ :=
  ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V,
    G.s u v * G.s v w * G.s w x * (G.n x u + G.c x u)

/-- C₄(G) = Σ_{(u,v,w,x)} s(uv)·s(vw)·s(wx)·s(xu) -/
def C4 (G : Trigraph V) : ℤ :=
  ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V,
    G.s u v * G.s v w * G.s w x * G.s x u

/-- K₁,₃(G) = Σ_{(u,v,w,x)} s(uv)·s(uw)·s(ux) -/
def K13 (G : Trigraph V) : ℤ :=
  ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V,
    G.s u v * G.s u w * G.s u x

/-- D(G) = Σ_{(u,v,w,x)} (n(uv)+c(uv))·s(uw)·s(ux)·n(vw)·n(vx) -/
def D (G : Trigraph V) : ℤ :=
  ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V,
    (G.n u v + G.c u v) * G.s u w * G.s u x * G.n v w * G.n v x

/-- R(G) = Σ_{(u,v,w,x)} s(uv)·s(uw)·n(wx)·c(vx) -/
def R (G : Trigraph V) : ℤ :=
  ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V,
    G.s u v * G.s u w * G.n w x * G.c v x

end Trigraph


/-! ================================================================
    From Defs
    ================================================================ -/

/-
# Triangle-independent sets vs. cuts

Formalization of the main result from:
  Sergey Norin and Yue Ru Sun,
  "Triangle-independent sets vs. cuts"

Main theorem: For every finite simple graph G,
  α₁(G) + τ_B(G) ≤ |V(G)|² / 4
where α₁(G) is the maximum size of a triangle-independent edge set
and τ_B(G) is the minimum number of edges to delete to make G bipartite.
-/


variable {V : Type*} [Fintype V] [DecidableEq V]

namespace TriangleIndep

/-! ## Key Definitions -/

/-- A set of edges `T` in a graph `G` is *triangle-independent* if `T ⊆ E(G)` and
    `T` contains at most one edge from each triangle in `G`. -/
def IsTriangleIndependent (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset (Sym2 V)) : Prop :=
  T ⊆ G.edgeFinset ∧
  ∀ u v w : V, G.Adj u v → G.Adj v w → G.Adj u w →
    ({s(u, v), s(v, w), s(u, w)} ∩ T).card ≤ 1

/-- `alpha1 G` is α₁(G), the maximum cardinality of a triangle-independent edge set
    in the graph `G`. -/
noncomputable def alpha1 (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.edgeFinset.powerset.filter (IsTriangleIndependent G)).sup Finset.card

/-- `tauB G` is τ_B(G), the minimum number of edges one must delete from `G`
    to obtain a bipartite graph. -/
noncomputable def tauB (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf ((fun F => F.card) ''
    {F : Finset (Sym2 V) | F ⊆ G.edgeFinset ∧
      (G.deleteEdges (F : Set (Sym2 V))).IsBipartite})

end TriangleIndep


/-! ================================================================
    From P4LeD
    ================================================================ -/

/-
# Proof that P₄(G) ≤ D(G) for triangle-free trigraphs (Lemma 2.2, part 2)

The proof uses a Cauchy-Schwarz-like argument:
1. Define the cross term: A = Σ (n+c)(uv) * s(uw) * n(vw) * s(vx) * n(ux)
2. Show SOS := Σ (n+c)(uv) * [Σ_w (s(uw)n(vw) - s(vw)n(uw))]² = 2D - 2A
3. Since SOS ≥ 0, we get A ≤ D
4. Show P₄ ≤ A using triangle-free condition and s ≤ 1
5. Conclude P₄ ≤ D
-/


namespace Trigraph

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 1600000

/-- The cross term A from the expansion of the SOS expression. -/
def crossTermA (G : Trigraph V) : ℤ :=
  ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V,
    (G.n u v + G.c u v) * G.s u w * G.n v w * G.s v x * G.n u x

/-
SOS identity: the SOS expression equals 2D - 2A
-/
lemma sos_eq_2D_sub_2A (G : Trigraph V) :
    ∑ u : V, ∑ v : V, (G.n u v + G.c u v) *
      (∑ w : V, (G.s u w * G.n v w - G.s v w * G.n u w)) ^ 2 =
    2 * G.D - 2 * G.crossTermA := by
  simp +decide only [sum_sub_distrib, pow_two, mul_sub, sub_mul];
  simp +decide only [mul_comm, Finset.mul_sum _ _ _, mul_left_comm];
  simp +decide only [mul_assoc, mul_left_comm, D, mul_comm, crossTermA];
  rw [ show ∑ x : V, ∑ x_1 : V, ∑ x_2 : V, ∑ x_3 : V, G.n x x_2 * ( G.n x x_3 * ( ( G.n x x_1 + G.c x x_1 ) * ( G.s x_1 x_2 * G.s x_1 x_3 ) ) ) = ∑ x : V, ∑ x_1 : V, ∑ x_2 : V, ∑ x_3 : V, G.n x_1 x_2 * ( G.n x_1 x_3 * ( ( G.n x x_1 + G.c x x_1 ) * ( G.s x x_2 * G.s x x_3 ) ) ) from ?_ ] ; ring_nf;
  · congr! 3;
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring_nf );
  · rw [ Finset.sum_comm ];
    simp +decide only [n_symm, c_symm]

/-- A ≤ D, since the SOS is nonneg -/
lemma crossTermA_le_D (G : Trigraph V) : G.crossTermA ≤ G.D := by
  have h : 0 ≤ ∑ u : V, ∑ v : V, (G.n u v + G.c u v) *
      (∑ w : V, (G.s u w * G.n v w - G.s v w * G.n u w)) ^ 2 := by
    apply Finset.sum_nonneg; intro u _
    apply Finset.sum_nonneg; intro v _
    apply mul_nonneg
    · linarith [G.n_nonneg u v, G.c_nonneg u v]
    · exact sq_nonneg _
  linarith [G.sos_eq_2D_sub_2A]

/-
P₄ ≤ A using triangle-free and s ≤ 1
-/
lemma P4_le_crossTermA (G : Trigraph V) : G.P4 ≤ G.crossTermA := by
  -- Consider the intermediate sum $B$:
  set B := ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V,
    (G.n u v + G.c u v) * G.s u w * G.n v w * G.s v x * G.n u x * G.s x w;
  -- We need to show that $B \leq \text{crossTermA}$.
  have h_B_le_crossTermA : B ≤ G.crossTermA := by
    refine' Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun v hv => Finset.sum_le_sum fun w hw => Finset.sum_le_sum fun x hx => _;
    refine' mul_le_of_le_one_right _ _;
    · apply_rules [ mul_nonneg, n_nonneg, c_nonneg, s_nonneg ];
      exact add_nonneg ( n_nonneg G u v ) ( c_nonneg G u v );
    · exact G.s_le_one x w;
  -- Using the triangle-free condition, we can simplify the expression for $B$.
  have h_B_simplified : B = ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V,
    (G.n u v + G.c u v) * G.s u w * G.s v x * G.s x w := by
      have h_B_simplified : ∀ u v w x : V, G.s v x * G.s x w * G.n v w = G.s v x * G.s x w := by
        intro u v w x
        have h_triangle_free : G.s v x * G.s x w * (G.c v w + G.s v w) = 0 := by
          exact G.triangle_free x v w ▸ by simp +decide [ G.s_symm ] ;
        have h_simplify : G.s v x * G.s x w * G.n v w = G.s v x * G.s x w := by
          simp_all +decide [ Trigraph.n ];
          grind
        exact h_simplify;
      refine' Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => Finset.sum_congr rfl fun w hw => Finset.sum_congr rfl fun x hx => _;
      grind +suggestions;
  convert h_B_le_crossTermA using 1;
  rw [ h_B_simplified ];
  unfold Trigraph.P4;
  simp +decide only [mul_comm];
  simp +decide only [← sum_product'];
  apply Finset.sum_bij (fun x _ => (x.2.2.2, x.1, x.2.2.1, x.2.1)) _ _ _ _ <;> simp +decide [ mul_assoc, mul_comm, mul_left_comm ];
  exact fun u v w x => Or.inl <| Or.inl <| Or.inl <| G.s_symm _ _

/-- **Lemma 2.2, part 2:** P₄(G) ≤ D(G). -/
theorem P4_le_D (G : Trigraph V) : G.P4 ≤ G.D :=
  le_trans G.P4_le_crossTermA G.crossTermA_le_D

end Trigraph


/-! ================================================================
    From CauchySchwarz
    ================================================================ -/

/-
# Cauchy-Schwarz inequalities for trigraphs (Lemma 2.2)

We prove:
  (1) P₄(G) + C₄(G) ≤ K₁,₃(G)
  (2) P₄(G) ≤ D(G)
-/


namespace Trigraph

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 800000

/-! ### Part 1: P₄ + C₄ ≤ K₁,₃ -/

/-- P₄ + C₄ = Σ s(uv)·s(vw)·s(wx) -/
lemma P4_add_C4_eq (G : Trigraph V) :
    G.P4 + G.C4 = ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V,
      G.s u v * G.s v w * G.s w x := by
  simp only [P4, C4, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro u _
  apply Finset.sum_congr rfl; intro v _
  apply Finset.sum_congr rfl; intro w _
  apply Finset.sum_congr rfl; intro x _
  simp only [Trigraph.n]
  ring_nf

/-- The sum-of-squares expression that gives 2(K₁,₃ - P₄ - C₄) ≥ 0 -/
lemma K13_minus_P4_C4_eq_half_sos (G : Trigraph V) :
    2 * (G.K13 - G.P4 - G.C4) =
      ∑ u : V, ∑ v : V, G.s u v *
        (∑ w : V, (G.s u w - G.s v w)) ^ 2 := by
  -- proved by subagent
  have h_expand : ∑ u : V, ∑ v : V, G.s u v * (∑ w : V, (G.s u w - G.s v w))^2 = ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, G.s u v * (G.s u w - G.s v w) * (G.s u x - G.s v x) := by
    simp +decide only [pow_two, Finset.mul_sum _ _ _, mul_comm, mul_assoc]
  have h_expand_further : ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, G.s u v * (G.s u w - G.s v w) * (G.s u x - G.s v x) = ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, (G.s u v * G.s u w * G.s u x + G.s u v * G.s v w * G.s v x - G.s u v * G.s u w * G.s v x - G.s u v * G.s v w * G.s u x) := by
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring_nf
  have h_simplify : ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, (G.s u v * G.s u w * G.s u x + G.s u v * G.s v w * G.s v x - G.s u v * G.s u w * G.s v x - G.s u v * G.s v w * G.s u x) = 2 * ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, G.s u v * G.s u w * G.s u x - 2 * ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, G.s u v * G.s u w * G.s v x := by
    have h_simplify : ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, G.s u v * G.s v w * G.s v x = ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, G.s u v * G.s u w * G.s u x := by
      rw [ Finset.sum_comm ]
      simp +decide only [s_symm]
    have h_simplify2 : ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, G.s u v * G.s v w * G.s u x = ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, G.s u v * G.s u w * G.s v x := by
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring_nf )
    simp +decide [ Finset.sum_add_distrib, Finset.sum_sub_distrib, two_mul, * ]
    linarith
  have h_combine : ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, G.s u v * G.s u w * G.s u x = G.K13 ∧ ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, G.s u v * G.s u w * G.s v x = G.P4 + G.C4 := by
    constructor
    · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring_nf
    · rw [ P4_add_C4_eq ]
      simp +decide only [← sum_product']
      apply Finset.sum_bij (fun x _ => (x.2.2.1, x.1, x.2.1, x.2.2.2))
      · simp +decide
      · grind
      · simp +decide
      · simp +decide [ mul_assoc, mul_comm, mul_left_comm, G.s_symm ]
  grind

/-- **Lemma 2.2, part 1:** P₄(G) + C₄(G) ≤ K₁,₃(G). -/
theorem P4_add_C4_le_K13 (G : Trigraph V) : G.P4 + G.C4 ≤ G.K13 := by
  suffices h : 0 ≤ 2 * (G.K13 - G.P4 - G.C4) by linarith
  rw [K13_minus_P4_C4_eq_half_sos]
  apply Finset.sum_nonneg
  intro u _
  apply Finset.sum_nonneg
  intro v _
  exact mul_nonneg (G.s_nonneg u v) (sq_nonneg _)

/-! ### Part 2: P₄ ≤ D -/

/-- **Lemma 2.2, part 2:** P₄(G) ≤ D(G). -/
theorem P4_add_C4_le_K13_and_P4_le_D (G : Trigraph V) : G.P4 ≤ G.D :=
  Trigraph.P4_le_D G

end Trigraph


/-! ================================================================
    From Fbound3Helpers
    ================================================================ -/

/-
# Helper lemmas for the fbound3 identity (equation e:fbound3)

The proof of fbound3 follows the paper's decomposition:
1. Algebraic rewriting (fbound4)
2. aux1 (already proved in BigSum.lean)
3. Symmetrization using triangle-free condition
4. Splitting the remaining sum into P₄ + K₁,₃ + D + R
-/


namespace Trigraph

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 1600000

/-
(e:fbound4): Algebraic rewriting of the LHS of fbound3.
    LHS = Σ s(uv)(s(uw)+s(vw))(n(wx)+s(wx)+c(wx)·s(ux)+c(wx)·s(vx))
-/
lemma fbound4 (G : Trigraph V) :
    ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, G.s u v * (G.s u w + G.s v w)
    - ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V,
        G.s u v * G.c w x * (G.s u w + G.s v w) * (1 - G.s u x - G.s v x) =
    ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V,
        G.s u v * (G.s u w + G.s v w) *
        (G.n w x + G.s w x + G.c w x * G.s u x + G.c w x * G.s v x) := by
  rw [ ← Finset.sum_sub_distrib ];
  refine' Finset.sum_congr rfl fun u hu => _;
  rw [ ← Finset.sum_sub_distrib ] ; congr ; ext v ; rw [ ← Finset.sum_sub_distrib ] ; congr ; ext w ; rw [ ← Finset.sum_sub_distrib ] ; congr ; ext x ; ring_nf;
  unfold Trigraph.n; ring_nf;

/-
Triangle-free kills c(wx)·s(ux)·s(uw): this product is always 0.
    From triangle_free u x w: s(ux)·s(uw)·(c(xw)+s(xw)) = 0,
    hence s(uw)·s(ux)·c(wx) = 0 since c(wx) ≤ c(xw)+s(xw).
-/
lemma c_s_s_vanish (G : Trigraph V) (u w x : V) :
    G.s u w * G.s u x * G.c w x = 0 := by
  by_contra h_contra;
  have := G.triangle_free u x w;
  simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
  exact h_contra.1 ( by linarith [ G.c_symm w x, G.s_symm w x, G.c_nonneg w x, G.s_nonneg w x ] )

/-
Symmetrization: Σ s(uv)(s(uw)+s(vw))(n(wx)+c(wx)s(ux)+c(wx)s(vx))
    = 2·Σ s(uv)s(uw)(n(wx)+c(wx)s(vx))
    Uses c_s_s_vanish to eliminate c(wx)s(ux)s(uw) terms,
    and swaps u↔v in the s(vw) part.
-/
lemma symmetrize_aux2 (G : Trigraph V) :
    ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V,
      G.s u v * (G.s u w + G.s v w) *
      (G.n w x + G.c w x * G.s u x + G.c w x * G.s v x) =
    2 * ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V,
      G.s u v * G.s u w * (G.n w x + G.c w x * G.s v x) := by
  -- Apply the c_s_s_vanish lemma to each term in the sum.
  have h_vanish : ∀ u w x, G.s u w * G.s u x * G.c w x = 0 := by
    exact fun u w x => G.c_s_s_vanish u w x;
  -- Apply the c_s_s_vanish lemma to each term in the sum to simplify it.
  have h_simp : ∀ u v w x, G.s u v * (G.s u w + G.s v w) * (G.n w x + G.c w x * G.s u x + G.c w x * G.s v x) = G.s u v * G.s u w * (G.n w x + G.c w x * G.s v x) + G.s u v * G.s v w * (G.n w x + G.c w x * G.s u x) := by
    grind;
  simp +decide only [h_simp, sum_add_distrib, two_mul];
  simp +decide only [← sum_product'];
  refine' congr rfl ( Finset.sum_bij ( fun x _ => ( x.2.1, x.1, x.2.2.1, x.2.2.2 ) ) _ _ _ _ ) <;> simp +decide;
  exact fun u v w x => Or.inl <| Or.inl <| G.s_symm u v

/-
Part (a) of aux2 splitting: Σ s(uv)s(uw)s(vx)(1-s(wx)) = P₄.
    Uses triangle-free to simplify.
-/
lemma sum_svx_one_sub_swx_eq_P4 (G : Trigraph V) :
    ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V,
      G.s u v * G.s u w * G.s v x * (1 - G.s w x) = G.P4 := by
  -- By definition of $P₄$, we know that
  have hP4 : G.P4 = ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, G.s u v * G.s v w * G.s w x * (1 - G.s x u) := by
    refine' Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => Finset.sum_congr rfl fun w hw => Finset.sum_congr rfl fun x hx => _;
    unfold Trigraph.n; ring_nf;
  simp +decide only [mul_sub, mul_one, hP4];
  simp +decide only [← sum_product'];
  apply Finset.sum_bij (fun x _ => (x.2.2.2, x.2.1, x.1, x.2.2.1));
  · grind;
  · aesop;
  · simp +decide;
  · simp +decide [ mul_assoc, mul_comm, mul_left_comm, G.s_symm ]

/-
Part (b) of aux2 splitting: Σ s(uv)s(uw)n(vx)n(wx) = K₁,₃ + D.
    Uses triangle-free and relabeling v↔x.
-/
lemma sum_nvx_nwx_eq_K13_D (G : Trigraph V) :
    ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V,
      G.s u v * G.s u w * G.n v x * G.n w x = G.K13 + G.D := by
  unfold K13 D;
  -- Let's simplify the expression by factoring out common terms and using the definitions of $K13$ and $D$.
  have h_simp : ∀ (u v w x : V), G.s u v * G.s u w * G.n v x * G.n w x = G.s u v * G.s u w * G.s u x + G.s u v * G.s u w * (G.n u x + G.c u x) * G.n v x * G.n w x := by
    grind +suggestions;
  simp +decide only [h_simp, sum_add_distrib];
  simp +decide only [← sum_product'];
  refine' congr rfl ( Finset.sum_bij ( fun x _ => ( x.1, x.2.2.2, x.2.2.1, x.2.1 ) ) _ _ _ _ ) <;> simp +decide;
  simp +decide [ mul_assoc, mul_comm, mul_left_comm, Trigraph.n_symm ]

/-
Part (c): Σ s(uv)s(uw)c(vx)n(wx) = R by definition.
-/
lemma sum_cvx_nwx_eq_R (G : Trigraph V) :
    ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V,
      G.s u v * G.s u w * G.c v x * G.n w x = G.R := by
  -- By definition of $R$, we know that
  simp [Trigraph.R];
  ac_rfl

/-
Combined: Σ s(uv)s(uw)(n(wx)+c(wx)s(vx)) = P₄ + K₁,₃ + D + R.
-/
lemma aux2_combined (G : Trigraph V) :
    ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V,
      G.s u v * G.s u w * (G.n w x + G.c w x * G.s v x) =
    G.P4 + G.K13 + G.D + G.R := by
  have h1 := sum_svx_one_sub_swx_eq_P4 G
  have h2 := sum_nvx_nwx_eq_K13_D G
  have h3 := sum_cvx_nwx_eq_R G
  -- n(wx) + c(wx)s(vx) = s(vx)(n(wx)+c(wx)) + n(vx)n(wx) + c(vx)n(wx)
  -- = s(vx)(1-s(wx)) + n(vx)n(wx) + c(vx)n(wx)
  convert congr_arg₂ ( · + · ) ( congr_arg₂ ( · + · ) h2 h1 ) h3 using 1;
  · simp +decide [ ← mul_assoc, ← Finset.sum_add_distrib, n ];
    refine' Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => Finset.sum_congr rfl fun w hw => Finset.sum_congr rfl fun x hx => _;
    ring_nf;
  · grind

end Trigraph


/-! ================================================================
    From BigSum
    ================================================================ -/

/-
# Big sum identity (Lemma 2.3)

Proves: 2·LHS_c + B = (card V)²·S_total - 6P₄ - 2C₄ - 2K₁,₃ - 4D - 4R
-/


namespace Trigraph

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 1600000

def S_total' (G : Trigraph V) : ℤ :=
  ∑ u : V, ∑ v : V, G.s u v

/-- B = (card V)²·S_total - 2·degSum + thirdPiece -/
lemma B_expansion (G : Trigraph V) :
    ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V,
      G.s u v * (1 - G.s u w - G.s v w) * (1 - G.s u x - G.s v x) =
    (Fintype.card V) ^ 2 * G.S_total'
    - 2 * (∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, G.s u v * (G.s u w + G.s v w))
    + (∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V,
        G.s u v * (G.s u w + G.s v w) * (G.s u x + G.s v x)) := by
  have h_expand : ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, G.s u v * (1 - G.s u w - G.s v w) * (1 - G.s u x - G.s v x) = ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, (G.s u v - G.s u v * G.s u w - G.s u v * G.s v w - G.s u v * G.s u x - G.s u v * G.s v x + G.s u v * G.s u w * G.s u x + G.s u v * G.s u w * G.s v x + G.s u v * G.s v w * G.s u x + G.s u v * G.s v w * G.s v x) := by
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring_nf;
  simp +decide only [h_expand, sum_add_distrib, sum_sub_distrib];
  simp +decide only [mul_add, sum_add_distrib];
  simp +decide only [sum_const, card_univ, nsmul_eq_mul, mul_assoc, S_total', add_mul, sum_add_distrib];
  simp +decide only [← Finset.mul_sum _ _ _, ← sum_mul] ; ring_nf

/-- The third piece = 2·K₁,₃ + 2·(P₄+C₄) -/
lemma third_piece_eq (G : Trigraph V) :
    ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V,
      G.s u v * (G.s u w + G.s v w) * (G.s u x + G.s v x) =
    2 * G.K13 + 2 * (G.P4 + G.C4) := by
  simp +decide only [mul_add, add_mul, sum_add_distrib];
  have hP4_C4 : ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, G.s u v * G.s v w * G.s w x = G.P4 + G.C4 := by
    convert P4_add_C4_eq G |> Eq.symm using 1;
  have hP4_C4' : ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, G.s u v * G.s v w * G.s u x = G.P4 + G.C4 := by
    rw [ ← hP4_C4 ];
    simp +decide only [sum_sigma'];
    apply Finset.sum_bij (fun x _ => ⟨x.snd.snd.fst, x.snd.fst, x.fst, x.snd.snd.snd⟩);
    · aesop;
    · grind;
    · aesop;
    · simp +decide [ mul_assoc, mul_comm, mul_left_comm, Trigraph.s_symm ];
  have hP4_C4'' : ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, G.s u v * G.s u w * G.s u x = G.K13 := by
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring_nf;
  have hP4_C4''' : ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, G.s u v * G.s u w * G.s v x = G.P4 + G.C4 := by
    convert hP4_C4' using 1;
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring_nf );
  have hP4_C4'''' : ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, G.s u v * G.s v w * G.s v x = G.K13 := by
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [ G.s_symm, G.s_symm ] );
  grind

/-- Equation (e:aux1): Σ s(uv)·(s(uw)+s(vw))·s(wx) = 2·(P₄+C₄) -/
lemma aux1 (G : Trigraph V) :
    ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V,
      G.s u v * (G.s u w + G.s v w) * G.s w x = 2 * (G.P4 + G.C4) := by
  have := @P4_add_C4_eq V;
  simp +decide only [mul_add, add_mul, mul_assoc, sum_add_distrib, this];
  rw [ two_mul, ← Finset.sum_comm ];
  simp +decide only [s_symm]

/-- The "fbound3" identity from the paper (equation e:fbound3).
    This is a complex combinatorial identity proved using
    equations (e:fbound4), (e:aux1), and (e:aux2). -/
lemma fbound3 (G : Trigraph V) :
    ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, G.s u v * (G.s u w + G.s v w)
    - ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V,
        G.s u v * G.c w x * (G.s u w + G.s v w) * (1 - G.s u x - G.s v x) =
    4 * G.P4 + 2 * G.C4 + 2 * G.K13 + 2 * G.D + 2 * G.R := by
  -- Step 1: rewrite LHS via fbound4
  rw [fbound4]
  -- Step 2: split into s(wx) part and the rest
  have h_split : ∀ u v w x : V,
      G.s u v * (G.s u w + G.s v w) *
      (G.n w x + G.s w x + G.c w x * G.s u x + G.c w x * G.s v x) =
      G.s u v * (G.s u w + G.s v w) * G.s w x +
      G.s u v * (G.s u w + G.s v w) *
      (G.n w x + G.c w x * G.s u x + G.c w x * G.s v x) := by
    intro u v w x; ring_nf
  simp_rw [h_split, Finset.sum_add_distrib]
  -- Step 3: first sum = 2(P₄+C₄) by aux1
  have h_aux1 := aux1 G
  -- Step 4: second sum = 2·(P₄+K₁,₃+D+R) by symmetrize_aux2 and aux2_combined
  have h_sym := symmetrize_aux2 G
  have h_aux2 := aux2_combined G
  linarith

/-- Lemma 2.3 (reformulated without division) -/
lemma bigsum_identity' (G : Trigraph V) :
    2 * ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V,
      G.s u v * G.c w x * (G.s u w + G.s v w) * (1 - G.s u x - G.s v x) +
    ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V,
      G.s u v * (1 - G.s u w - G.s v w) * (1 - G.s u x - G.s v x) =
    (Fintype.card V) ^ 2 * G.S_total'
    - 6 * G.P4 - 2 * G.C4 - 2 * G.K13 - 4 * G.D - 4 * G.R := by
  have hB := B_expansion G
  have hT := third_piece_eq G
  have hF := fbound3 G
  linarith

end Trigraph


/-! ================================================================
    From FBound
    ================================================================ -/

/-
# The F(G) ≤ |V|²|S| bound

This is the core algebraic inequality from the paper (equation 2.10).
We define F₂ = 2·F and show F₂ ≤ (card V)² · S_total.

The proof combines:
- Identity (e:fbound1)
- Lemma 2.3 (big sum identity)  
- Lemma 2.2 (Cauchy-Schwarz inequalities)
-/


namespace Trigraph

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 1600000

/-- 2·f(u,v,w,x) to avoid fractions -/
def f2 (G : Trigraph V) (u v w x : V) : ℤ :=
  G.s u v * (2 * (3 * G.s w x + G.c w x) * (G.s u w + G.s v w) * (1 - G.s u x - G.s v x)
  + (1 - G.s u w - G.s v w) * (1 - G.s u x - G.s v x)
  + 4 * G.s w x * G.s u w * G.s v x)

/-- F₂(G) = Σ 2·f(u,v,w,x) -/
def F2 (G : Trigraph V) : ℤ :=
  ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, G.f2 u v w x

/-- Total number of S-edges (counting ordered pairs) -/
def S_total (G : Trigraph V) : ℤ :=
  ∑ u : V, ∑ v : V, G.s u v

/-! ### Helper identities -/

/-- (e:fbound1): Σ s(uv)·s(wx)·(s(uw)+s(vw))·(1-s(ux)-s(vx)) = 2·P₄ -/
lemma fbound1 (G : Trigraph V) :
    ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V,
      G.s u v * G.s w x * (G.s u w + G.s v w) * (1 - G.s u x - G.s v x) =
    2 * G.P4 := by
  -- By definition of $P4$, we can expand the left-hand side.
  have h_expand : ∑ u, ∑ v, ∑ w, ∑ x, G.s u v * G.s w x * (G.s u w + G.s v w) * (1 - G.s u x - G.s v x) = ∑ u, ∑ v, ∑ w, ∑ x, G.s u v * G.s u w * G.s w x * (1 - G.s v x) + ∑ u, ∑ v, ∑ w, ∑ x, G.s u v * G.s v w * G.s w x * (1 - G.s u x) := by
    simp +decide only [mul_comm, mul_left_comm, add_mul, mul_add, sub_mul, mul_sub, mul_assoc, ← sum_add_distrib];
    refine' Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => Finset.sum_congr rfl fun w hw => Finset.sum_congr rfl fun x hx => _;
    have := G.triangle_free u w x; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
    rcases this with ( h | h | h ) <;> simp_all +decide [ add_eq_zero_iff_of_nonneg, G.c_nonneg, G.s_nonneg ];
    · have := G.triangle_free v u w; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
      rcases this with ( h' | h' | h' ) <;> have := G.c_add_s_add_n u w <;> simp_all +decide;
      · have := G.triangle_free v w x; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
        rcases this with ( h'' | h'' | h'' ) <;> simp_all +decide [ add_eq_zero_iff_of_nonneg, G.c_nonneg, G.s_nonneg ];
      · have := G.s_symm u v; aesop;
    · have := G.triangle_free v u x; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
      have := G.triangle_free v w x; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
      rcases this with ( h | h | h ) <;> simp_all +decide [ add_eq_zero_iff_of_nonneg, G.c_nonneg, G.s_nonneg ];
  have h_sum1 : ∑ u, ∑ v, ∑ w, ∑ x, G.s u v * G.s u w * G.s w x * (1 - G.s v x) = ∑ u, ∑ v, ∑ w, ∑ x, G.s u v * G.s v w * G.s w x * (1 - G.s u x) := by
    simp +decide only [sum_sigma'];
    apply Finset.sum_bij (fun x _ => ⟨x.snd.fst, x.fst, x.snd.snd.fst, x.snd.snd.snd⟩) _ _ _ _ <;> simp +decide [ Trigraph.s_symm ];
    · grind;
    · exact fun b => ⟨ b.2.1, b.1, b.2.2.1, b.2.2.2, rfl ⟩;
  have h_sum2 : ∑ u, ∑ v, ∑ w, ∑ x, G.s u v * G.s v w * G.s w x * (1 - G.s u x) = G.P4 := by
    refine' Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => Finset.sum_congr rfl fun w hw => Finset.sum_congr rfl fun x hx => _;
    simp +decide [ Trigraph.n, G.c_symm, G.s_symm ];
    exact Or.inl ( by ring_nf );
  grind

/-- The sum Σ s(uv)·s(wx)·s(uw)·s(vx) equals C₄ -/
lemma sum_s_s_s_s_eq_C4 (G : Trigraph V) :
    ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V,
      G.s u v * G.s w x * G.s u w * G.s v x = G.C4 := by
  have h_comm : ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, G.s u v * G.s w x * G.s u w * G.s v x = ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, G.s v u * G.s w x * G.s v w * G.s u x := by
    rw [ Finset.sum_comm ];
  convert h_comm using 1;
  exact Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => Finset.sum_congr rfl fun w hw => Finset.sum_congr rfl fun x hx => by rw [ G.s_symm u v, G.s_symm u x ] ; ring_nf;

/-- Lemma 2.3: follows from BigSum.lean's bigsum_identity' -/
lemma bigsum_identity (G : Trigraph V) :
    2 * ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V,
      G.s u v * G.c w x * (G.s u w + G.s v w) * (1 - G.s u x - G.s v x) +
    ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V,
      G.s u v * (1 - G.s u w - G.s v w) * (1 - G.s u x - G.s v x) =
    (Fintype.card V) ^ 2 * G.S_total
    - 6 * G.P4 - 2 * G.C4 - 2 * G.K13 - 4 * G.D - 4 * G.R := by
  exact bigsum_identity' G

/-- R(G) ≥ 0 since it's a sum of products of nonneg terms -/
lemma R_nonneg (G : Trigraph V) : 0 ≤ G.R := by
  unfold R
  apply Finset.sum_nonneg; intro u _
  apply Finset.sum_nonneg; intro v _
  apply Finset.sum_nonneg; intro w _
  apply Finset.sum_nonneg; intro x _
  exact mul_nonneg (mul_nonneg (mul_nonneg (G.s_nonneg u v) (G.s_nonneg u w)) (G.n_nonneg w x)) (G.c_nonneg v x)

/-
F₂ expressed in terms of the counting quantities
-/
lemma F2_eq (G : Trigraph V) :
    G.F2 = (Fintype.card V) ^ 2 * G.S_total
    + 2 * (G.P4 + G.C4 - G.K13)
    + 4 * (G.P4 - G.D)
    - 4 * G.R := by
  -- Apply the definitions of `A`, `B`, and `C` from the provided solution.
  have h_F2_decomp : G.F2 = ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, 2 * G.s u v * (3 * G.s w x + G.c w x) * (G.s u w + G.s v w) * (1 - G.s u x - G.s v x) + ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, G.s u v * (1 - G.s u w - G.s v w) * (1 - G.s u x - G.s v x) + ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, 4 * G.s u v * G.s w x * G.s u w * G.s v x := by
    simpa only [ ← sum_add_distrib ] using Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => Finset.sum_congr rfl fun w hw => Finset.sum_congr rfl fun x hx => by unfold Trigraph.f2; ring_nf;
  have h_A : ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, 2 * G.s u v * (3 * G.s w x + G.c w x) * (G.s u w + G.s v w) * (1 - G.s u x - G.s v x) = 12 * G.P4 + 2 * ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, G.s u v * G.c w x * (G.s u w + G.s v w) * (1 - G.s u x - G.s v x) := by
    have h_A : ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, 2 * G.s u v * (3 * G.s w x) * (G.s u w + G.s v w) * (1 - G.s u x - G.s v x) = 12 * G.P4 := by
      convert congr_arg ( · * 6 ) ( fbound1 G ) using 1 ; ring_nf;
      · simp +decide only [Finset.sum_mul _ _ _] ; congr ; ext ; congr ; ext ; congr ; ext ; congr ; ext ; ring_nf;
      · ring_nf;
    simp +decide only [mul_add, mul_left_comm, mul_assoc, Finset.mul_sum _ _ _];
    rw [ ← h_A ] ; rw [ ← Finset.sum_add_distrib ] ; congr ; ext ; rw [ ← Finset.sum_add_distrib ] ; congr ; ext ; rw [ ← Finset.sum_add_distrib ] ; congr ; ext ; rw [ ← Finset.sum_add_distrib ] ; congr ; ext ; ring_nf;
  have h_C : ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, 4 * G.s u v * G.s w x * G.s u w * G.s v x = 4 * G.C4 := by
    simp +decide only [← mul_assoc, ← sum_s_s_s_s_eq_C4];
    simp +decide only [mul_assoc, Finset.mul_sum _ _ _];
  linarith [ bigsum_identity G ]

/-- **Key bound:** F₂(G) ≤ (card V)² · S_total -/
theorem F2_le (G : Trigraph V) :
    G.F2 ≤ (Fintype.card V) ^ 2 * G.S_total := by
  rw [F2_eq]
  have h1 := P4_add_C4_le_K13 G
  have h2 := P4_le_D G
  have h3 := R_nonneg G
  linarith

end Trigraph


/-! ================================================================
    From TrigraphPartition
    ================================================================ -/

/-
# Trigraph Partition Theorem

For every triangle-free trigraph G = (V, C, S), there exists a bipartition
(A, B) of V such that 4·(ē(A,B) + |S|) ≤ |V|².
-/


namespace Trigraph

variable {V : Type*} [Fintype V] [DecidableEq V]

def edgesWithin (G : Trigraph V) (χ : V → Bool) : ℤ :=
  ∑ u : V, ∑ v : V,
    (G.c u v + G.s u v) * if χ u = χ v then 1 else 0

lemma exists_bipartition_edgesWithin_le (G : Trigraph V) :
    ∃ χ : V → Bool,
      2 * G.edgesWithin χ ≤
      ∑ u : V, ∑ v : V, (G.c u v + G.s u v) := by
  have h_sum : ∑ χ : V → Bool, 2 * G.edgesWithin χ = ∑ u : V, ∑ v : V, (G.c u v + G.s u v) * (Finset.card (Finset.univ : Finset (V → Bool))) := by
    have h_sum : ∑ χ : V → Bool, 2 * G.edgesWithin χ = ∑ u : V, ∑ v : V, (G.c u v + G.s u v) * (∑ χ : V → Bool, if χ u = χ v then 2 else 0) := by
      simp +decide [ Trigraph.edgesWithin, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, Finset.sum_mul ];
      exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm );
    convert h_sum using 3;
    rename_i u _ v _;
    by_cases huv : u = v <;> simp +decide [ huv ];
    · rw [ G.c_self, G.s_self, add_zero ];
    · have h_sum : ∑ χ : V → Bool, (if χ u = χ v then 2 else 0) = ∑ χ : V → Bool, (if χ u ≠ χ v then 2 else 0) := by
        rw [ ← Equiv.sum_comp ( Equiv.addRight ( Pi.single v Bool.true ) ) ] ; simp +decide [ huv ];
        exact Finset.sum_congr rfl fun x hx => by cases x u <;> cases x v <;> simp +decide ;
      have h_sum : ∑ χ : V → Bool, (if χ u = χ v then 2 else 0) + ∑ χ : V → Bool, (if χ u ≠ χ v then 2 else 0) = ∑ χ : V → Bool, 2 := by
        rw [ ← Finset.sum_add_distrib, Finset.sum_congr rfl ] ; aesop;
      simp_all +decide [ Finset.card_univ ];
      exact Or.inl ( by linarith );
  contrapose! h_sum;
  refine' ne_of_gt ( lt_of_le_of_lt _ ( Finset.sum_lt_sum_of_nonempty ( Finset.univ_nonempty ) fun χ _ => h_sum χ ) ) ; simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
  rw [ mul_comm ]

lemma total_edges_le_sq (G : Trigraph V) :
    ∑ u : V, ∑ v : V, (G.c u v + G.s u v) ≤ (Fintype.card V) ^ 2 :=
  le_trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    show G.c i j + G.s i j ≤ 1 from G.cs_disjoint i j) (by simp +decide [pow_two])

lemma partition_when_S_zero (G : Trigraph V) (hS : G.S_total = 0) :
    ∃ χ : V → Bool,
      2 * (G.edgesWithin χ + G.S_total) ≤ (Fintype.card V) ^ 2 := by
  obtain ⟨χ, hχ⟩ := exists_bipartition_edgesWithin_le G
  use χ; rw [hS, mul_add, mul_zero, add_zero]; linarith [total_edges_le_sq G]

def restrict (G : Trigraph V) (Z : Finset V) : Trigraph ↥Z where
  c u v := G.c u.val v.val
  s u v := G.s u.val v.val
  c_nonneg u v := G.c_nonneg _ _
  c_le_one u v := G.c_le_one _ _
  s_nonneg u v := G.s_nonneg _ _
  s_le_one u v := G.s_le_one _ _
  c_symm u v := G.c_symm _ _
  s_symm u v := G.s_symm _ _
  c_self v := G.c_self _
  s_self v := G.s_self _
  cs_disjoint u v := G.cs_disjoint _ _
  triangle_free u v w := G.triangle_free _ _ _

lemma S_total_nonneg (G : Trigraph V) : 0 ≤ G.S_total :=
  Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => G.s_nonneg u v

lemma s_eq_zero_or_one (G : Trigraph V) (u v : V) : G.s u v = 0 ∨ G.s u v = 1 := by
  have := G.s_nonneg u v; have := G.s_le_one u v; omega

lemma c_eq_zero_or_one (G : Trigraph V) (u v : V) : G.c u v = 0 ∨ G.c u v = 1 := by
  have := G.c_nonneg u v; have := G.c_le_one u v; omega

lemma no_edges_in_S_nbrs (G : Trigraph V) (v₀ u w : V)
    (hu : G.s v₀ u = 1) (hw : G.s v₀ w = 1) :
    G.c u w = 0 ∧ G.s u w = 0 := by
  have h := G.triangle_free v₀ u w; rw [hu, hw] at h; simp at h
  exact ⟨by linarith [G.c_nonneg u w, G.s_nonneg u w],
         by linarith [G.c_nonneg u w, G.s_nonneg u w]⟩

lemma s_nbrs_disjoint (G : Trigraph V) (u₀ v₀ : V) (huv : G.s u₀ v₀ = 1) :
    ∀ w, G.s v₀ w = 1 → G.s u₀ w = 0 := by
  intro w hw
  have h := G.triangle_free v₀ u₀ w
  rw [G.s_symm v₀ u₀, huv, hw] at h; simp at h
  linarith [G.c_nonneg u₀ w, G.s_nonneg u₀ w]

lemma f2_nonneg (G : Trigraph V) (u v w x : V) (huv : G.s u v = 1) :
    0 ≤ G.f2 u v w x := by
      have h_s_values : ∀ u v, G.s u v = 0 ∨ G.s u v = 1 := by
        grind +suggestions;
      cases h_s_values u w <;> cases h_s_values v w <;> cases h_s_values u x <;> cases h_s_values v x <;> simp_all +decide only [f2];
      all_goals have := G.triangle_free u v w; have := G.triangle_free u v x; simp_all +decide ;
      any_goals linarith [ G.c_nonneg v w, G.c_le_one v w, G.c_nonneg v x, G.c_le_one v x ];
      · linarith [ G.c_nonneg w x, G.s_nonneg w x ];
      · linarith [ G.c_nonneg w x, G.s_nonneg w x ];
      · grind

lemma exists_small_f2_sum (G : Trigraph V) (hS : 0 < G.S_total) :
    ∃ u₀ v₀, G.s u₀ v₀ = 1 ∧
    (∑ w : V, ∑ x : V, G.f2 u₀ v₀ w x) ≤ (Fintype.card V : ℤ) ^ 2 := by
      by_contra! h;
      have h_sum : ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, G.f2 u v w x > (Fintype.card V) ^ 2 * ∑ u : V, ∑ v : V, G.s u v := by
        have h_sum : ∑ u : V, ∑ v : V, ∑ w : V, ∑ x : V, G.f2 u v w x > ∑ u : V, ∑ v : V, (G.s u v * (Fintype.card V) ^ 2) := by
          refine' Finset.sum_lt_sum _ _;
          · intro u hu; refine' Finset.sum_le_sum fun v hv => _; by_cases huv : G.s u v = 1 <;> simp_all +decide [ mul_comm ] ;
            · exact le_of_lt ( h u v huv );
            · rw [ show G.s u v = 0 by exact Or.resolve_right ( s_eq_zero_or_one G u v ) huv ] ; simp +decide [ Trigraph.f2 ];
              rw [ show G.s u v = 0 by exact Or.resolve_right ( s_eq_zero_or_one G u v ) huv ] ; simp +decide;
          · obtain ⟨u₀, v₀, huv⟩ : ∃ u₀ v₀ : V, G.s u₀ v₀ = 1 := by
              by_cases h_zero : ∀ u v : V, G.s u v = 0;
              · exact False.elim ( hS.ne' ( Finset.sum_eq_zero fun u hu => Finset.sum_eq_zero fun v hv => h_zero u v ) );
              · exact by push Not at h_zero; obtain ⟨ u, v, h ⟩ := h_zero; exact ⟨ u, v, Or.resolve_left ( G.s_eq_zero_or_one u v ) h ⟩ ;
            refine' ⟨ u₀, Finset.mem_univ _, _ ⟩;
            refine' Finset.sum_lt_sum _ _;
            · intro i hi;
              by_cases hi' : G.s u₀ i = 1 <;> simp_all +decide [ Trigraph.f2 ];
              · exact le_of_lt ( h u₀ i hi' );
              · rw [ show G.s u₀ i = 0 by exact Or.resolve_right ( s_eq_zero_or_one G u₀ i ) hi' ] ; norm_num;
            · exact ⟨ v₀, Finset.mem_univ _, by simpa [ huv ] using h u₀ v₀ huv ⟩;
        simpa only [ mul_comm, Finset.mul_sum _ _ _ ] using h_sum;
      convert F2_le G using 1;
      unfold Trigraph.F2 Trigraph.S_total; aesop;

lemma Z_card_lt (G : Trigraph V) (u₀ v₀ : V) (huv : G.s u₀ v₀ = 1) :
    (Finset.univ \ (Finset.univ.filter (fun w => G.s v₀ w = 1) ∪
                    Finset.univ.filter (fun w => G.s u₀ w = 1))).card <
    Fintype.card V := by
      rw [ Finset.card_sdiff ] ; norm_num;
      exact ⟨ Fintype.card_pos_iff.mpr ⟨ u₀ ⟩, Or.inr ⟨ v₀, by simpa [ G.s_symm ] using huv ⟩ ⟩

/-! ### Helper lemmas for partition_construction_bound -/

/-- Z membership: w ∈ Z iff s(v₀,w) = 0 and s(u₀,w) = 0 -/
private lemma mem_Z_iff' (G : Trigraph V) (u₀ v₀ w : V) :
    w ∈ Finset.univ \ (Finset.univ.filter (fun w => G.s v₀ w = 1) ∪
                        Finset.univ.filter (fun w => G.s u₀ w = 1)) ↔
    G.s v₀ w ≠ 1 ∧ G.s u₀ w ≠ 1 := by
  simp [Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter]

/-- s values are 0 or 1, so ≠ 1 implies = 0. -/
private lemma s_zero_of_ne_one (G : Trigraph V) (u v : V) (h : G.s u v ≠ 1) :
    G.s u v = 0 :=
  (G.s_eq_zero_or_one u v).resolve_right h

set_option maxHeartbeats 6400000 in
/-- Pairwise bound on f₂ symmetrization (copy for use without circular import). -/
private lemma pairwise_bound (G : Trigraph V) (u₀ v₀ w x : V)
    (huv : G.s u₀ v₀ = 1)
    (a b : Bool) :
    let sw₀ := G.s v₀ w; let su₀ := G.s u₀ w
    let sx₀ := G.s v₀ x; let sx₁ := G.s u₀ x
    let wZ : ℤ := if sw₀ = 0 ∧ su₀ = 0 then 1 else 0
    let xZ : ℤ := if sx₀ = 0 ∧ sx₁ = 0 then 1 else 0
    let χ₁w := if sw₀ = 0 ∧ su₀ = 0 then a else if sw₀ = 1 then false else true
    let χ₁x := if sx₀ = 0 ∧ sx₁ = 0 then b else if sx₀ = 1 then false else true
    let χ₂w := if sw₀ = 0 ∧ su₀ = 0 then !a else if sw₀ = 1 then false else true
    let χ₂x := if sx₀ = 0 ∧ sx₁ = 0 then !b else if sx₀ = 1 then false else true
    2 * ((G.c w x + G.s w x) * (if χ₁w = χ₁x then 1 else 0) +
         (G.c w x + G.s w x) * (if χ₂w = χ₂x then 1 else 0) +
         2 * G.s w x -
         2 * (G.c w x + G.s w x) * wZ * xZ * (if χ₁w = χ₁x then 1 else 0) -
         2 * G.s w x * wZ * xZ) ≤
    G.f2 u₀ v₀ w x + G.f2 u₀ v₀ x w - 2 * (wZ * xZ) := by
  have hdis_w : G.s v₀ w = 1 → G.s u₀ w = 0 := G.s_nbrs_disjoint u₀ v₀ huv w
  have hdis_x : G.s v₀ x = 1 → G.s u₀ x = 0 := G.s_nbrs_disjoint u₀ v₀ huv x
  have hno_v : G.s v₀ w = 1 → G.s v₀ x = 1 → G.c w x = 0 ∧ G.s w x = 0 :=
    fun hw hx => G.no_edges_in_S_nbrs v₀ w x hw hx
  have hno_u : G.s u₀ w = 1 → G.s u₀ x = 1 → G.c w x = 0 ∧ G.s w x = 0 :=
    fun hw hx => G.no_edges_in_S_nbrs u₀ w x hw hx
  rcases G.s_eq_zero_or_one v₀ w with hsw₀ | hsw₀ <;>
  rcases G.s_eq_zero_or_one u₀ w with hsu₀ | hsu₀ <;>
  rcases G.s_eq_zero_or_one v₀ x with hsx₀ | hsx₀ <;>
  rcases G.s_eq_zero_or_one u₀ x with hsx₁ | hsx₁ <;>
  rcases G.c_eq_zero_or_one w x with hcw | hcw <;>
  rcases G.s_eq_zero_or_one w x with hswx | hswx <;>
  cases a <;>
  cases b
  all_goals
    simp [Trigraph.f2, huv, hsw₀, hsu₀, hsx₀, hsx₁, hcw, hswx, G.c_symm, G.s_symm] at *
    try omega

/-
Unfolding the restricted edgesWithin + S_total as a sum over the subtype.
-/
private lemma restrict_sum_unfold (G : Trigraph V) (Z : Finset V) (χ_Z : ↥Z → Bool) :
    (G.restrict Z).edgesWithin χ_Z + (G.restrict Z).S_total =
    ∑ w : ↥Z, ∑ x : ↥Z,
      ((G.c w.val x.val + G.s w.val x.val) *
        (if χ_Z w = χ_Z x then 1 else 0) +
       G.s w.val x.val) := by
  unfold Trigraph.edgesWithin Trigraph.S_total;
  unfold Trigraph.restrict; simp +decide [ Finset.sum_add_distrib ] ;

/-
Convert a sum over a subtype to a sum over V with indicator functions.
    Specifically: Σ_{w:↥Z} Σ_{x:↥Z} f(w.val,x.val) =
    Σ_{w:V} Σ_{x:V} f(w,x) * [w∈Z] * [x∈Z]
-/
private lemma sum_subtype_eq_sum_indicator (Z : Finset V) (f : V → V → ℤ) :
    ∑ w : ↥Z, ∑ x : ↥Z, f w.val x.val =
    ∑ w : V, ∑ x : V, f w x * (if w ∈ Z then 1 else 0) * (if x ∈ Z then 1 else 0) := by
  -- By definition of Finset.sum_coe_sort, we can rewrite the left-hand side as a sum over V with an indicator function for Z.
  have h_sum_coe_sort : ∑ w : ↥Z, ∑ x : ↥Z, f w.val x.val = ∑ w ∈ Z, ∑ x ∈ Z, f w x := by
    refine' Finset.sum_bij ( fun x _ => x.val ) _ _ _ _ <;> simp +decide;
    exact fun x hx => by conv_rhs => rw [ ← Finset.sum_attach ] ;
  simp_all +decide [ Finset.sum_ite ]

/-
The sum Σ_{w,x} [w∈Z] * [x∈Z] = |Z|²
-/
private lemma sum_indicator_Z_sq (Z : Finset V) :
    ∑ w : V, ∑ x : V,
      ((if w ∈ Z then (1:ℤ) else 0) * (if x ∈ Z then 1 else 0)) = (Z.card : ℤ) ^ 2 := by
  simp +decide [ sq, Finset.sum_ite ]

/-
Reindexing: Σ_{w,x} f2(u₀,v₀,x,w) = Σ_{w,x} f2(u₀,v₀,w,x)
-/
private lemma sum_f2_swap (G : Trigraph V) (u₀ v₀ : V) :
    ∑ w : V, ∑ x : V, G.f2 u₀ v₀ x w =
    ∑ w : V, ∑ x : V, G.f2 u₀ v₀ w x := by
  rw [ Finset.sum_comm, Finset.sum_congr rfl ];
  swap;
  exacts [ fun x => ∑ x_1, G.f2 u₀ v₀ x x_1, fun x _ => rfl ]

/-! ### The key combined inequality -/

/-
Core averaging step: given two colorings χ₁, χ₂ whose edgesWithin sum is
    bounded by Σ f₂, conclude existence of a single coloring achieving the bound.
-/
private lemma partition_from_sum_bound (G : Trigraph V) (u₀ v₀ : V)
    (χ₁ χ₂ : V → Bool)
    (h : G.edgesWithin χ₁ + G.edgesWithin χ₂ + 2 * G.S_total ≤
         ∑ w : V, ∑ x : V, G.f2 u₀ v₀ w x) :
    ∃ χ : V → Bool,
      2 * (G.edgesWithin χ + G.S_total) ≤ ∑ w : V, ∑ x : V, G.f2 u₀ v₀ w x := by
  by_cases h₁ : G.edgesWithin χ₁ ≤ G.edgesWithin χ₂ <;> [ exact ⟨ χ₁, by linarith ⟩ ; exact ⟨ χ₂, by linarith ⟩ ]

/-
Key identity: the sum of indicator-restricted terms equals the restricted trigraph sum.
    This converts the IH from restricted-trigraph form to indicator-sum form.
-/
private lemma IH_as_indicator_bound (G : Trigraph V) (u₀ v₀ : V) (huv : G.s u₀ v₀ = 1)
    (Z : Finset V)
    (hZ : Z = Finset.univ \ (Finset.univ.filter (fun w => G.s v₀ w = 1) ∪
                              Finset.univ.filter (fun w => G.s u₀ w = 1)))
    (χ_Z : ↥Z → Bool)
    (hIH : 2 * ((G.restrict Z).edgesWithin χ_Z + (G.restrict Z).S_total) ≤
           (Z.card : ℤ) ^ 2)
    (χ₁ : V → Bool)
    (hχ₁_on_Z : ∀ (w : V) (hw : w ∈ Z), χ₁ w = χ_Z ⟨w, hw⟩) :
    2 * ∑ w : V, ∑ x : V,
      ((G.c w x + G.s w x) * (if χ₁ w = χ₁ x then 1 else 0) + G.s w x) *
      (if w ∈ Z then 1 else 0) * (if x ∈ Z then 1 else 0)
    ≤ (Z.card : ℤ) ^ 2 := by
  convert hIH using 2;
  convert restrict_sum_unfold G Z χ_Z |> Eq.symm using 1;
  rw [ ← Finset.sum_subset ( Finset.subset_univ Z ) ];
  · refine' Finset.sum_bij ( fun w hw => ⟨ w, hw ⟩ ) _ _ _ _ <;> simp +decide [ hχ₁_on_Z ];
    intro w hw; rw [ ← Finset.sum_attach ] ; simp +decide [ hχ₁_on_Z w hw ] ;
    grind;
  · aesop

set_option maxHeartbeats 6400000 in
/-- Core inequality: summing pairwise_bound over all (w,x) and applying the IH gives
    the global two-coloring bound. -/
private lemma two_coloring_sum_le (G : Trigraph V) (u₀ v₀ : V) (huv : G.s u₀ v₀ = 1)
    (Z : Finset V)
    (hZ : Z = Finset.univ \ (Finset.univ.filter (fun w => G.s v₀ w = 1) ∪
                              Finset.univ.filter (fun w => G.s u₀ w = 1)))
    (χ_Z : ↥Z → Bool)
    (hIH : 2 * ((G.restrict Z).edgesWithin χ_Z + (G.restrict Z).S_total) ≤
           (Z.card : ℤ) ^ 2)
    (χ₁ χ₂ : V → Bool)
    (hχ₁_on_Z : ∀ (w : V) (hw : w ∈ Z), χ₁ w = χ_Z ⟨w, hw⟩)
    (hχ₂_on_Z : ∀ (w : V) (hw : w ∈ Z), χ₂ w = !(χ_Z ⟨w, hw⟩))
    (hχ_off_Z : ∀ w, w ∉ Z → χ₁ w = χ₂ w)
    (hχ₁_A : ∀ w, G.s v₀ w = 1 → χ₁ w = false)
    (hχ₁_B : ∀ w, G.s u₀ w = 1 → χ₁ w = true) :
    G.edgesWithin χ₁ + G.edgesWithin χ₂ + 2 * G.S_total ≤
    ∑ w : V, ∑ x : V, G.f2 u₀ v₀ w x := by
  revert hχ₂_on_Z hχ_off_Z hχ₁_A hχ₁_B;
  intro hχ₂_on_Z hχ_off_Z hχ₁_A hχ₁_B
  have h_sum : ∑ w : V, ∑ x : V, (2 * ((G.c w x + G.s w x) * (if χ₁ w = χ₁ x then 1 else 0) + (G.c w x + G.s w x) * (if χ₂ w = χ₂ x then 1 else 0) + 2 * G.s w x - 2 * (if w ∈ Z then 1 else 0) * (if x ∈ Z then 1 else 0) * ((G.c w x + G.s w x) * (if χ₁ w = χ₁ x then 1 else 0) + G.s w x))) ≤ ∑ w : V, ∑ x : V, G.f2 u₀ v₀ w x + ∑ w : V, ∑ x : V, G.f2 u₀ v₀ x w - 2 * (Z.card : ℤ) ^ 2 := by
    have h_sum : ∑ w : V, ∑ x : V, (2 * ((G.c w x + G.s w x) * (if χ₁ w = χ₁ x then 1 else 0) + (G.c w x + G.s w x) * (if χ₂ w = χ₂ x then 1 else 0) + 2 * G.s w x - 2 * (if w ∈ Z then 1 else 0) * (if x ∈ Z then 1 else 0) * ((G.c w x + G.s w x) * (if χ₁ w = χ₁ x then 1 else 0) + G.s w x))) ≤ ∑ w : V, ∑ x : V, (G.f2 u₀ v₀ w x + G.f2 u₀ v₀ x w - 2 * (if w ∈ Z then 1 else 0) * (if x ∈ Z then 1 else 0)) := by
      refine' Finset.sum_le_sum fun w hw => Finset.sum_le_sum fun x hx => _;
      have := pairwise_bound G u₀ v₀ w x huv (χ₁ w) (χ₁ x);
      grind +suggestions;
    convert h_sum using 1;
    simp +decide [ Finset.sum_add_distrib, sum_f2_swap ];
    ring_nf;
  have h_sum : 4 * ∑ w : V, ∑ x : V, (if w ∈ Z then 1 else 0) * (if x ∈ Z then 1 else 0) * ((G.c w x + G.s w x) * (if χ₁ w = χ₁ x then 1 else 0) + G.s w x) ≤ 2 * (Z.card : ℤ) ^ 2 := by
    have h_sum : 2 * (∑ w : V, ∑ x : V, ((G.c w x + G.s w x) * (if χ₁ w = χ₁ x then 1 else 0) + G.s w x) * (if w ∈ Z then 1 else 0) * (if x ∈ Z then 1 else 0)) ≤ (Z.card : ℤ) ^ 2 := by
      convert IH_as_indicator_bound G u₀ v₀ huv Z hZ χ_Z hIH χ₁ hχ₁_on_Z using 1;
    convert mul_le_mul_of_nonneg_left h_sum zero_le_two using 1 ; ring_nf;
    exact congrArg₂ _ ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by split_ifs <;> ring_nf ) rfl;
  have h_sum : ∑ w : V, ∑ x : V, (2 * ((G.c w x + G.s w x) * (if χ₁ w = χ₁ x then 1 else 0) + (G.c w x + G.s w x) * (if χ₂ w = χ₂ x then 1 else 0) + 2 * G.s w x)) = 2 * (G.edgesWithin χ₁ + G.edgesWithin χ₂) + 4 * G.S_total := by
    simp +decide [ Finset.mul_sum _ _ _, Trigraph.edgesWithin, Trigraph.S_total ] ; ring_nf;
    simp +decide only [sum_add_distrib, sum_mul _ _ _] ; ring_nf;
  norm_num [ Finset.mul_sum _ _ _, mul_assoc ] at *;
  norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] at *;
  linarith [ show ∑ w : V, ∑ x : V, G.f2 u₀ v₀ x w = ∑ w : V, ∑ x : V, G.f2 u₀ v₀ w x from sum_f2_swap G u₀ v₀ ]

set_option maxHeartbeats 3200000 in
theorem partition_construction_bound (G : Trigraph V) (u₀ v₀ : V)
    (huv : G.s u₀ v₀ = 1)
    (χ_Z : ↥(Finset.univ \ (Finset.univ.filter (fun w => G.s v₀ w = 1) ∪
                              Finset.univ.filter (fun w => G.s u₀ w = 1))) → Bool)
    (hIH : 2 * ((G.restrict (Finset.univ \ (Finset.univ.filter (fun w => G.s v₀ w = 1) ∪
                              Finset.univ.filter (fun w => G.s u₀ w = 1)))).edgesWithin χ_Z +
                 (G.restrict (Finset.univ \ (Finset.univ.filter (fun w => G.s v₀ w = 1) ∪
                              Finset.univ.filter (fun w => G.s u₀ w = 1)))).S_total) ≤
           ((Finset.univ \ (Finset.univ.filter (fun w => G.s v₀ w = 1) ∪
                            Finset.univ.filter (fun w => G.s u₀ w = 1))).card : ℤ) ^ 2) :
    ∃ χ : V → Bool,
      2 * (G.edgesWithin χ + G.S_total) ≤ ∑ w : V, ∑ x : V, G.f2 u₀ v₀ w x := by
  convert two_coloring_sum_le G u₀ v₀ huv _ rfl χ_Z hIH _ _ _ _ _ using 1;
  rotate_left;
  exact fun w => if hw : w ∈ Finset.univ \ ( Finset.filter ( fun w => G.s v₀ w = 1 ) Finset.univ ∪ Finset.filter ( fun w => G.s u₀ w = 1 ) Finset.univ ) then χ_Z ⟨ w, hw ⟩ else if G.s v₀ w = 1 then Bool.false else Bool.true;
  use fun w => if hw : w ∈ Finset.univ \ ( Finset.filter ( fun w => G.s v₀ w = 1 ) Finset.univ ∪ Finset.filter ( fun w => G.s u₀ w = 1 ) Finset.univ ) then !χ_Z ⟨ w, hw ⟩ else if G.s v₀ w = 1 then false else true;
  · aesop;
  · aesop;
  · aesop;
  · constructor <;> intro h;
    · convert two_coloring_sum_le G u₀ v₀ huv _ rfl χ_Z hIH _ _ _ _ _ using 1;
      · aesop;
      · aesop;
      · aesop;
    · contrapose! h;
      refine' ⟨ _, _, _ ⟩;
      · aesop;
      · intro w hw; simp +decide [ hw ] ;
        have := G.triangle_free u₀ v₀ w; simp_all +decide ;
        linarith [ G.c_nonneg v₀ w, G.s_nonneg v₀ w ];
      · grind +splitImp

/-! ### Main induction -/

private theorem partition_aux (n : ℕ) :
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : Trigraph V),
    Fintype.card V ≤ n →
    ∃ χ : V → Bool, 2 * (G.edgesWithin χ + G.S_total) ≤ (Fintype.card V : ℤ) ^ 2 := by
  induction n with
  | zero =>
    intro V _ _ G hn
    have hcard : Fintype.card V = 0 := Nat.le_zero.mp hn
    exact ⟨fun _ => false, by simp [edgesWithin, S_total, Fintype.card_eq_zero_iff.mp hcard]⟩
  | succ n ih =>
    intro V _ _ G hn
    by_cases hS : G.S_total = 0
    · exact partition_when_S_zero G hS
    · have hS_pos : 0 < G.S_total := lt_of_le_of_ne (S_total_nonneg G) (Ne.symm hS)
      obtain ⟨u₀, v₀, huv, hf2⟩ := exists_small_f2_sum G hS_pos
      set Z := Finset.univ \ (Finset.univ.filter (fun w => G.s v₀ w = 1) ∪
                               Finset.univ.filter (fun w => G.s u₀ w = 1))
      have hZ_lt : Fintype.card ↥Z < Fintype.card V := by
        rw [Fintype.card_coe]; exact Z_card_lt G u₀ v₀ huv
      have hZ_le : Fintype.card ↥Z ≤ n := by omega
      obtain ⟨χ_Z, hχ_Z⟩ := ih (G.restrict Z) hZ_le
      have hIH : 2 * ((G.restrict Z).edgesWithin χ_Z + (G.restrict Z).S_total) ≤
                 (Z.card : ℤ) ^ 2 := by
        have : Fintype.card ↥Z = Z.card := Fintype.card_coe Z
        rw [this] at hχ_Z; exact_mod_cast hχ_Z
      obtain ⟨χ, hχ⟩ := partition_construction_bound G u₀ v₀ huv χ_Z hIH
      exact ⟨χ, le_trans hχ hf2⟩

/-- **Trigraph Partition Theorem** (Norin–Sun, Theorem 1.3 for trigraphs). -/
theorem trigraph_partition_exists (G : Trigraph V) :
    ∃ χ : V → Bool,
      2 * (G.edgesWithin χ + G.S_total) ≤ (Fintype.card V) ^ 2 :=
  partition_aux (Fintype.card V) G le_rfl

end Trigraph


/-! ================================================================
    From Bridge
    ================================================================ -/

/-
# Bridge: SimpleGraph ↔ Trigraph

Connects the graph-theoretic definitions (alpha1, tauB) to the
trigraph machinery (F₂ bound, partition theorem).
-/


namespace TriangleIndep

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Construction of trigraph from graph + triangle-independent set -/

/-
Given a simple graph G and a triangle-independent set S ⊆ E(G),
    construct the trigraph T = (V, E\S, S).
-/
noncomputable def mkTrigraph (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) (hS : S ⊆ G.edgeFinset)
    (hTI : IsTriangleIndependent G S) : Trigraph V where
  c u v := if G.Adj u v ∧ s(u, v) ∉ S then 1 else 0
  s u v := if s(u, v) ∈ S then 1 else 0
  c_nonneg u v := by split_ifs <;> omega
  c_le_one u v := by split_ifs <;> omega
  s_nonneg u v := by split_ifs <;> omega
  s_le_one u v := by split_ifs <;> omega
  c_symm u v := by
    simp only [Sym2.eq_swap]; split_ifs <;> simp_all [SimpleGraph.adj_comm]
  s_symm u v := by simp [Sym2.eq_swap]
  c_self v := by simp
  s_self v := by
    simp only [ite_eq_right_iff, one_ne_zero]
    intro hmem
    have h := hS hmem
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at h
    exact absurd h (G.loopless.1 v)
  cs_disjoint u v := by
    by_cases h : s(u, v) ∈ S
    · simp [h]
    · simp [h]; omega
  triangle_free u v w := by
    by_cases huv : s(u, v) ∈ S <;> by_cases huw : s(u, w) ∈ S <;> simp +decide [ huv, huw ];
    have := hTI.2 u v w;
    by_cases hvw : G.Adj v w <;> simp_all +decide;
    · by_cases huv' : G.Adj u v <;> by_cases huw' : G.Adj u w <;> simp_all +decide;
      · rw [ Finset.card_le_one_iff ] at this;
        specialize @this s(u, v) s(u, w) ; aesop;
      · have := hS huw; simp_all +decide [ SimpleGraph.mem_edgeSet ] ;
      · have := hS huv; have := hS huw; simp_all +decide [ SimpleGraph.mem_edgeSet ] ;
      · have := hS huv; have := hS huw; simp_all +decide [ SimpleGraph.mem_edgeSet ] ;
    · exact fun h => hvw <| by have := hS h; aesop;

/-! ## Properties of the constructed trigraph -/

/-
The edgesWithin of the constructed trigraph equals the ordered count
    of G-edges within parts of the bipartition.
-/
lemma mkTrigraph_edgesWithin (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) (hS : S ⊆ G.edgeFinset)
    (hTI : IsTriangleIndependent G S) (χ : V → Bool) :
    (mkTrigraph G S hS hTI).edgesWithin χ =
    ∑ u : V, ∑ v : V,
      if G.Adj u v ∧ χ u = χ v then 1 else 0 := by
  have h_edgesWithin : ∀ u v, (mkTrigraph G S hS hTI).c u v + (mkTrigraph G S hS hTI).s u v = if G.Adj u v then 1 else 0 := by
    intro u v; split_ifs <;> simp_all +decide [ mkTrigraph ] ;
    · split_ifs <;> norm_num;
    · exact fun h => by have := hS h; simp_all +decide [ SimpleGraph.mem_edgeSet ] ;
  exact Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => by specialize h_edgesWithin u v; aesop;

/-
The S_total of the constructed trigraph.
-/
lemma mkTrigraph_S_total (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) (hS : S ⊆ G.edgeFinset)
    (hTI : IsTriangleIndependent G S) :
    (mkTrigraph G S hS hTI).S_total = 2 * (S.card : ℤ) := by
  unfold Trigraph.S_total mkTrigraph;
  -- Since $s(u, v) = 1$ if and only if $s(u, v) \in S$, the sum counts the number of edges in $S$.
  have h_count_edges : ∑ u : V, ∑ v : V, (if s(u, v) ∈ S then 1 else 0) = ∑ e ∈ S, 2 := by
    have h_count_edges : ∑ e ∈ S, 2 = ∑ e ∈ S, ∑ u : V, ∑ v : V, (if e = s(u, v) then 1 else 0) := by
      refine' Finset.sum_congr rfl fun e he => _;
      rcases e with ⟨ u, v ⟩ ; simp +decide ;
      rw [ Finset.sum_eq_add ( u ) ( v ) ] <;> simp +decide [ Finset.filter_eq, Finset.filter_or ];
      · by_cases hu : u = v <;> simp +decide [ hu ];
        · have := hS he; simp_all +decide [ SimpleGraph.mem_edgeFinset ] ;
        · exact Ne.symm hu;
      · intro h; have := hS he; simp_all +decide ;
      · exact fun c hc₁ hc₂ => ⟨ Ne.symm hc₁, Ne.symm hc₂ ⟩;
    rw [ h_count_edges, Finset.sum_comm ];
    rw [ Finset.sum_comm, Finset.sum_congr rfl ];
    rw [ Finset.sum_comm ];
    intro u hu; rw [ ← Finset.sum_comm ] ; simp +decide ;
  convert h_count_edges using 1 ; norm_cast ; simp +decide [ mul_comm ];
  norm_cast

/-! ## tauB bound -/

/-
For any Boolean partition χ, tauB G is at most the number of
    G-edges within parts (unordered count).
-/
omit [DecidableEq V] in
lemma tauB_le_noncut (G : SimpleGraph V) [DecidableRel G.Adj] (χ : V → Bool) :
    tauB G ≤ (G.edgeFinset.filter (fun e =>
      Sym2.lift ⟨fun u v => χ u = χ v, by intros; simp [eq_comm]⟩ e)).card := by
  refine' csInf_le _ _;
  · exact ⟨ 0, Set.forall_mem_image.2 fun F hF => Nat.zero_le _ ⟩;
  · refine' ⟨ _, ⟨ _, _ ⟩, rfl ⟩;
    · exact Finset.filter_subset _ _;
    · refine' ⟨ fun v => if χ v then 0 else 1, _ ⟩;
      intro u v huv; contrapose! huv; aesop;

end TriangleIndep


/-! ================================================================
    From MainTheorem
    ================================================================ -/

/-
# Main Theorem: Triangle-independent sets vs. cuts

Formalization of Theorem 1.3 from Norin–Sun:
  For every graph G, α₁(G) + τ_B(G) ≤ |V(G)|² / 4.
-/


namespace TriangleIndep

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Main Theorem -/

/-
**Norin–Sun (Theorem 1.3).** For every finite simple graph G,
    4 * (α₁(G) + τ_B(G)) ≤ |V(G)|².
    This is equivalent to α₁(G) + τ_B(G) ≤ |V(G)|²/4 (over the reals).
-/
set_option maxHeartbeats 1600000 in
theorem main_inequality (G : SimpleGraph V) [DecidableRel G.Adj] :
    4 * (alpha1 G + tauB G) ≤ (Fintype.card V) ^ 2 := by
  -- By definition of $alpha1$, there exists a triangle-independent set $S$ such that $|S| \geq alpha1 G$.
  obtain ⟨S, hS⟩ : ∃ S : Finset (Sym2 V), S ⊆ G.edgeFinset ∧ IsTriangleIndependent G S ∧ S.card ≥ alpha1 G := by
    have := Finset.exists_max_image ( Finset.filter ( IsTriangleIndependent G ) ( G.edgeFinset.powerset ) ) Finset.card ⟨ ∅, by simp +decide [ IsTriangleIndependent ] ⟩;
    obtain ⟨ S, hS₁, hS₂ ⟩ := this; use S; simp_all +decide [ alpha1 ] ;
  -- By definition of $tauB$, there exists a bipartition $\chi$ such that $tauB G \leq (G.edgeFinset.filter (fun e => Sym2.lift ⟨fun u v => χ u = χ v, by intros; simp [eq_comm]⟩ e)).card$.
  obtain ⟨χ, hχ⟩ : ∃ χ : V → Bool, 2 * ((∑ u : V, ∑ v : V, (if G.Adj u v ∧ χ u = χ v then 1 else 0)) + 2 * S.card) ≤ (Fintype.card V) ^ 2 := by
    have := Trigraph.trigraph_partition_exists (TriangleIndep.mkTrigraph G S hS.1 hS.2.1);
    convert this using 4;
    rw [ TriangleIndep.mkTrigraph_edgesWithin, TriangleIndep.mkTrigraph_S_total ] ; norm_cast;
  have h_tauB : tauB G ≤ (G.edgeFinset.filter (fun e => Sym2.lift ⟨fun u v => χ u = χ v, by intros; simp [eq_comm]⟩ e)).card := by
    apply TriangleIndep.tauB_le_noncut;
  have h_card_filter : (G.edgeFinset.filter (fun e => Sym2.lift ⟨fun u v => χ u = χ v, by intros; simp [eq_comm]⟩ e)).card ≤ (∑ u : V, ∑ v : V, (if G.Adj u v ∧ χ u = χ v then 1 else 0)) / 2 := by
    have h_card_filter : (G.edgeFinset.filter (fun e => Sym2.lift ⟨fun u v => χ u = χ v, by intros; simp [eq_comm]⟩ e)).card * 2 ≤ (∑ u : V, ∑ v : V, (if G.Adj u v ∧ χ u = χ v then 1 else 0)) := by
      have h_card_filter : (G.edgeFinset.filter (fun e => Sym2.lift ⟨fun u v => χ u = χ v, by intros; simp [eq_comm]⟩ e)).card * 2 ≤ Finset.card (Finset.filter (fun (uv : V × V) => G.Adj uv.1 uv.2 ∧ χ uv.1 = χ uv.2) (Finset.univ : Finset (V × V))) := by
        have h_card_filter : Finset.card (Finset.filter (fun (uv : V × V) => G.Adj uv.1 uv.2 ∧ χ uv.1 = χ uv.2) (Finset.univ : Finset (V × V))) ≥ Finset.card (Finset.biUnion (Finset.filter (fun e => Sym2.lift ⟨fun u v => χ u = χ v, by intros; simp [eq_comm]⟩ e) G.edgeFinset) (fun e => Finset.filter (fun (uv : V × V) => Sym2.mk uv.1 uv.2 = e) (Finset.univ : Finset (V × V)))) := by
          refine Finset.card_le_card ?_;
          simp +decide [ Finset.subset_iff ];
        refine' le_trans _ h_card_filter;
        rw [ Finset.card_biUnion ];
        · rw [ Finset.sum_const_nat ];
          simp +decide;
          intro e he hχe; rcases e with ⟨ u, v ⟩ ; simp_all +decide [ Sym2.lift ] ;
          rw [ Finset.card_eq_two ] ; use ( u, v ), ( v, u ) ; aesop;
        · intro e he f hf hne; simp_all +decide [ Finset.disjoint_left ] ;
      convert h_card_filter using 1;
      rw [ Finset.card_filter ];
      exact Eq.symm (Fintype.sum_prod_type fun x => if G.Adj x.1 x.2 ∧ χ x.1 = χ x.2 then 1 else 0);
    exact Nat.le_div_iff_mul_le zero_lt_two |>.2 h_card_filter;
  grind

end TriangleIndep


/-! ================================================================
    From Corollary
    ================================================================ -/

/-
# Erdős Corollary: α₁(G) + τ₁(G) ≤ |V(G)|² / 4

This follows from the stronger Norin-Sun theorem:
  α₁(G) + τ_B(G) ≤ |V(G)|² / 4
together with the trivial observation τ₁(G) ≤ τ_B(G).

τ₁(G) is the minimum number of edges to delete to make G triangle-free.
τ_B(G) is the minimum number of edges to delete to make G bipartite.
Since every bipartite graph is triangle-free, τ₁(G) ≤ τ_B(G).
-/


namespace TriangleIndep

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Definition of τ₁ -/

/-- A graph is triangle-free if it has no 3-clique. -/
def IsTriangleFree (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ u v w : V, G.Adj u v → G.Adj v w → G.Adj u w → False

/-- `tau1 G` is τ₁(G), the minimum number of edges to delete to make G triangle-free. -/
noncomputable def tau1 (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf ((fun F => F.card) ''
    {F : Finset (Sym2 V) | F ⊆ G.edgeFinset ∧
      IsTriangleFree (G.deleteEdges (F : Set (Sym2 V)))})

/-! ## τ₁(G) ≤ τ_B(G) -/

/-
Every bipartite graph is triangle-free.
-/
omit [Fintype V] [DecidableEq V] in
lemma IsBipartite.isTriangleFree (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsBipartite) : IsTriangleFree G := by
  obtain ⟨ A, hA ⟩ := hG;
  intro u v w hu hv hw; have := hA hu; have := hA hv; have := hA hw; ( have := Fin.exists_fin_two.mp ⟨ A u, rfl ⟩ ; ( have := Fin.exists_fin_two.mp ⟨ A v, rfl ⟩ ; ( have := Fin.exists_fin_two.mp ⟨ A w, rfl ⟩ ; aesop; ) ) )

/-
τ₁(G) ≤ τ_B(G): Making G bipartite also makes it triangle-free.
-/
theorem tau1_le_tauB (G : SimpleGraph V) [DecidableRel G.Adj] :
    tau1 G ≤ tauB G := by
  refine' le_csInf _ _;
  · refine' ⟨ _, ⟨ G.edgeFinset, ⟨ Finset.Subset.refl _, _ ⟩, rfl ⟩ ⟩;
    use fun _ => 0; aesop;
  · rintro _ ⟨ F, ⟨ hF₁, hF₂ ⟩, rfl ⟩;
    refine' Nat.sInf_le _;
    exact ⟨ F, ⟨ hF₁, IsBipartite.isTriangleFree _ hF₂ ⟩, rfl ⟩

/-! ## Erdős Corollary -/

/-- **Erdős–Gallai–Tuza Conjecture (proved by Norin–Sun).**
    For every finite simple graph G,
    4 * (α₁(G) + τ₁(G)) ≤ |V(G)|².
    This follows from the stronger inequality α₁(G) + τ_B(G) ≤ |V(G)|²/4
    together with τ₁(G) ≤ τ_B(G). -/
theorem erdos_conjecture (G : SimpleGraph V) [DecidableRel G.Adj] :
    4 * (alpha1 G + tau1 G) ≤ (Fintype.card V) ^ 2 := by
  have h1 := main_inequality G
  have h2 := tau1_le_tauB G
  calc 4 * (alpha1 G + tau1 G)
      ≤ 4 * (alpha1 G + tauB G) := by omega
    _ ≤ (Fintype.card V) ^ 2 := h1

#print axioms erdos_conjecture
-- 'Erdos621.TriangleIndep.erdos_conjecture' depends on axioms: [propext, Classical.choice,
-- Quot.sound]

end TriangleIndep


end

end Erdos621
