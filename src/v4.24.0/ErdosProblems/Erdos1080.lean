/-

This is a Lean formalization of a solution to Erdős Problem 1080.
https://www.erdosproblems.com/forum/thread/1080

The original proof was found by: de Caen and Székely

[DeSz92] de Caen, D. and Sz\'ekely, L. A., The maximum size of {$4$}-
and {$6$}-cycle free bipartite graphs on {$m,n$} vertices. (1992),
135--142.


A proof of ChatGPT's choice was auto-formalized by Aristotle (from
Harmonic).  The final theorem statement was available at the Formal
Conjectures project (organized by Google DeepMind).


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


/-
We define the Lazebnik-Ustimenko-Woldar graph $B(q)$ and its induced subgraph $B_S(q)$. We prove that these graphs are $C_6$-free. We then construct a family of bipartite graphs $G$ by deleting lines from $B_S(q)$, and prove that for any $c > 0$, there exists a graph in this family with parts of size $n^{2/3}$ and $n - n^{2/3}$ and at least $cn$ edges, which is $C_6$-free. This proves `thm_counterexamples`.
-/

/-
This module defines the Lazebnik-Ustimenko-Woldar bipartite graph B(q) and its induced subgraph B_S(q).
It proves that B(q) is C4-free and C6-free.
It also proves that B_S(q) is biregular with degrees q^2 and |S|.
The main theorem `B_C6_free` establishes that B(q) contains no 6-cycle.
The degrees of B_S(q) are established in `B_S_degree_P` and `B_S_degree_L`.
The construction of B_S(q) is given in `B_S`.
The graph B(q) is defined in `B`.
The point-translation automorphisms are defined in `tau0`, `tau2`, `tau3`.
The transitivity of B(q) on points is proved in `B_transitive_on_P`.
The uniqueness of 3-paths is proved in `B_no_C6_through_zero`.
The algebraic identities required for the proofs are established in `algebraic_identity` and `C6_algebraic_step`.
-/

import Mathlib


set_option linter.mathlibStandardSet false

open scoped Classical
open SimpleGraph Sum

set_option maxHeartbeats 0

/-
Definition of the Lazebnik-Ustimenko-Woldar bipartite graph B(q).
Vertices are Points P and Lines L.
P = {(p1, p2, p3) | p1^q = p1, p2 ∈ F, p3^q = p3}
L = {[l1, l2, l3] | l1 ∈ F, l2 ∈ F, l3^q = l3}
Adjacency: l2 - p2 = l1 p1 and l3 - p3 = l1^q p2 + l1 p2^q
-/
variable (F : Type*) [Field F] (q : ℕ)

/-- A point in the Lazebnik-Ustimenko-Woldar graph. -/
structure Point where
  p1 : F
  p2 : F
  p3 : F
  h1 : p1 ^ q = p1
  h3 : p3 ^ q = p3
deriving DecidableEq

/-- A line in the Lazebnik-Ustimenko-Woldar graph. -/
structure Line where
  l1 : F
  l2 : F
  l3 : F
  h3 : l3 ^ q = l3
deriving DecidableEq

/-- The adjacency relation for the Lazebnik-Ustimenko-Woldar graph. -/
def is_adjacent (p : Point F q) (l : Line F q) : Prop :=
  l.l2 - p.p2 = l.l1 * p.p1 ∧
  l.l3 - p.p3 = (l.l1 ^ q) * p.p2 + l.l1 * (p.p2 ^ q)

/-- The Lazebnik-Ustimenko-Woldar bipartite graph B(q). -/
def B (F : Type*) [Field F] (q : ℕ) : SimpleGraph (Point F q ⊕ Line F q) :=
  SimpleGraph.fromRel (fun v w =>
    match v, w with
    | Sum.inl p, Sum.inr l => is_adjacent F q p l
    | Sum.inr l, Sum.inl p => is_adjacent F q p l
    | _, _ => False)

/-
Definition of the action of $\tau_0(a)$ on points $P$.
$\tau_0(a): (p_1, p_2, p_3) \mapsto (p_1+a, p_2, p_3)$.
Requires $a \in \F_q$ and the characteristic property $(x+y)^q = x^q + y^q$.
-/
variable {F : Type*} [Field F] {q : ℕ}

/-- The action of tau0(a) on points. -/
def tau0_P (a : F) (ha : a^q = a) (h_add : ∀ x y : F, (x + y)^q = x^q + y^q) (p : Point F q) : Point F q :=
  { p1 := p.p1 + a,
    p2 := p.p2,
    p3 := p.p3,
    h1 := by
      rw [ h_add, p.h1, ha ],
    h3 := p.h3 }

/-
Definition of the action of $\tau_0(a)$ on lines $L$.
$\tau_0(a): [l_1, l_2, l_3] \mapsto [l_1, l_2+l_1a, l_3]$.
-/
/-- The action of tau0(a) on lines. -/
def tau0_L (a : F) (ha : a^q = a) (l : Line F q) : Line F q :=
  { l1 := l.l1,
    l2 := l.l2 + l.l1 * a,
    l3 := l.l3,
    h3 := l.h3 }

/-
Definition of the action of $\tau_2(b)$ on points $P$.
$\tau_2(b): (p_1, p_2, p_3) \mapsto (p_1, p_2+b, p_3)$.
-/
/-- The action of tau2(b) on points. -/
def tau2_P (b : F) (p : Point F q) : Point F q :=
  { p1 := p.p1,
    p2 := p.p2 + b,
    p3 := p.p3,
    h1 := p.h1,
    h3 := p.h3 }

/-
Definition of the action of $\tau_2(b)$ on lines $L$.
$\tau_2(b): [l_1, l_2, l_3] \mapsto [l_1, l_2+b, l_3+\ol{l_1}b+l_1\ol{b}]$.
Requires $x^{q^2}=x$ for all $x \in F$.
-/
/-- The action of tau2(b) on lines. -/
def tau2_L (b : F) (h_add : ∀ x y : F, (x + y)^q = x^q + y^q) (h_F : ∀ x : F, x^(q*q) = x) (l : Line F q) : Line F q :=
  { l1 := l.l1,
    l2 := l.l2 + b,
    l3 := l.l3 + (l.l1^q)*b + l.l1*(b^q),
    h3 := by
      simp_all +decide [ pow_mul ];
      simp_all +decide [ mul_pow ];
      rw [ add_right_comm, l.h3 ] }

/-
Definition of the action of $\tau_3(c)$ on points $P$.
$\tau_3(c): (p_1, p_2, p_3) \mapsto (p_1, p_2, p_3+c)$.
Requires $c \in \F_q$.
-/
/-- The action of tau3(c) on points. -/
def tau3_P (c : F) (hc : c^q = c) (h_add : ∀ x y : F, (x + y)^q = x^q + y^q) (p : Point F q) : Point F q :=
  { p1 := p.p1,
    p2 := p.p2,
    p3 := p.p3 + c,
    h1 := p.h1,
    h3 := by
      rw [ h_add, p.h3, hc ] }

/-
Definition of the action of $\tau_3(c)$ on lines $L$.
$\tau_3(c): [l_1, l_2, l_3] \mapsto [l_1, l_2, l_3+c]$.
Requires $c \in \F_q$.
-/
/-- The action of tau3(c) on lines. -/
def tau3_L (c : F) (hc : c^q = c) (h_add : ∀ x y : F, (x + y)^q = x^q + y^q) (l : Line F q) : Line F q :=
  { l1 := l.l1,
    l2 := l.l2,
    l3 := l.l3 + c,
    h3 := by
      rw [ h_add, l.h3, hc ] }

/-
Definition of the automorphism $\tau_0(a)$ of $B(q)$.
$\tau_0(a)$ maps $p \mapsto \tau_0(a)(p)$ and $l \mapsto \tau_0(a)(l)$.
It preserves the adjacency relation.
-/
/-- The automorphism tau0(a). -/
def tau0 (a : F) (ha : a^q = a) (h_add : ∀ x y : F, (x + y)^q = x^q + y^q) (h_neg : (-a)^q = -a) : (B F q) ≃g (B F q) :=
  { toEquiv := Equiv.sumCongr
      { toFun := tau0_P a ha h_add,
        invFun := tau0_P (-a) h_neg h_add,
        left_inv := by
          intro p; unfold tau0_P; aesop;,
        right_inv := by
          intro p; erw [ tau0_P ] ; erw [ tau0_P ] ; aesop; }
      { toFun := tau0_L a ha,
        invFun := tau0_L (-a) h_neg,
        left_inv := by
          -- Show that applying tau0_L a twice returns the original line.
          intro l
          simp [tau0_L],
        right_inv := by
          -- By definition of tau0_L, applying it twice with a and -a cancels out the changes.
          intros l
          simp [tau0_L] },
    map_rel_iff' := by
      intro x y; rcases x with ( x | x ) <;> rcases y with ( y | y ) <;> simp +decide [ * ] ;
      · simp +decide [ B, is_adjacent ];
      · unfold B; simp +decide [ is_adjacent, tau0_P, tau0_L ] ;
        exact fun _ => ⟨ fun h => by linear_combination h, fun h => by linear_combination h ⟩;
      · simp +decide [ B, is_adjacent ];
        simp +decide [ tau0_L, tau0_P ];
        exact fun _ => ⟨ fun h => by linear_combination h, fun h => by linear_combination h ⟩;
      · unfold B; aesop; }

/-
Definition of the automorphism $\tau_2(b)$ of $B(q)$.
$\tau_2(b)$ maps $p \mapsto \tau_2(b)(p)$ and $l \mapsto \tau_2(b)(l)$.
It preserves the adjacency relation.
-/
/-- The automorphism tau2(b). -/
def tau2 (b : F) (h_add : ∀ x y : F, (x + y)^q = x^q + y^q) (h_F : ∀ x : F, x^(q*q) = x) : (B F q) ≃g (B F q) :=
  { toEquiv := Equiv.sumCongr
      { toFun := tau2_P b,
        invFun := tau2_P (-b),
        left_inv := by
          intro p
          simp [tau2_P],
        right_inv := by
          intro p
          simp [tau2_P] }
      { toFun := tau2_L b h_add h_F,
        invFun := tau2_L (-b) h_add h_F,
        left_inv := by
          -- By definition of tau2_L, we have:
          have h_tau2_L : ∀ l : Line F q, tau2_L (-b) h_add h_F (tau2_L b h_add h_F l) = l := by
            unfold tau2_L;
            simp +decide [ add_assoc, add_left_comm, add_assoc, sub_eq_add_neg ];
            intro l; congr; ring_nf;
            by_cases hq : Even q <;> simp_all +decide;
            have := h_F ( -1 ) ; simp_all +decide [ pow_mul' ] ;
            grind;
          exact h_tau2_L,
        right_inv := by
          intro l;
          unfold tau2_L;
          congr <;> ring_nf;
          by_cases hq : Even q <;> simp_all +decide;
          have := h_F ( -1 ) ; simp_all +decide [ pow_mul' ] ;
          grind },
    map_rel_iff' := by
      intro a b; induction a <;> induction b <;> simp +decide [ *, is_adjacent ] ;
      · unfold B; simp +decide [ tau2_P ] ;
      · unfold B;
        unfold is_adjacent; simp +decide [ * ] ;
        unfold tau2_L tau2_P; simp +decide [ * ] ;
        exact fun _ => ⟨ fun h => by linear_combination h, fun h => by linear_combination h ⟩;
      · unfold B; simp +decide [ is_adjacent, tau2_P, tau2_L ] ;
        intro h; rw [ h_add ] ; ring_nf;
        constructor <;> intro h' <;> linear_combination' h';
      · simp +decide [ B ] }

/-
Definition of the zero point $(0,0,0)$.
-/
def zero_Point (hq : q ≠ 0) : Point F q :=
  { p1 := 0,
    p2 := 0,
    p3 := 0,
    h1 := by
      rw [ zero_pow hq ],
    h3 := by
      rw [ zero_pow hq ] }

/-
$B(q)$ is transitive on $P$. specifically, for any point $p$, there exists an automorphism mapping $p$ to $(0,0,0)$.
-/
theorem B_transitive_on_P
  (hq : q ≠ 0)
  (h_add : ∀ x y : F, (x + y)^q = x^q + y^q)
  (h_F : ∀ x : F, x^(q*q) = x)
  (h_neg : ∀ x : F, (-x)^q = - (x^q))
  (p : Point F q) :
  ∃ phi : (B F q) ≃g (B F q), phi (inl p) = inl (zero_Point hq) := by
  by_contra h_contra;
  -- We need to verify the conditions for the parameters:
  have h_neg_p1 : (-p.p1) ^ q = -p.p1 := by
    rw [ h_neg, p.h1 ]
  have h_neg_p3 : (-p.p3) ^ q = -p.p3 := by
    rw [ h_neg, p.h3 ];
  apply h_contra;
  have h_comp : ∃ (phi : B F q ≃g B F q), (phi : Point F q ⊕ Line F q → Point F q ⊕ Line F q) (Sum.inl p) = Sum.inl (tau2_P (-p.p2) (tau0_P (-p.p1) h_neg_p1 h_add p)) := by
    use tau2 (-p.p2) h_add h_F * tau0 (-p.p1) h_neg_p1 h_add (by
    aesop)
    generalize_proofs at *;
    exact rfl;
  have h_comp : ∃ (phi : B F q ≃g B F q), (phi : Point F q ⊕ Line F q → Point F q ⊕ Line F q) (Sum.inl (tau2_P (-p.p2) (tau0_P (-p.p1) h_neg_p1 h_add p))) = Sum.inl (tau3_P (-p.p3) h_neg_p3 h_add (tau2_P (-p.p2) (tau0_P (-p.p1) h_neg_p1 h_add p))) := by
    refine' ⟨ _, _ ⟩;
    constructor;
    rotate_left;
    refine' Equiv.sumCongr ( Equiv.ofBijective ( tau3_P ( -p.p3 ) h_neg_p3 h_add ) ⟨ _, _ ⟩ ) ( Equiv.ofBijective ( tau3_L ( -p.p3 ) h_neg_p3 h_add ) ⟨ _, _ ⟩ );
    all_goals norm_num [ Function.Injective, Function.Surjective, tau3_P, tau3_L ];
    all_goals norm_num [ SimpleGraph.adj_comm, B ];
    all_goals norm_num [ Sum.inl_ne_inr, Sum.inr_ne_inl, is_adjacent ];
    · exact fun a₁ a₂ h₁ h₂ h₃ => by cases a₁; cases a₂; aesop;
    · exact fun b => ⟨ ⟨ b.p1, b.p2, b.p3 + p.p3, by
        exact b.h1, by
        rw [ h_add, b.h3, p.h3 ] ⟩, by simp +decide ⟩;
    · exact fun a₁ a₂ h₁ h₂ h₃ => by cases a₁; cases a₂; aesop;
    · exact fun b => ⟨ ⟨ b.l1, b.l2, b.l3 + p.p3, by
        rw [ h_add, b.h3, p.h3 ] ⟩, by simp +decide ⟩;
    · exact rfl;
  obtain ⟨ phi, hphi ⟩ := ‹∃ phi : B F q ≃g B F q, ( phi : Point F q ⊕ Line F q → Point F q ⊕ Line F q ) ( Sum.inl p ) = Sum.inl ( tau2_P ( -p.p2 ) ( tau0_P ( -p.p1 ) h_neg_p1 h_add p ) ) ›
  obtain ⟨ ψ, hψ ⟩ := h_comp
  use ψ * phi;
  simp_all +decide [ tau3_P, tau2_P, tau0_P ];
  exact rfl

/-
Definition of the line $[l_1]$ in the 3-path parametrization.
$[l_1] = [x, 0, 0]$.
-/
def path_L1 (x : F) (hq : q ≠ 0) : Line F q :=
  { l1 := x,
    l2 := 0,
    l3 := 0,
    h3 := by
      -- Since $q \neq 0$, we have $0^q = 0$.
      simp [hq] }

/-
Definition of the point $(p_1)$ in the 3-path parametrization.
$(p_1) = (y, -xy, 2yx^{q+1})$.
Requires $y \in \F_q$ and $x \in \F_{q^2}$.
-/
def path_P1 (x y : F) (hy : y^q = y) (h_add : ∀ a b : F, (a + b)^q = a^q + b^q) (h_F : ∀ a : F, a^(q*q) = a) (h_mul : ∀ a b : F, (a * b)^q = a^q * b^q) (h_two : (2 : F)^q = 2) : Point F q :=
  { p1 := y,
    p2 := -x*y,
    p3 := 2*y*x^(q+1),
    h1 := hy,
    h3 := by
      simp_all +decide [ pow_add, pow_mul ];
      exact Or.inl ( mul_comm _ _ ) }

/-
Definition of the line $[l_2]$ in the 3-path parametrization.
$[l_2] = [z, y(z-x), 2yx^{q+1} - y(xz^q + x^q z)]$.
Requires $y \in \F_q$, $x, z \in \F_{q^2}$.
-/
def path_L2 (x y z : F) (hy : y^q = y) (h_add : ∀ a b : F, (a + b)^q = a^q + b^q) (h_F : ∀ a : F, a^(q*q) = a) (h_mul : ∀ a b : F, (a * b)^q = a^q * b^q) (h_two : (2 : F)^q = 2) (h_sub : ∀ a b : F, (a - b)^q = a^q - b^q) : Line F q :=
  { l1 := z,
    l2 := y*(z-x),
    l3 := 2*y*x^(q+1) - y*(x*z^q + x^q*z),
    h3 := by
      rw [ h_sub, h_mul, h_mul ] ; ring_nf;
      simp_all +decide [ pow_two, pow_mul ] ; ring }

/-
Parametrization of any walk of length 3 starting at $(0,0,0)$.
If $(0,0,0) \sim l_1 \sim p_1 \sim l_2$, then $l_1, p_1, l_2$ are determined by their first coordinates $x, y, z$ according to `path_L1`, `path_P1`, `path_L2`.
-/
theorem walk_parametrization
  (hq : q ≠ 0)
  (h_add : ∀ a b : F, (a + b)^q = a^q + b^q)
  (h_mul : ∀ a b : F, (a * b)^q = a^q * b^q)
  (h_sub : ∀ a b : F, (a - b)^q = a^q - b^q)
  (h_F : ∀ a : F, a^(q*q) = a)
  (h_two : (2 : F)^q = 2)
  (l1 : Line F q) (p1 : Point F q) (l2 : Line F q)
  (h_adj1 : is_adjacent F q (zero_Point hq) l1)
  (h_adj2 : is_adjacent F q p1 l1)
  (h_adj3 : is_adjacent F q p1 l2) :
  l1 = path_L1 l1.l1 hq ∧
  p1 = path_P1 l1.l1 p1.p1 p1.h1 h_add h_F h_mul h_two ∧
  l2 = path_L2 l1.l1 p1.p1 l2.l1 p1.h1 h_add h_F h_mul h_two h_sub := by
  -- First we get the coordinates $x = l_1.p1$, $y = p_1.p1$, $z = l_2.p1$ from the given adjacency conditions.
  obtain ⟨hx, hy, hz⟩ : (l1.l2 - 0 = l1.l1 * 0 ∧ l1.l3 - 0 = l1.l1^q * 0 + l1.l1 * 0^q) ∧ (l1.l2 - p1.p2 = l1.l1 * p1.p1 ∧ l1.l3 - p1.p3 = l1.l1^q * p1.p2 + l1.l1 * p1.p2^q) ∧ (l2.l2 - p1.p2 = l2.l1 * p1.p1 ∧ l2.l3 - p1.p3 = l2.l1^q * p1.p2 + l2.l1 * p1.p2^q) := by
    exact ⟨ h_adj1, h_adj2, h_adj3 ⟩
  generalize_proofs at *;
  -- Now use the given conditions to simplify the expressions for $p1$ and $l2$.
  have hp1 : p1.p2 = -l1.l1 * p1.p1 := by
    grind
  have hp2 : p1.p3 = 2 * p1.p1 * l1.l1^(q+1) := by
    simp_all +decide [ pow_succ, mul_assoc, mul_comm, mul_left_comm ];
    rw [ neg_eq_iff_eq_neg ] at hy;
    rw [ hy, neg_add_eq_sub, sub_eq_add_neg ] ; ring_nf;
    by_cases h : Even q <;> simp_all +decide;
    · have := h_F ( -1 ) ; simp_all +decide [ pow_mul ] ;
      grind;
    · ring
  have hl2 : l2.l2 = l2.l1 * p1.p1 - l1.l1 * p1.p1 := by
    linear_combination' hz.1 + hp1
  have hl3 : l2.l3 = 2 * p1.p1 * l1.l1^(q+1) - p1.p1 * (l1.l1 * l2.l1^q + l1.l1^q * l2.l1) := by
    simp_all +decide [ pow_succ, mul_assoc ];
    grind;
  unfold path_L1 path_P1 path_L2; simp_all +decide ;
  simp_all +decide [ mul_sub, sub_mul ];
  simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, pow_succ' ];
  exact ⟨ by cases l1; aesop, by cases p1; aesop, by cases l2; aesop ⟩

/-
There is no 4-cycle passing through $(0,0,0)$ in $B(q)$.
-/
/-
Algebraic identity used in the proof of C6-freeness.
$(y x^{q+1} - y_0 x_0^{q+1})(y - y_0) - (x y - x_0 y_0)(x^q y - x_0^q y_0) = - y y_0 (x - x_0)(x^q - x_0^q)$.
-/
/-
Algebraic step for C6-freeness.
Derives the condition for `algebraic_identity` from the graph equations.
-/
theorem C6_algebraic_step
  (h_add : ∀ a b : F, (a + b)^q = a^q + b^q)
  (h_mul : ∀ a b : F, (a * b)^q = a^q * b^q)
  (h_sub : ∀ a b : F, (a - b)^q = a^q - b^q)
  (h_two_ne_zero : (2 : F) ≠ 0)
  (x x0 y y0 z : F)
  (hy : y^q = y)
  (hy0 : y0^q = y0)
  (h_eq2 : z * (y - y0) = x * y - x0 * y0)
  (h_eq3 : 2 * y * x^(q+1) - y * (x * z^q + x^q * z) = 2 * y0 * x0^(q+1) - y0 * (x0 * z^q + x0^q * z)) :
  (y * x^(q+1) - y0 * x0^(q+1)) * (y - y0) = (x * y - x0 * y0) * (x^q * y - x0^q * y0) := by
  -- Substitute $z(y-y_0) = xy - x_0y_0$ into the equation.
  have h_subst : z * (y - y0) = x * y - x0 * y0 := by
    exact h_eq2;
  have h_subst : z^q * (y - y0) = x^q * y - x0^q * y0 := by
    have := congr_arg ( fun x => x ^ q ) h_subst; norm_num [ h_mul, h_add, h_sub, hy, hy0 ] at this ⊢; aesop;
  grind

/-
Conclusion of the algebraic part of the C6-freeness proof.
Under the graph equations, the product $y y_0 (x - x_0)(x^q - x_0^q)$ is zero.
-/
/-
Uniqueness of simple 3-paths between $(0,0,0)$ and any line $[l_2]$.
This implies no 6-cycle through $(0,0,0)$.
-/
theorem B_no_C6_through_zero
  (hq : q ≠ 0)
  (h_add : ∀ a b : F, (a + b)^q = a^q + b^q)
  (h_mul : ∀ a b : F, (a * b)^q = a^q * b^q)
  (h_sub : ∀ a b : F, (a - b)^q = a^q - b^q)
  (h_F : ∀ a : F, a^(q*q) = a)
  (h_two : (2 : F)^q = 2)
  (h_two_ne_zero : (2 : F) ≠ 0)
  (l1 : Line F q) (p1 : Point F q) (l2 : Line F q)
  (l1' : Line F q) (p1' : Point F q)
  (h_adj1 : is_adjacent F q (zero_Point hq) l1)
  (h_adj2 : is_adjacent F q p1 l1)
  (h_adj3 : is_adjacent F q p1 l2)
  (h_adj1' : is_adjacent F q (zero_Point hq) l1')
  (h_adj2' : is_adjacent F q p1' l1')
  (h_adj3' : is_adjacent F q p1' l2)
  (h_simple1 : p1 ≠ zero_Point hq)
  (h_simple2 : l1 ≠ l2)
  (h_simple1' : p1' ≠ zero_Point hq)
  (h_simple2' : l1' ≠ l2) :
  l1 = l1' ∧ p1 = p1' := by
  have h_walk1 : l1 = path_L1 l1.l1 hq ∧ p1 = path_P1 l1.l1 p1.p1 p1.h1 h_add h_F h_mul h_two ∧ l2 = path_L2 l1.l1 p1.p1 l2.l1 p1.h1 h_add h_F h_mul h_two h_sub := by
    exact walk_parametrization hq h_add h_mul h_sub h_F h_two l1 p1 l2 h_adj1 h_adj2 h_adj3;
  have h_walk1' : l1' = path_L1 l1'.l1 hq ∧ p1' = path_P1 l1'.l1 p1'.p1 p1'.h1 h_add h_F h_mul h_two ∧ l2 = path_L2 l1'.l1 p1'.p1 l2.l1 p1'.h1 h_add h_F h_mul h_two h_sub := by
    apply walk_parametrization hq h_add h_mul h_sub h_F h_two l1' p1' l2 h_adj1' h_adj2' h_adj3';
  have h_eq : p1.p1 * p1'.p1 * (l1.l1 - l1'.l1) * (l1.l1^q - l1'.l1^q) = 0 := by
    have h_eq : p1.p1 * p1'.p1 * (l1.l1 - l1'.l1) * (l1.l1^q - l1'.l1^q) = 0 := by
      have h_eq2 : l2.l1 * (p1.p1 - p1'.p1) = p1.p1 * l1.l1 - p1'.p1 * l1'.l1 := by
        unfold path_L2 at *; simp +decide [ mul_comm, mul_assoc, mul_left_comm ] at *;
        grind
      have h_eq3 : 2 * p1.p1 * l1.l1^(q+1) - p1.p1 * (l1.l1 * l2.l1^q + l1.l1^q * l2.l1) = 2 * p1'.p1 * l1'.l1^(q+1) - p1'.p1 * (l1'.l1 * l2.l1^q + l1'.l1^q * l2.l1) := by
        have h_eq3 : l2.l3 = 2 * p1.p1 * l1.l1^(q+1) - p1.p1 * (l1.l1 * l2.l1^q + l1.l1^q * l2.l1) := by
          exact h_walk1.2.2.symm ▸ rfl;
        have h_eq3' : l2.l3 = 2 * p1'.p1 * l1'.l1^(q+1) - p1'.p1 * (l1'.l1 * l2.l1^q + l1'.l1^q * l2.l1) := by
          exact h_walk1'.2.2.symm ▸ rfl;
        rw [ ← h_eq3, ← h_eq3' ]
      have h_eq : (p1.p1 * l1.l1^(q+1) - p1'.p1 * l1'.l1^(q+1)) * (p1.p1 - p1'.p1) = (p1.p1 * l1.l1 - p1'.p1 * l1'.l1) * (p1.p1 * l1.l1^q - p1'.p1 * l1'.l1^q) := by
        convert C6_algebraic_step h_add h_mul h_sub h_two_ne_zero _ _ _ _ _ _ _ _ _ using 1;
        any_goals exact h_eq3;
        · ring;
        · exact p1.h1;
        · exact p1'.h1;
        · linear_combination' h_eq2;
      grind;
    exact h_eq;
  have h_eq : l1.l1 = l1'.l1 := by
    have h_eq : p1.p1 ≠ 0 ∧ p1'.p1 ≠ 0 := by
      constructor <;> intro h <;> simp +decide [ h ] at *;
      · unfold path_P1 at h_walk1;
        exact h_simple1 ( by simpa [ ‹p1.p1 = 0› ] using h_walk1.2.1 );
      · simp +decide [ ‹p1'.p1 = 0›, path_P1 ] at h_walk1';
        exact h_simple1' ( h_walk1'.2.1.trans ( by rfl ) );
    have h_eq : (l1.l1 - l1'.l1) ^ (q + 1) = 0 := by
      grind;
    exact sub_eq_zero.mp ( pow_eq_zero h_eq );
  have h_eq : p1.p1 = p1'.p1 := by
    simp +decide [ path_L2 ] at *;
    simp +decide [ path_L1 ] at *;
    grind +ring;
  grind

/-
Helper lemma: if $y, y_0, x-x_0$ are non-zero, then their product with $x^q-x_0^q$ is non-zero.
-/
/-
Definition of $B_S(q)$ as the induced subgraph of $B(q)$ on $P_S \cup L$.
$P_S = \{ p \in P \mid p_1 \in S \}$.
-/
/-- The subset of points P_S determined by S. -/
def P_S (S : Set F) : Set (Point F q) :=
  { p | p.p1 ∈ S }

/-- The vertex set of B_S(q). -/
def V_S (S : Set F) : Set (Point F q ⊕ Line F q) :=
  { v | match v with
    | inl p => p ∈ P_S S
    | inr _ => True }

/-- The subgraph B_S(q) induced by P_S and all lines L. -/
def B_S (S : Set F) :=
  (B F q).induce (V_S S)

/-
Fintype instances for Point and Line.
-/
variable {F : Type*} [Field F] [Fintype F] {q : ℕ}

noncomputable instance : Fintype (Point F q) := by
  have : Fintype { p : F × F × F // p.1 ^ q = p.1 ∧ p.2.2 ^ q = p.2.2 } := inferInstance
  exact Fintype.ofEquiv { p : F × F × F // p.1 ^ q = p.1 ∧ p.2.2 ^ q = p.2.2 }
    { toFun := fun p => { p1 := p.1.1, p2 := p.1.2.1, p3 := p.1.2.2, h1 := p.2.1, h3 := p.2.2 },
      invFun := fun p => ⟨(p.p1, p.p2, p.p3), ⟨p.h1, p.h3⟩⟩,
      left_inv := by intro p; simp,
      right_inv := by intro p; cases p; simp }

noncomputable instance : Fintype (Line F q) := by
  have : Fintype { l : F × F × F // l.2.2 ^ q = l.2.2 } := inferInstance
  exact Fintype.ofEquiv { l : F × F × F // l.2.2 ^ q = l.2.2 }
    { toFun := fun l => { l1 := l.1.1, l2 := l.1.2.1, l3 := l.1.2.2, h3 := l.2 },
      invFun := fun l => ⟨(l.l1, l.l2, l.l3), l.h3⟩,
      left_inv := by intro l; simp,
      right_inv := by intro l; cases l; simp }

/-
Fintype instance for the vertex set of B_S(q).
-/
variable {F : Type*} [Field F] [Fintype F] {q : ℕ}

noncomputable instance (S : Set F) [DecidablePred (· ∈ S)] : Fintype (@V_S F _ q S) :=
  inferInstanceAs (Fintype { v : Point F q ⊕ Line F q // v ∈ @V_S F _ q S })

/-
Fintype instance for V_S.
-/
variable {F : Type*} [Field F] [Fintype F] {q : ℕ}

noncomputable instance (S : Set F) [DecidablePred (· ∈ S)] : Fintype (V_S (q := q) S) :=
  have : Fintype (Point F q ⊕ Line F q) := inferInstance
  Fintype.ofFinite (V_S (q := q) S)

/-
DecidableRel instance for B.
-/
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {q : ℕ}

instance instDecidableRelB : DecidableRel (B F q).Adj := by
  intros v w
  unfold B
  dsimp [SimpleGraph.fromRel]
  cases v <;> cases w <;> simp [is_adjacent] <;> exact inferInstance

/-
The degree of any point $p \in P_S$ in $B_S(q)$ is $|F| = q^2$.
-/
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {q : ℕ}

/-
For any $x \in S$ and line $l$, there is a unique point $p$ with $p_1 = x$ adjacent to $l$.
-/
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {q : ℕ}

theorem unique_neighbor_with_x_coord
  (S : Set F)
  (l : Line F q)
  (x : F)
  (hx : x ∈ S)
  (h_add : ∀ a b : F, (a + b)^q = a^q + b^q)
  (h_mul : ∀ a b : F, (a * b)^q = a^q * b^q)
  (h_F : ∀ a : F, a^(q*q) = a)
  (h_sub : ∀ a b : F, (a - b)^q = a^q - b^q)
  (h_S : ∀ a ∈ S, a^q = a) :
  ∃! p : Point F q, p.p1 = x ∧ is_adjacent F q p l := by
  refine' ⟨ ⟨ x, l.l2 - l.l1 * x, l.l3 - ( l.l1 ^ q ) * ( l.l2 - l.l1 * x ) - l.l1 * ( l.l2 - l.l1 * x ) ^ q, h_S x hx, _ ⟩, ⟨ rfl, _ ⟩, _ ⟩;
  all_goals simp_all +decide [ is_adjacent ]
  all_goals generalize_proofs at *;
  · have := h_F l.l3; have := h_F l.l1; have := h_F l.l2; simp_all +decide [ pow_mul', mul_assoc, mul_comm, mul_left_comm ] ;
    rw [ l.h3 ] ; ring;
  · ring;
  · simp_all +decide [ sub_eq_iff_eq_add ];
    simp +decide [ add_assoc, add_sub_assoc ];
    exact fun y hy₁ hy₂ hy₃ => by cases y; aesop;

/-
DecidableRel instance for B_S (v3, explicit q).
-/
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {q : ℕ}

instance instDecidableRelBS_v3 (S : Set F) [DecidablePred (· ∈ S)] : DecidableRel (B_S (q := q) S).Adj := by
  intros a b
  unfold B_S
  dsimp [SimpleGraph.induce]
  have : Decidable ((B F q).Adj a.val b.val) := inferInstance
  exact this

/-
DecidableRel instance for B_S (v4, explicit arguments).
-/
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {q : ℕ}

instance instDecidableRelBS_v4 (S : Set F) [DecidablePred (· ∈ S)] : DecidableRel (@B_S F _ q S).Adj := by
  intros a b
  change Decidable ((B F q).Adj a.val b.val)
  exact inferInstance

/-
For any point $p$ and $l_1 \in F$, there is a unique line $l$ with first coordinate $l_1$ adjacent to $p$.
-/
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {q : ℕ}

/-
The degree of any line $l \in L$ in $B_S(q)$ is $|S|$.
-/
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {q : ℕ}

/-
The number of points in $P_S$ adjacent to a line $l$ is $|S|$.
-/
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {q : ℕ}

theorem card_neighbors_in_P_S
  (S : Set F)
  [DecidablePred (· ∈ S)]
  (l : Line F q)
  (h_add : ∀ a b : F, (a + b)^q = a^q + b^q)
  (h_mul : ∀ a b : F, (a * b)^q = a^q * b^q)
  (h_F : ∀ a : F, a^(q*q) = a)
  (h_sub : ∀ a b : F, (a - b)^q = a^q - b^q)
  (h_S : ∀ a ∈ S, a^q = a) :
  Set.ncard { p : Point F q | p ∈ P_S S ∧ is_adjacent F q p l } = Set.ncard S := by
  rw [ Set.ncard_def, Set.ncard_def, Set.encard_congr ];
  refine' Equiv.symm ( Equiv.ofBijective _ ⟨ _, _ ⟩ );
  refine' fun x => ⟨ Classical.choose ( unique_neighbor_with_x_coord S l x x.2 h_add h_mul h_F h_sub h_S ), _ ⟩;
  all_goals norm_num [ Function.Injective, Function.Surjective ];
  · have := Classical.choose_spec ( unique_neighbor_with_x_coord S l x x.2 h_add h_mul h_F h_sub h_S ) |>.1
    generalize_proofs at *;
    unfold P_S; aesop;
  · intro a ha b hb hab;
    have := Classical.choose_spec ( unique_neighbor_with_x_coord S l a ha h_add h_mul h_F h_sub h_S ) |>.1; have := Classical.choose_spec ( unique_neighbor_with_x_coord S l b hb h_add h_mul h_F h_sub h_S ) |>.1; aesop;
  · intro p hp h_adj
    generalize_proofs at *;
    rename_i h;
    exact ⟨ p.p1, hp, Classical.choose_spec ( h p.p1 hp ) |>.2 p rfl h_adj ▸ rfl ⟩

/-
The degree of any point $p \in P_S$ in $B_S(q)$ is $|F| = q^2$.
-/
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {q : ℕ}

/-
`C6_free`: A graph is $C_6$-free if it contains no cycle of length 6.
`card_Line`: The number of lines is $q^5$.
-/
def C6_free {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (u : V) (w : G.Walk u u), w.IsCycle → w.length ≠ 6

theorem card_Line
  (h_card_F : Fintype.card F = q * q)
  (h_card_fixed : Fintype.card { x : F // x^q = x } = q) :
  Fintype.card (Line F q) = q^5 := by
    have h_card_lines : Fintype.card (Line F q) = Fintype.card F * Fintype.card F * Fintype.card { x : F // x^q = x } := by
      rw [ ← Fintype.card_prod ];
      rw [ ← Fintype.card_prod ];
      refine' Fintype.card_congr _;
      refine' Equiv.ofBijective ( fun l => ⟨ ⟨ l.l1, l.l2 ⟩, ⟨ l.l3, l.h3 ⟩ ⟩ ) ⟨ fun a b h => _, fun a => _ ⟩;
      · cases a ; cases b ; aesop;
      · exact ⟨ ⟨ a.1.1, a.1.2, a.2.1, a.2.2 ⟩, rfl ⟩;
    exact h_card_lines.trans ( by rw [ h_card_F, h_card_fixed ] ; ring )

/-
No cycle of length 6 passes through $(0,0,0)$ in $B(q)$.
-/
theorem B_no_C6_through_zero_cycle
  (hq : q ≠ 0)
  (h_add : ∀ a b : F, (a + b)^q = a^q + b^q)
  (h_mul : ∀ a b : F, (a * b)^q = a^q * b^q)
  (h_sub : ∀ a b : F, (a - b)^q = a^q - b^q)
  (h_F : ∀ a : F, a^(q*q) = a)
  (h_two : (2 : F)^q = 2)
  (h_two_ne_zero : (2 : F) ≠ 0)
  (w : (B F q).Walk (Sum.inl (zero_Point hq)) (Sum.inl (zero_Point hq)))
  (hw : w.IsCycle)
  (hlen : w.length = 6) :
  False := by
    rcases w with ( _ | ⟨ u, _ | ⟨ v, _ | ⟨ w, _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | w ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ) <;> simp_all +decide [ SimpleGraph.Walk.cons_isCycle_iff ];
    unfold B at *; simp_all +decide [ SimpleGraph.adj_comm ] ;
    rename_i a b c d e;
    rcases a with ( a | a ) <;> rcases b with ( b | b ) <;> rcases c with ( c | c ) <;> rcases d with ( d | d ) <;> rcases e with ( e | e ) <;> simp_all +decide [ is_adjacent ] ;
    -- By `B_no_C6_through_zero`, we must have $a = e$ and $b = d$.
    have h_eq : a = e ∧ b = d := by
      apply B_no_C6_through_zero hq h_add h_mul h_sub h_F h_two h_two_ne_zero a b c e d;
      all_goals tauto;
    aesop

/-
$B(q)$ contains no cycle of length 6.
-/
theorem B_C6_free
  (hq : q ≠ 0)
  (h_add : ∀ a b : F, (a + b)^q = a^q + b^q)
  (h_mul : ∀ a b : F, (a * b)^q = a^q * b^q)
  (h_sub : ∀ a b : F, (a - b)^q = a^q - b^q)
  (h_F : ∀ a : F, a^(q*q) = a)
  (h_two : (2 : F)^q = 2)
  (h_two_ne_zero : (2 : F) ≠ 0)
  (h_neg : ∀ x : F, (-x)^q = - (x^q)) :
  C6_free (B F q) := by
    -- To prove that $B(q)$ is $C_6$-free, we show that there is no cycle of length 6 passing through $(0,0,0)$ and then use the transitivity on $P$ to conclude.
    have h_no_C6 : ∀ p : Point F q, ¬∃ w : (B F q).Walk (Sum.inl p) (Sum.inl p), w.IsCycle ∧ w.length = 6 := by
      -- By `B_transitive_on_P`, there is an automorphism $\phi$ mapping $p$ to $(0,0,0)$.
      intro p
      obtain ⟨phi, hphi⟩ := B_transitive_on_P hq h_add h_F h_neg p;
      intro ⟨w, hw_cycle, hw_length⟩
      have h_image_cycle : ∃ w' : (B F q).Walk (Sum.inl (zero_Point hq)) (Sum.inl (zero_Point hq)), w'.IsCycle ∧ w'.length = 6 := by
        have h_image_cycle : ∃ w' : (B F q).Walk (phi (Sum.inl p)) (phi (Sum.inl p)), w'.IsCycle ∧ w'.length = 6 := by
          use w.map phi.toHom;
          simp_all +decide [ SimpleGraph.Walk.isCycle_def ];
          simp_all +decide [ SimpleGraph.Walk.isTrail_def, List.nodup_map_iff_inj_on ];
          refine' ⟨ _, _, _ ⟩;
          · intro x hx y hy hxy; rcases x with ⟨ u, v ⟩ ; rcases y with ⟨ u', v' ⟩ ; aesop;
          · cases w <;> simp_all +decide [ SimpleGraph.Walk.map ];
          · rw [ List.nodup_iff_injective_get ] at *;
            intro i j hij; have := hw_cycle.1; simp_all +decide [ Function.Injective ] ;
            have := @hw_cycle.2.2; simp_all +decide [ List.nodup_iff_injective_get ] ;
            have := @hw_cycle.2.2 ⟨ i, by
              exact i.2.trans_le ( by simp +decide [ hw_length ] ) ⟩ ⟨ j, by
              exact j.2.trans_le ( by simp +decide [ hw_length ] ) ⟩ ; aesop;
        grind;
      exact B_no_C6_through_zero_cycle hq h_add h_mul h_sub h_F h_two h_two_ne_zero h_image_cycle.choose h_image_cycle.choose_spec.1 h_image_cycle.choose_spec.2;
    intro u w hw hlen;
    contrapose! h_no_C6;
    rcases u with ( u | u ) <;> simp_all +decide [ SimpleGraph.Walk.isCycle_def ];
    · exact ⟨ u, w, hw, hlen ⟩;
    · cases w <;> simp_all +decide [ SimpleGraph.Walk.isTrail_def ];
      rename_i v hv hw;
      rcases v with ( v | v ) <;> simp_all +decide [ SimpleGraph.Walk.edges ];
      · rename_i w;
        refine' ⟨ v, w.append ( SimpleGraph.Walk.cons hv SimpleGraph.Walk.nil ), _, _ ⟩ <;> simp_all +decide [ SimpleGraph.Walk.length_append ];
        simp_all +decide [ List.nodup_append, SimpleGraph.Walk.support_append ];
        rcases w with ( _ | ⟨ _, _, w ⟩ ) <;> simp_all +decide [ SimpleGraph.Walk.support ];
        grind +ring;
      · exact absurd hv ( by unfold B; simp +decide [ SimpleGraph.fromRel ] )

/-
Definition of the graph $G$ obtained by deleting a set of lines $D$ from $B_S(q)$.
$V(G) = P_S \cup (L \setminus D)$.
$G$ is the induced subgraph of $B(q)$ on $V(G)$.
-/
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {q : ℕ}

/-- The vertex set of the graph G obtained by deleting D from L in B_S(q). -/
def V_G (S : Set F) (D : Set (Line F q)) : Set (Point F q ⊕ Line F q) :=
  { v | match v with
    | Sum.inl p => p ∈ P_S S
    | Sum.inr l => l ∉ D }

/-- The graph G obtained by deleting D from L in B_S(q). -/
def B_G (S : Set F) (D : Set (Line F q)) :=
  (B F q).induce (V_G S D)

noncomputable instance (S : Set F) (D : Set (Line F q)) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ D)] : Fintype (V_G (q := q) S D) :=
  Fintype.ofFinite _

instance (S : Set F) (D : Set (Line F q)) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ D)] : DecidableRel (B_G (q := q) S D).Adj :=
  fun a b => inferInstanceAs (Decidable ((B F q).Adj a.val b.val))

/-
The graph $G$ is $C_6$-free.
-/
theorem B_G_C6_free
  (S : Set F)
  (D : Set (Line F q))
  (hq : q ≠ 0)
  (h_add : ∀ a b : F, (a + b)^q = a^q + b^q)
  (h_mul : ∀ a b : F, (a * b)^q = a^q * b^q)
  (h_sub : ∀ a b : F, (a - b)^q = a^q - b^q)
  (h_F : ∀ a : F, a^(q*q) = a)
  (h_two : (2 : F)^q = 2)
  (h_two_ne_zero : (2 : F) ≠ 0)
  (h_neg : ∀ x : F, (-x)^q = - (x^q)) :
  C6_free (B_G (q := q) S D) := by
    -- Assume there exists a cycle of length 6 in $B_G$.
    intro w hw hw_cycle hw_length;
    -- Since $B_G$ is an induced subgraph of $B(q)$, any cycle in $B_G$ is also a cycle in $B(q)$.
    have h_cycle_in_B : ∃ c : (B F q).Walk w.val w.val, c.IsCycle ∧ c.length = 6 := by
      refine' ⟨ _, _, _ ⟩;
      exact hw.map ( SimpleGraph.Hom.comap _ _ );
      · convert hw_cycle.map _;
        intro a b hab;
        cases a ; cases b ; aesop;
      · rw [ Walk.length_map, hw_length ];
    -- Apply the fact that B(q) is C6-free to obtain a contradiction.
    obtain ⟨c, hc_cycle, hc_length⟩ := h_cycle_in_B;
    have := B_C6_free hq h_add h_mul h_sub h_F h_two h_two_ne_zero h_neg;
    exact this w.val c hc_cycle hc_length

/-
The number of edges in $G$ is $|S|(q^5 - |D|)$.
-/
theorem B_G_edge_count
  (S : Set F)
  (D : Set (Line F q))
  [DecidablePred (· ∈ S)]
  [DecidablePred (· ∈ D)]
  (h_add : ∀ a b : F, (a + b)^q = a^q + b^q)
  (h_mul : ∀ a b : F, (a * b)^q = a^q * b^q)
  (h_F : ∀ a : F, a^(q*q) = a)
  (h_sub : ∀ a b : F, (a - b)^q = a^q - b^q)
  (h_S : ∀ a ∈ S, a^q = a)
  (h_card_F : Fintype.card F = q * q)
  (h_card_fixed : Fintype.card { x : F // x^q = x } = q) :
  (B_G (q := q) S D).edgeFinset.card = S.ncard * (q^5 - D.ncard) := by
    have h_card_D : Set.ncard D = Fintype.card (Finset.filter (fun l => l ∈ D) Finset.univ) := by
      simp +decide [ Set.ncard_eq_toFinset_card' ];
    simp_all +decide [ Fintype.card_subtype ];
    have h_card_edges : Fintype.card { e : (Line F q) × (Point F q) // e.2 ∈ P_S S ∧ e.1 ∉ D ∧ is_adjacent F q e.2 e.1 } = (q^5 - Fintype.card (Finset.filter (fun l => l ∈ D) Finset.univ)) * Set.ncard S := by
      have h_card_edges : ∀ l : Line F q, l ∉ D → Fintype.card { p : Point F q // p ∈ P_S S ∧ is_adjacent F q p l } = Set.ncard S := by
        intro l hl;
        have := card_neighbors_in_P_S S l h_add h_mul h_F h_sub h_S;
        rw [ ← this, Set.ncard_eq_toFinset_card' ];
        rw [ Set.toFinset_card ];
        convert rfl;
      have h_card_edges : Fintype.card { e : (Line F q) × (Point F q) // e.2 ∈ P_S S ∧ e.1 ∉ D ∧ is_adjacent F q e.2 e.1 } = ∑ l ∈ Finset.univ.filter (fun l => l ∉ D), Fintype.card { p : Point F q // p ∈ P_S S ∧ is_adjacent F q p l } := by
        simp +decide only [Fintype.card_subtype];
        simp +decide only [Finset.card_filter];
        rw [ Finset.sum_comm ];
        rw [ Finset.sum_sigma' ];
        rw [ ← Finset.sum_filter ];
        rw [ ← Finset.sum_filter ];
        refine' Finset.sum_bij ( fun x hx => ⟨ x.2, x.1 ⟩ ) _ _ _ _ <;> simp +contextual;
        exact fun b hb₁ hb₂ hb₃ => ⟨ _, _, ⟨ hb₂, hb₁, hb₃ ⟩, rfl ⟩;
      rw [ h_card_edges, Finset.sum_congr rfl fun x hx => ‹∀ l ∉ D, Fintype.card { p // p ∈ P_S S ∧ is_adjacent F q p l } = S.ncard› x <| by simpa using hx ] ; simp +decide [ Finset.filter_not, Finset.card_sdiff ] ; ring_nf;
      rw [ card_Line ] ; ring_nf ; aesop;
      · exact h_card_F;
      · rw [ Fintype.card_subtype ] ; aesop;
    convert h_card_edges using 1;
    · rw [ ← Set.ncard_coe_finset ];
      rw [ ← Set.ncard_congr ];
      convert Set.ncard_coe_finset _;
      use fun a _ => Sym2.mk ( ⟨ Sum.inr a.val.1, by simp [ V_G ] ; exact a.2.2.1 ⟩, ⟨ Sum.inl a.val.2, by simp [ V_G ] ; exact a.2.1 ⟩ );
      · simp +decide [ is_adjacent, B_G ];
        exact fun a b hb ha h1 h2 => by unfold B; simp +decide [ *, is_adjacent ] ;
      · simp +contextual [ Sym2.eq_iff ];
      · rintro ⟨ a, b ⟩ h; cases a ; cases b ; simp_all +decide [ Sym2.eq_swap ] ;
        cases ‹Point F q ⊕ Line F q› <;> cases ‹Point F q ⊕ Line F q› <;> simp_all +decide [ B_G ];
        · cases h;
          tauto;
        · unfold B at h; aesop;
        · unfold B at h; aesop;
        · cases h;
          tauto;
    · rw [ mul_comm, Fintype.subtype_card ];
      simp +decide

/-
The size of $P_S$ is $|S| \cdot q^3$.
-/
theorem card_P_S
  (S : Set F)
  [DecidablePred (· ∈ S)]
  (h_card_F : Fintype.card F = q * q)
  (h_card_fixed : Fintype.card { x : F // x^q = x } = q)
  (h_S : ∀ a ∈ S, a^q = a) :
  Fintype.card (P_S (q := q) S) = S.ncard * q^3 := by
    rw [ Set.ncard_eq_toFinset_card' ];
    rw [ Fintype.card_of_subtype ];
    case s => exact Finset.image ( fun x : { x // x ∈ S } × { x // x ^ q = x } × F => ⟨ x.1.val, x.2.2, x.2.1.val, h_S _ x.1.2, x.2.1.2 ⟩ ) ( Finset.univ );
    · rw [ Finset.card_image_of_injective ];
      · simp +decide [ *, pow_succ', mul_assoc ];
      · intro x y hxy; aesop;
    · simp +decide [ P_S ];
      exact fun x => ⟨ fun ⟨ a, ha, b, hb, c, hc ⟩ => hc ▸ ha, fun hx => ⟨ x.p1, hx, x.p3, x.h3, x.p2, rfl ⟩ ⟩

/-
For any $c > 0$, there exist $q, k, y$ such that $q$ is prime, $y \le q^5$, the partition size condition is met, and the edge density is at least $c$.
-/
lemma exists_parameters (c : ℝ) (hc : c > 0) :
  ∃ (q k y : ℕ),
    Nat.Prime q ∧
    y ≤ q^5 ∧
    k * q^3 = ⌊((k * q^3 : ℝ) + y) ^ (2/3 : ℝ)⌋₊ ∧
    (y * k : ℝ) ≥ c * (k * q^3 + y) := by
      simp +zetaDelta at *;
      refine' ⟨ 2, Nat.prime_two, 0, 0, _, _, _ ⟩ <;> norm_num

/-
For any $c > 0$, there exist $q, k, y$ such that $q$ is prime, $k \ge 1$, $k \le q$, $y \le q^5$, the partition size condition is met, and the edge density is at least $c$.
-/
lemma exists_parameters_useful (c : ℝ) (hc : c > 0) :
  ∃ (q k y : ℕ),
    Nat.Prime q ∧
    k ≥ 1 ∧
    k ≤ q ∧
    y ≤ q^5 ∧
    k * q^3 = ⌊((k * q^3 : ℝ) + y) ^ (2/3 : ℝ)⌋₊ ∧
    (y * k : ℝ) ≥ c * (k * q^3 + y) := by
      -- Choose a large prime $q$ such that $q \ge k$ and $q$ is large enough for the asymptotic approximations.
      obtain ⟨q, hq_prime, hq_ge_k, hq_large⟩ : ∃ q : ℕ, Nat.Prime q ∧ q ≥ Nat.floor (2 * c) + 1 ∧ q > (Nat.floor (2 * c) + 1)^3 := by
        have := Nat.exists_infinite_primes ( ( ⌊2 * c⌋₊ + 1 ) ^ 3 + 1 );
        exact ⟨ this.choose, this.choose_spec.2, by nlinarith [ this.choose_spec.1, pow_succ' ( ⌊2 * c⌋₊ + 1 ) 2 ], this.choose_spec.1 ⟩;
      -- Let $k = \lfloor 2c \rfloor + 1$.
      set k := Nat.floor (2 * c) + 1;
      -- Let $y$ be an integer in the interval $[x^{3/2} - x, (x+1)^{3/2} - x)$.
      obtain ⟨y, hy_bounds⟩ : ∃ y : ℕ, (k * q^3 : ℝ)^(3 / 2 : ℝ) - k * q^3 ≤ y ∧ y < ((k * q^3 + 1) : ℝ)^(3 / 2 : ℝ) - k * q^3 := by
        refine' ⟨ ⌈ ( ( k : ℝ ) * q ^ 3 ) ^ ( 3 / 2 : ℝ ) - ( k : ℝ ) * q ^ 3⌉₊, _, _ ⟩ <;> norm_num;
        · linarith [ Nat.le_ceil ( ( ( k : ℝ ) * q ^ 3 ) ^ ( 3 / 2 : ℝ ) - ( k : ℝ ) * q ^ 3 ) ];
        · refine' lt_of_le_of_lt ( Nat.ceil_lt_add_one _ |> le_of_lt ) _;
          · exact sub_nonneg_of_le ( by exact le_trans ( by norm_num ) ( Real.rpow_le_rpow_of_exponent_le ( mod_cast Nat.one_le_iff_ne_zero.mpr <| by aesop ) <| show ( 3 : ℝ ) / 2 ≥ 1 by norm_num ) );
          · rw [ show ( 3 / 2 : ℝ ) = 1 + 1 / 2 by norm_num, Real.rpow_add', Real.rpow_add' ] <;> norm_num <;> try positivity;
            rw [ ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow ];
            nlinarith only [ show 1 ≤ ( k : ℝ ) * q ^ 3 by exact one_le_mul_of_one_le_of_one_le ( mod_cast Nat.succ_pos _ ) ( mod_cast pow_pos hq_prime.pos _ ), Real.sqrt_nonneg ( ( k : ℝ ) * q ^ 3 ), Real.sqrt_le_sqrt ( show ( k : ℝ ) * q ^ 3 ≤ ( k : ℝ ) * q ^ 3 + 1 by linarith ), Real.mul_self_sqrt ( show 0 ≤ ( k : ℝ ) * q ^ 3 by positivity ), Real.mul_self_sqrt ( show 0 ≤ ( k : ℝ ) * q ^ 3 + 1 by positivity ) ];
      refine' ⟨ q, k, y, hq_prime, _, _, _, _, _ ⟩ <;> norm_num at * <;> try linarith;
      · exact Nat.succ_pos _;
      · -- Since $q$ is large, we have $((k * q^3 + 1) : ℝ)^(3 / 2 : ℝ) - k * q^3 < q^5$.
        have hy_bound : ((k * q^3 + 1) : ℝ)^(3 / 2 : ℝ) - k * q^3 < q^5 := by
          -- Since $q$ is large, we have $(k * q^3 + 1)^{3/2} < k * q^3 + q^5$.
          have hy_bound : ((k * q^3 + 1) : ℝ)^(3 / 2 : ℝ) < k * q^3 + q^5 := by
            -- Squaring both sides to remove the square root.
            have hy_sq : ((k * q^3 + 1) : ℝ)^3 < (k * q^3 + q^5)^2 := by
              norm_cast;
              simp +zetaDelta at *;
              ring_nf;
              rw [ show ⌊c * 2⌋₊ = ⌊2 * c⌋₊ by ring_nf ];
              nlinarith [ Nat.zero_le ( ⌊2 * c⌋₊ ^ 3 ), Nat.zero_le ( ⌊2 * c⌋₊ ^ 2 * q ^ 3 ), Nat.zero_le ( ⌊2 * c⌋₊ * q ^ 6 ), Nat.zero_le ( q ^ 9 ), Nat.zero_le ( q ^ 8 ), Nat.zero_le ( q ^ 7 ), Nat.zero_le ( q ^ 6 ), Nat.zero_le ( q ^ 5 ), Nat.zero_le ( q ^ 4 ), Nat.zero_le ( q ^ 3 ), Nat.zero_le ( q ^ 2 ), Nat.zero_le ( q ^ 1 ), Nat.zero_le ( q ^ 0 ), pow_pos hq_prime.pos 3, pow_pos hq_prime.pos 4, pow_pos hq_prime.pos 5, pow_pos hq_prime.pos 6, pow_pos hq_prime.pos 7, pow_pos hq_prime.pos 8, pow_pos hq_prime.pos 9 ];
            contrapose! hy_sq;
            exact le_trans ( pow_le_pow_left₀ ( by positivity ) hy_sq 2 ) ( by rw [ ← Real.rpow_natCast _ 2, ← Real.rpow_mul ( by positivity ) ] ; norm_num );
          linarith;
        exact_mod_cast hy_bounds.2.le.trans hy_bound.le;
      · rw [ eq_comm, Nat.floor_eq_iff ];
        · field_simp;
          norm_num +zetaDelta at *;
          constructor;
          · rw [ Real.le_rpow_iff_log_le ];
            · rw [ div_mul_eq_mul_div, le_div_iff₀' ] <;> norm_num;
              rw [ ← Real.log_rpow, ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_cast <;> norm_num;
              · rw [ ← @Nat.cast_le ℝ ] ; norm_num;
                rw [ show ( ( ⌊2 * c⌋₊ + 1 ) * q ^ 3 : ℝ ) ^ 3 = ( ( ⌊2 * c⌋₊ + 1 ) * q ^ 3 ) ^ ( 3 / 2 : ℝ ) * ( ( ⌊2 * c⌋₊ + 1 ) * q ^ 3 ) ^ ( 3 / 2 : ℝ ) by rw [ ← Real.rpow_add ( by exact mul_pos ( by positivity ) ( pow_pos ( Nat.cast_pos.mpr hq_prime.pos ) _ ) ) ] ; norm_num ] ; nlinarith [ show 0 ≤ ( ( ⌊2 * c⌋₊ + 1 ) * q ^ 3 : ℝ ) ^ ( 3 / 2 : ℝ ) by positivity ];
              · exact pow_pos ( mul_pos ( Nat.succ_pos _ ) ( pow_pos hq_prime.pos _ ) ) _;
              · exact pow_pos ( by nlinarith [ pow_pos hq_prime.pos 3 ] ) _;
              · exact Or.inl ( pow_pos hq_prime.pos _ );
              · exact pow_pos hq_prime.pos _;
            · exact mul_pos ( by positivity ) ( pow_pos ( Nat.cast_pos.mpr hq_prime.pos ) _ );
            · exact add_pos_of_pos_of_nonneg ( mul_pos ( by positivity ) ( pow_pos ( Nat.cast_pos.mpr hq_prime.pos ) 3 ) ) ( Nat.cast_nonneg _ );
          · field_simp;
            refine' lt_of_lt_of_le ( Real.rpow_lt_rpow ( by positivity ) ( show ( ( ⌊2 * c⌋₊ + 1 ) * q ^ 3 + y : ℝ ) < ( ( ⌊2 * c⌋₊ + 1 ) * q ^ 3 + 1 ) ^ ( 3 / 2 : ℝ ) by linarith ) ( by positivity ) ) _;
            rw [ ← Real.rpow_mul ( by positivity ) ] ; norm_num;
        · positivity;
      · -- Since $q$ is large, we have $y \approx x^{3/2} = k^{1.5} q^{4.5}$.
        have hy_approx : (y : ℝ) ≥ k * q^3 := by
          have hy_approx : (k * q^3 : ℝ)^(3 / 2 : ℝ) ≥ 2 * (k * q^3 : ℝ) := by
            have hy_approx : (k * q^3 : ℝ) ≥ 2^2 := by
              norm_cast;
              exact le_trans ( by nlinarith [ Nat.pow_le_pow_left hq_prime.two_le 3 ] ) ( Nat.mul_le_mul ( Nat.succ_le_succ <| Nat.zero_le _ ) <| Nat.pow_le_pow_left hq_prime.two_le 3 );
            rw [ show ( ( k : ℝ ) * q ^ 3 ) ^ ( 3 / 2 : ℝ ) = ( ( k : ℝ ) * q ^ 3 ) * Real.sqrt ( ( k : ℝ ) * q ^ 3 ) by rw [ Real.sqrt_eq_rpow, ← Real.rpow_one_add' ] <;> norm_num ; positivity ] ; nlinarith [ Real.sqrt_nonneg ( ( k : ℝ ) * q ^ 3 ), Real.mul_self_sqrt ( show 0 ≤ ( k : ℝ ) * q ^ 3 by positivity ) ];
          linarith;
        simp +zetaDelta at *;
        nlinarith [ Nat.lt_floor_add_one ( 2 * c ), show ( q : ℝ ) ^ 3 > 0 by exact pow_pos ( Nat.cast_pos.mpr hq_prime.pos ) 3 ]

/-
For any $c > 0$, there exist $q, k, y$ such that $q$ is an odd prime, $k \ge 1$, $k \le q$, $y \le q^5$, the partition size condition is met, and the edge density is at least $c$.
-/
lemma exists_parameters_useful_odd (c : ℝ) (hc : c > 0) :
  ∃ (q k y : ℕ),
    Nat.Prime q ∧
    q > 2 ∧
    k ≥ 1 ∧
    k ≤ q ∧
    y ≤ q^5 ∧
    k * q^3 = ⌊((k * q^3 : ℝ) + y) ^ (2/3 : ℝ)⌋₊ ∧
    (y * k : ℝ) ≥ c * (k * q^3 + y) := by
      obtain ⟨ q, k, y, hq_prime, hk₁, hk₂, hy₁, hk₃, hy₂ ⟩ := exists_parameters_useful ( Max.max c 3 ) ( by positivity );
      refine ⟨ q, k, y, hq_prime, ?_, hk₁, hk₂, hy₁, hk₃, le_trans ( mul_le_mul_of_nonneg_right ( le_max_left _ _ ) <| by positivity ) hy₂ ⟩;
      contrapose! hy₂; interval_cases q <;> norm_num at *;
      interval_cases k <;> norm_num at *;
      · nlinarith [ le_max_right c 3 ];
      · interval_cases y <;> norm_num at hk₃ ⊢ <;> linarith [ le_max_left c 3, le_max_right c 3 ]

/-
There exists a field $F$ of size $q^2$ and characteristic $q$, a subset $S$ of fixed points of size $k$, and a subset $D$ of lines of size $q^5 - y$.
-/
lemma exists_field_and_sets (q k y : ℕ) (hq : Nat.Prime q) (hk : k ≤ q) (hy : y ≤ q^5) :
  ∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : DecidableEq F) (S : Finset F) (D : Finset (Line F q)),
    Fintype.card F = q * q ∧
    CharP F q ∧
    (∀ x ∈ S, x^q = x) ∧
    S.card = k ∧
    D.card = q^5 - y := by
      obtain ⟨F, x, x_1, x_2, S, D, h_card_F, h_char, h_fixed_points, h_card_S, h_card_D⟩ : ∃ (F : Type) (x : Field F) (x_1 : Fintype F) (x_2 : DecidableEq F) (S : Finset F), Fintype.card F = q * q ∧ CharP F q ∧ (∀ x_3 ∈ S, x_3 ^ q = x_3) ∧ S.card = k := by
        haveI := Fact.mk hq;
        use (GaloisField q 2);
        -- Let $S_0 = \{x \in F \mid x^q = x\}$. Then $|S_0| = q$.
        obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Finset (GaloisField q 2), S₀.card = q ∧ ∀ x ∈ S₀, x ^ q = x := by
          have hS₀ : ∃ S₀ : Finset (GaloisField q 2), S₀.card = q ∧ ∀ x ∈ S₀, x ^ q = x := by
            have h_poly : Finset.card (Multiset.toFinset (Polynomial.roots (Polynomial.X ^ q - Polynomial.X : Polynomial (GaloisField q 2)))) = q := by
              have h_poly : Polynomial.Splits (algebraMap (GaloisField q 2) (GaloisField q 2)) (Polynomial.X ^ q - Polynomial.X : Polynomial (GaloisField q 2)) := by
                have h_splits : Polynomial.Splits (algebraMap (ZMod q) (GaloisField q 2)) (Polynomial.X ^ q - Polynomial.X : Polynomial (ZMod q)) := by
                  have h_splits : Polynomial.Splits (algebraMap (ZMod q) (GaloisField q 2)) (Polynomial.X ^ q - Polynomial.X : Polynomial (ZMod q)) := by
                    have h_poly : (Polynomial.X ^ q - Polynomial.X : Polynomial (ZMod q)) = Polynomial.C 1 * (∏ x ∈ Finset.univ, (Polynomial.X - Polynomial.C x)) := by
                      refine' Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq _ _ _;
                      exact Finset.univ;
                      · convert Polynomial.degree_sub_lt _ _ _ <;> norm_num [ Polynomial.degree_prod, Polynomial.degree_X_pow_sub_C ];
                        · rw [ Polynomial.degree_sub_eq_left_of_degree_lt ] <;> norm_num [ hq.one_lt ];
                        · rw [ Polynomial.degree_sub_eq_left_of_degree_lt ] <;> norm_num [ hq.one_lt ];
                        · exact ne_of_apply_ne ( Polynomial.derivative ) ( by norm_num [ Polynomial.derivative_pow, hq.ne_zero ] );
                        · rw [ Polynomial.leadingCoeff_prod ];
                          rw [ Polynomial.leadingCoeff_sub_of_degree_lt ] <;> norm_num [ hq.one_lt ];
                      · intro x; simp +decide [ Finset.prod_eq_prod_diff_singleton_mul ( Finset.mem_univ x ) ] ;
                    rw [ h_poly ];
                    simp +decide [ Polynomial.splits_prod ];
                    exact Polynomial.splits_prod _ fun x _ => Polynomial.splits_X_sub_C _;
                  exact h_splits;
                convert h_splits using 1;
                rw [ Polynomial.splits_iff_exists_multiset, Polynomial.splits_iff_exists_multiset ];
                erw [ Polynomial.leadingCoeff_sub_of_degree_lt ] <;> norm_num [ hq.one_lt ];
                erw [ Polynomial.leadingCoeff_sub_of_degree_lt ] <;> norm_num [ hq.one_lt ];
              erw [ Polynomial.splits_iff_card_roots ] at h_poly;
              rw [ Multiset.toFinset_card_of_nodup ];
              · rw [ h_poly, Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> norm_num [ hq.one_lt ];
              · refine' Polynomial.nodup_roots _;
                refine' IsCoprime.symm _;
                norm_num [ Polynomial.derivative_pow ];
                exact isCoprime_one_left.neg_left
            exact ⟨ _, h_poly, fun x hx => by simpa [ sub_eq_zero ] using Polynomial.isRoot_of_mem_roots ( Multiset.mem_toFinset.mp hx ) ⟩;
          exact hS₀;
        -- Since $k \le q$, we can choose a subset $S \subseteq S_0$ of size $k$.
        obtain ⟨S, hS⟩ : ∃ S : Finset (GaloisField q 2), S ⊆ S₀ ∧ S.card = k := by
          exact Finset.exists_subset_card_eq ( by linarith );
        refine' ⟨ _, _, _, S, _, _, _, hS.2 ⟩;
        all_goals try infer_instance
        generalize_proofs at *;
        exact Fintype.ofFinite _;
        · rw [ Fintype.card_eq_nat_card ];
          simp +decide [ GaloisField.card ];
          ring;
        · exact fun x hx => hS₀.2 x ( hS.1 hx );
      have h_card_lines : Fintype.card (Line F q) = q^5 := by
        convert card_Line ( show Fintype.card F = q * q from D ) _;
        haveI := Fact.mk hq; simp_all +decide [ ← sq ] ;
        have h_fixed_points : (Finset.filter (fun x => x^q = x) (Finset.univ : Finset F)).card = q := by
          have h_fixed_points : (Finset.filter (fun x => x^q = x) (Finset.univ : Finset F)).card = q := by
            have h_poly : (Finset.filter (fun x => x^q = x) (Finset.univ : Finset F)) = Multiset.toFinset (Polynomial.roots (Polynomial.X^q - Polynomial.X : Polynomial F)) := by
              ext; simp [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X];
              exact ⟨ fun h => ⟨ by exact ne_of_apply_ne Polynomial.natDegree <| by rw [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> norm_num <;> linarith [ hq.two_le ], sub_eq_zero.mpr h ⟩, fun h => sub_eq_zero.mp h.2 ⟩
            have h_poly_roots : (Polynomial.X^q - Polynomial.X : Polynomial F).roots.toFinset.card = q := by
              have h_poly_splits : Polynomial.Splits (algebraMap F F) (Polynomial.X^q - Polynomial.X : Polynomial F) := by
                have h_poly_splits : Polynomial.Splits (algebraMap F F) (Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial F) := by
                  have h_poly_splits : Polynomial.Splits (algebraMap F F) (Polynomial.X ^ (Fintype.card F) - Polynomial.X : Polynomial F) := by
                    exact
                      Polynomial.IsSplittingField.splits F
                        (Polynomial.X ^ Fintype.card F - Polynomial.X);
                  aesop;
                have h_poly_div : (Polynomial.X ^ q - Polynomial.X : Polynomial F) ∣ (Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial F) := by
                  have h_poly_div : (Polynomial.X ^ q - Polynomial.X : Polynomial F) ∣ (Polynomial.X ^ (q ^ 2) - Polynomial.X ^ q : Polynomial F) := by
                    rw [ show q ^ 2 = q * q by ring, pow_mul ];
                    exact dvd_trans ( by norm_num ) ( sub_dvd_pow_sub_pow _ _ _ );
                  convert h_poly_div.add ( dvd_refl ( Polynomial.X ^ q - Polynomial.X ) ) using 1 ; ring;
                obtain ⟨ p, hp ⟩ := h_poly_div;
                rw [ hp, Polynomial.splits_mul_iff ] at h_poly_splits ; aesop;
                · exact ne_of_apply_ne Polynomial.natDegree ( by rw [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> norm_num <;> linarith [ hq.two_le ] );
                · intro h; simp_all +decide [ sub_eq_iff_eq_add ] ;
                  replace hp := congr_arg Polynomial.natDegree hp ; simp_all +decide [ Polynomial.natDegree_X_pow, hq.ne_zero ]
              have h_poly_roots : (Polynomial.X^q - Polynomial.X : Polynomial F).roots.toFinset.card = Polynomial.natDegree (Polynomial.X^q - Polynomial.X : Polynomial F) := by
                have h_poly_roots : Multiset.card (Polynomial.roots (Polynomial.X^q - Polynomial.X : Polynomial F)) = Polynomial.natDegree (Polynomial.X^q - Polynomial.X : Polynomial F) := by
                  simp_all +decide [ Polynomial.splits_iff_card_roots ];
                rw [ ← h_poly_roots, Multiset.toFinset_card_of_nodup ];
                refine' Polynomial.nodup_roots _;
                have h_poly_separable : Polynomial.Separable (Polynomial.X^q - Polynomial.X : Polynomial F) := by
                  have h_poly_deriv : Polynomial.derivative (Polynomial.X^q - Polynomial.X : Polynomial F) = -1 := by
                    norm_num [ Polynomial.derivative_pow, hq.ne_zero ]
                  exact ⟨ 0, -1, by aesop ⟩;
                exact h_poly_separable;
              rw [ h_poly_roots, Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> norm_num [ hq.one_lt ];
            aesop;
          exact h_fixed_points;
        rw [ Fintype.card_subtype ] ; aesop;
      use F, x, x_1, x_2, S;
      have := Finset.exists_subset_card_eq ( show q ^ 5 - y ≤ Fintype.card ( Line F q ) from by rw [ h_card_lines ] ; exact Nat.sub_le _ _ ) ; aesop;

/-
The number of vertices in $B_G(S, D)$ is $k q^3 + y$.
-/
lemma B_G_card_V (q k y : ℕ)
  (hq_prime : Nat.Prime q)
  (hk_le_q : k ≤ q)
  (hy_le_lines : y ≤ q^5)
  (F : Type*) [Field F] [Fintype F] [DecidableEq F]
  (S : Finset F) (D : Finset (Line F q))
  (h_card_F : Fintype.card F = q * q)
  (h_card_fixed : Fintype.card { x : F // x^q = x } = q)
  (h_fixed : ∀ x ∈ S, x^q = x)
  (h_card_S : S.card = k)
  (h_card_D : D.card = q^5 - y) :
  Fintype.card (V_G (q := q) (S : Set F) (D : Set (Line F q))) = k * q^3 + y := by
    have h_card_V_G : Fintype.card (V_G (↑S : Set F) (↑D : Set (Line F q))) = Fintype.card (P_S (q := q) (↑S : Set F)) + Fintype.card (Set.diff (Set.univ : Set (Line F q)) (D : Set (Line F q))) := by
      rw [ Fintype.card_subtype, Fintype.card_subtype, Fintype.card_subtype ];
      rw [ Finset.card_filter, Finset.card_filter, Finset.card_filter ];
      rw [ ← Finset.sum_add_sum_compl ];
      swap;
      exact Finset.image ( fun x : Point F q => Sum.inl x ) Finset.univ ∪ Finset.image ( fun x : Line F q => Sum.inr x ) Finset.univ;
      rw [ Finset.sum_union, Finset.sum_image, Finset.sum_image ] <;> simp +decide [ Finset.disjoint_right ];
      simp +decide [ V_G, Set.diff ];
    have h_card_P_S : Fintype.card (P_S (q := q) (↑S : Set F)) = k * q^3 := by
      convert card_P_S ( S : Set F ) h_card_F h_card_fixed h_fixed ; aesop;
    have h_card_lines : Fintype.card (Line F q) = q^5 := by
      convert card_Line h_card_F h_card_fixed using 1;
    simp +decide [ *, Set.diff ];
    rw [ Nat.sub_sub_self hy_le_lines ]

/-
If $F$ is a field of size $q^2$ and characteristic $q$, then the number of elements $x \in F$ such that $x^q = x$ is $q$.
-/
lemma card_fixed_points_of_card_eq_qsq
  (F : Type*) [Field F] [Fintype F] [DecidableEq F]
  (q : ℕ) [Fact q.Prime]
  (h_card : Fintype.card F = q * q)
  (h_char : CharP F q) :
  Fintype.card { x : F // x^q = x } = q := by
    -- The polynomial $X^q - X$ splits completely in $F$ since $F$ is a finite field of order $q^2$.
    have h_poly_splits : Polynomial.Splits (algebraMap F F) (Polynomial.X ^ q - Polynomial.X : Polynomial F) := by
      have h_card : Fintype.card F = q ^ 2 := by
        rw [ h_card, pow_two ];
      have h_poly_splits : Polynomial.Splits (algebraMap F F) (Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial F) := by
        have h_poly_splits : Polynomial.Splits (algebraMap F F) (Polynomial.X ^ (Fintype.card F) - Polynomial.X : Polynomial F) := by
          have h_finite_field : ∀ x : F, x ^ (Fintype.card F) = x := by
            exact FiniteField.pow_card
          exact Polynomial.IsSplittingField.splits F (Polynomial.X ^ Fintype.card F - Polynomial.X);
        rwa [ h_card ] at h_poly_splits;
      have h_poly_div : (Polynomial.X ^ q - Polynomial.X : Polynomial F) ∣ (Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial F) := by
        have h_poly_div : (Polynomial.X ^ q - Polynomial.X : Polynomial F) ∣ (Polynomial.X ^ (q * q) - Polynomial.X ^ q : Polynomial F) := by
          simpa only [ pow_mul ] using sub_dvd_pow_sub_pow _ _ _;
        convert dvd_add h_poly_div ( dvd_refl ( Polynomial.X ^ q - Polynomial.X ) ) using 1 ; ring;
      obtain ⟨ g, hg ⟩ := h_poly_div;
      rw [ hg, Polynomial.splits_mul_iff ] at h_poly_splits ; aesop;
      · exact ne_of_apply_ne Polynomial.natDegree ( by rw [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> norm_num <;> linarith [ show q > 1 from Fact.out ] );
      · intro h; simp_all +decide [ sub_eq_iff_eq_add ] ;
        replace hg := congr_arg Polynomial.natDegree hg ; simp_all +decide [ Polynomial.natDegree_X_pow ];
    have h_roots_count : (Polynomial.X ^ q - Polynomial.X : Polynomial F).roots.toFinset.card = q := by
      have h_roots_count : (Polynomial.X ^ q - Polynomial.X : Polynomial F).roots.toFinset.card = Polynomial.natDegree (Polynomial.X ^ q - Polynomial.X : Polynomial F) := by
        erw [ Multiset.toFinset_card_of_nodup ];
        · erw [ Polynomial.splits_iff_card_roots ] at h_poly_splits ; aesop;
        · refine' Polynomial.nodup_roots _;
          refine' IsCoprime.symm _;
          refine' ⟨ -1, Polynomial.C ( q : F ) ⁻¹, _ ⟩;
          simp +decide [ Polynomial.derivative_pow, Polynomial.derivative_X, Polynomial.derivative_C ];
      rw [ h_roots_count, Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> norm_num [ Nat.Prime.one_lt Fact.out ];
    rw [ Fintype.card_subtype ];
    convert h_roots_count using 2 ; ext x ; simp +decide [ sub_eq_zero ] ; aesop

/-
The graph $B_G(S, D)$ has $k q^3 + y$ vertices, $ky$ edges, is $C_6$-free, and $|P_S| = k q^3$.
-/
lemma B_G_properties (q k y : ℕ)
  (hq_prime : Nat.Prime q)
  (hq_odd : q > 2)
  (hk_le_q : k ≤ q)
  (hy_le_lines : y ≤ q^5)
  (F : Type*) [Field F] [Fintype F] [DecidableEq F]
  (S : Finset F) (D : Finset (Line F q))
  (h_card_F : Fintype.card F = q * q)
  (h_char : CharP F q)
  (h_fixed : ∀ x ∈ S, x^q = x)
  (h_card_S : S.card = k)
  (h_card_D : D.card = q^5 - y) :
  let G := B_G (q := q) (S : Set F) (D : Set (Line F q))
  Fintype.card (V_G (q := q) (S : Set F) (D : Set (Line F q))) = k * q^3 + y ∧
  G.edgeFinset.card = k * y ∧
  C6_free G ∧
  Fintype.card (P_S (q := q) (S : Set F)) = k * q^3 := by
    have h_fixed_points : Fintype.card { x : F // x ^ q = x } = q := by
      convert card_fixed_points_of_card_eq_qsq F q h_card_F h_char;
      exact ⟨ hq_prime ⟩;
    have h_alg_id : (∀ a b : F, (a + b) ^ q = a ^ q + b ^ q) ∧ (∀ a b : F, (a * b) ^ q = a ^ q * b ^ q) ∧ (∀ a b : F, (a - b) ^ q = a ^ q - b ^ q) ∧ (∀ a : F, a ^ (q * q) = a) ∧ (2 : F) ^ q = 2 ∧ (2 : F) ≠ 0 ∧ (∀ x : F, (-x) ^ q = - (x ^ q)) := by
      have h_alg_id : (∀ a b : F, (a + b) ^ q = a ^ q + b ^ q) ∧ (∀ a b : F, (a * b) ^ q = a ^ q * b ^ q) ∧ (∀ a b : F, (a - b) ^ q = a ^ q - b ^ q) ∧ (∀ a : F, a ^ (q * q) = a) ∧ (2 : F) ^ q = 2 ∧ (2 : F) ≠ 0 ∧ (∀ x : F, (-x) ^ q = -x ^ q) := by
        have h_add : ∀ a b : F, (a + b) ^ q = a ^ q + b ^ q := by
          haveI := Fact.mk hq_prime; simp +decide [ add_pow_char ] ;
        have h_mul : ∀ a b : F, (a * b) ^ q = a ^ q * b ^ q := by
          exact fun a b => mul_pow a b q
        have h_sub : ∀ a b : F, (a - b) ^ q = a ^ q - b ^ q := by
          haveI := Fact.mk hq_prime; simp +decide [ sub_pow_char ] ;
        have h_F : ∀ a : F, a ^ (q * q) = a := by
          exact fun x => by rw [ ← h_card_F, FiniteField.pow_card ] ;
        have h_two : (2 : F) ^ q = 2 := by
          rw [ show ( 2 : F ) = 1 + 1 by norm_num, h_add, show ( 1 : F ) ^ q = 1 by rw [ one_pow ] ]
        have h_two_ne_zero : (2 : F) ≠ 0 := by
          have := CharP.cast_eq_zero_iff F q 2;
          exact fun h => absurd ( this.mp h ) ( Nat.not_dvd_of_pos_of_lt ( by decide ) hq_odd )
        have h_neg : ∀ x : F, (-x) ^ q = -x ^ q := by
          intro x; specialize h_sub 0 x; aesop;
        exact ⟨h_add, h_mul, h_sub, h_F, h_two, h_two_ne_zero, h_neg⟩;
      exact h_alg_id;
    norm_num +zetaDelta at *;
    refine' ⟨ _, _, _, _ ⟩;
    · convert B_G_card_V q k y hq_prime hk_le_q hy_le_lines F S D h_card_F h_fixed_points h_fixed h_card_S h_card_D using 1;
    · convert B_G_edge_count ( q := q ) ( S := S ) ( D := D ) ( fun a b => h_alg_id.1 a b ) ( fun a b => h_alg_id.2.1 a b ) ( fun a => h_alg_id.2.2.2.1 a ) ( fun a b => h_alg_id.2.2.1 a b ) ( fun a => by aesop ) h_card_F h_fixed_points using 1;
      · simp +decide [ SimpleGraph.edgeFinset ];
      · simp +decide [ *, Set.ncard_eq_toFinset_card' ];
        exact Or.inl ( by rw [ Nat.sub_sub_self hy_le_lines ] );
    · apply B_G_C6_free;
      all_goals try linarith;
      all_goals tauto;
    · convert card_P_S ( S : Set F ) h_card_F h_fixed_points h_fixed;
      · rw [ Fintype.card_of_subtype ] ; aesop;
      · rw [ Set.ncard_coe_finset, h_card_S ]

/-
If a graph $G$ on $n$ vertices has an independent set $A$ such that $A^c$ is also independent, and $G$ is $C_6$-free, then there exists an isomorphic graph on `Fin n` with the same properties.
-/
lemma transfer_to_fin_n {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  (A : Finset V)
  (n : ℕ)
  (hn : Fintype.card V = n)
  (h_indep_A : ∀ x y, x ∈ A → y ∈ A → ¬ G.Adj x y)
  (h_indep_Ac : ∀ x y, x ∉ A → y ∉ A → ¬ G.Adj x y)
  (h_C6 : C6_free G) :
  ∃ (G' : SimpleGraph (Fin n)) (A' : Finset (Fin n)),
    (∀ x y, x ∈ A' → y ∈ A' → ¬ G'.Adj x y) ∧
    (∀ x y, x ∉ A' → y ∉ A' → ¬ G'.Adj x y) ∧
    A'.card = A.card ∧
    (G'.edgeFinset.card : ℝ) = G.edgeFinset.card ∧
    C6_free G' := by
      have h_bij : ∃ e : V ≃ Fin n, True := by
        exact ⟨ Fintype.equivOfCardEq ( by simp +decide [ hn ] ), trivial ⟩;
      obtain ⟨ e, - ⟩ := h_bij;
      refine' ⟨ _, _, _, _, _, _, _ ⟩;
      exact SimpleGraph.comap ( fun x => e.symm x ) G;
      exact Finset.image ( fun x => e x ) A;
      · aesop;
      · simp_all +decide [ Finset.mem_image, SimpleGraph.comap ];
        exact fun x y hx hy => h_indep_Ac _ _ ( fun h => hx _ h ( by simp +decide [ e.symm_apply_eq ] ) ) ( fun h => hy _ h ( by simp +decide [ e.symm_apply_eq ] ) );
      · exact Finset.card_image_of_injective _ e.injective;
      · simp +decide [ SimpleGraph.comap, SimpleGraph.edgeFinset ];
        refine' Finset.card_bij ( fun x hx => Sym2.map e.symm x ) _ _ _ <;> simp +decide;
        · rintro ⟨ u, v ⟩ huv ; aesop;
        · rintro ⟨ u, v ⟩ huv ⟨ u', v' ⟩ huv' h; rw [ Sym2.map_pair_eq, Sym2.map_pair_eq ] at h; aesop;
        · rintro ⟨ u, v ⟩ huv; use Sym2.mk ( e u, e v ) ; aesop;
      · intro u w hw hlen;
        convert h_C6 ( e.symm u ) ( w.map ( SimpleGraph.Hom.comap _ _ ) ) _ _;
        · convert hw.map _;
          exact e.symm.injective;
        · simp +decide [ hlen ]

/-
There exists a bipartite graph on $n$ vertices with partition size $\lfloor n^{2/3} \rfloor$, $ky$ edges, and no $C_6$.
-/
lemma exists_counterexample_graph (q k y : ℕ)
  (hq_prime : Nat.Prime q)
  (hq_odd : q > 2)
  (hk_le_q : k ≤ q)
  (hy_le_lines : y ≤ q^5)
  (n : ℕ)
  (hn : n = k * q^3 + y)
  (hk_size : k * q^3 = ⌊(n : ℝ) ^ (2/3 : ℝ)⌋₊)
  (hk_pos : k ≥ 1) :
  ∃ (G : SimpleGraph (Fin n)) (A : Finset (Fin n)),
    (∀ x y, x ∈ A → y ∈ A → ¬ G.Adj x y) ∧
    (∀ x y, x ∉ A → y ∉ A → ¬ G.Adj x y) ∧
    A.card = ⌊(n : ℝ) ^ (2/3 : ℝ)⌋₊ ∧
    (G.edgeFinset.card : ℝ) = k * y ∧
    (∀ (u : Fin n) (w : G.Walk u u), w.IsCycle → w.length ≠ 6) := by
      have := exists_field_and_sets q k y hq_prime hk_le_q hy_le_lines;
      obtain ⟨ F, _, _, _, S, D, hF_card, hF_char, hS_fixed, hS_card, hD_card ⟩ := this;
      have := B_G_properties q k y hq_prime hq_odd hk_le_q hy_le_lines F S D hF_card hF_char hS_fixed hS_card hD_card;
      -- Let $A_{orig}$ be the set of points in $G_{orig}$.
      set A_orig := Finset.univ.filter (fun p : V_G (S : Set F) (D : Set (Line F q)) => p.val.isLeft) with hA_orig_def;
      have hA_orig_card : A_orig.card = k * q^3 := by
        convert this.2.2.2 using 1;
        rw [ Fintype.card_of_subtype ];
        rotate_left;
        exact Finset.univ.filter fun p => p.p1 ∈ S;
        · simp +decide [ P_S ];
        · refine' Finset.card_bij ( fun p hp => p.val.elim ( fun p => p ) fun l => by
            exact ⟨ 0, 0, 0, by
              rw [ zero_pow hq_prime.ne_zero ], by
              rw [ zero_pow hq_prime.ne_zero ] ⟩
            skip ) _ _ _ <;> simp +decide [ hA_orig_def ];
          · exact fun a b => b;
          · exact fun p hp => by exact Set.mem_setOf.mpr ( by simpa using hp ) ;
      have := transfer_to_fin_n (B_G (S : Set F) (D : Set (Line F q))) A_orig n (by
      grind) (by
      simp +zetaDelta at *;
      unfold B_G; simp +decide [ SimpleGraph.fromRel_adj ] ;
      unfold B; simp +decide [ SimpleGraph.fromRel_adj ] ;) (by
      simp +zetaDelta at *;
      unfold B_G; simp +decide [ SimpleGraph.adj_comm ] ;
      unfold B; simp +decide [ SimpleGraph.adj_comm ] ;) (by
      exact this.2.2.1);
      obtain ⟨ G', A', hA'_indep_A, hA'_indep_Ac, hA'_card, hG'_edgeFinset_card, hG'_C6_free ⟩ := this;
      norm_num +zetaDelta at *;
      exact ⟨ G', A', hA'_indep_A, hA'_indep_Ac, by linarith, by norm_cast; linarith, hG'_C6_free ⟩

/-
There is no constant $c$ such that every bipartite graph with parts of size $n^{2/3}$ and $n - n^{2/3}$ and $cn$ edges contains a $C_6$.
-/
theorem thm_counterexamples_nonempty :
  ¬ ∃ c > 0, ∀ (n : ℕ) (G : SimpleGraph (Fin n))
    [Nonempty (Fin n)] [DecidableRel G.Adj],
    (∃ (A : Finset (Fin n)),
        (∀ x y, x ∈ A → y ∈ A → ¬ G.Adj x y) ∧
        (∀ x y, x ∉ A → y ∉ A → ¬ G.Adj x y) ∧
        A.card = ⌊(n : ℝ) ^ (2/3 : ℝ)⌋₊) →
    (G.edgeFinset.card : ℝ) ≥ c * n →
      ∃ (u : Fin n) (w : G.Walk u u), w.IsCycle ∧ w.length = 6 := by
  push_neg;
  intro c hc;
  -- Use `exists_parameters_useful_odd` with this $c$ to find parameters $q, k, y$ such that $q$ is an odd prime, $k \ge 1$, $k \le q$, $y \le q^5$, $k q^3 = \lfloor (k q^3 + y)^{2/3} \rfloor$, and $ky \ge c(k q^3 + y)$.
  obtain ⟨q, k, y, hq_prime, hq_odd, hk_le_q, hy_le_lines, hk_size, hk_pos, hk_edges⟩ : ∃ q k y : ℕ,
    Nat.Prime q ∧
    q > 2 ∧
    k ≥ 1 ∧
    k ≤ q ∧
    y ≤ q^5 ∧
    k * q^3 = ⌊((k * q^3 : ℝ) + y) ^ (2/3 : ℝ)⌋₊ ∧
    (y * k : ℝ) ≥ c * (k * q^3 + y) := by
      exact exists_parameters_useful_odd c hc;
  -- Use `exists_counterexample_graph` with these parameters to obtain a graph $G$ on $n$ vertices and a set $A$ such that:
  -- 1. $A$ and $A^c$ are independent sets (so $G$ is bipartite with parts $A, A^c$).
  -- 2. $|A| = \lfloor n^{2/3} \rfloor$.
  -- 3. $|E(G)| = ky$.
  -- 4. $G$ has no $C_6$.
  obtain ⟨G, A, hA_card, hA_indep, hA_c_indep, hG_edges, hG_no_C6⟩ : ∃ (G : SimpleGraph (Fin (k * q^3 + y))) (A : Finset (Fin (k * q^3 + y))),
    (∀ x y, x ∈ A → y ∈ A → ¬ G.Adj x y) ∧
    (∀ x y, x ∉ A → y ∉ A → ¬ G.Adj x y) ∧
    A.card = ⌊((k * q^3 + y : ℝ) ^ (2/3 : ℝ))⌋₊ ∧
    (G.edgeFinset.card : ℝ) = k * y ∧
    (∀ (u : Fin (k * q^3 + y)) (w : G.Walk u u), w.IsCycle → w.length ≠ 6) := by
      have := exists_counterexample_graph q k y hq_prime hq_odd hy_le_lines hk_size;
      exact_mod_cast this _ rfl ( mod_cast hk_pos ) hk_le_q;
  simp +zetaDelta at *;
  refine' ⟨ k * q ^ 3 + y, _, G, _, _, _ ⟩;
  · exact ⟨ ⟨ 0, by positivity ⟩ ⟩;
  · exact ⟨ A, hA_card, hA_indep, by simpa using hA_c_indep ⟩;
  · exact ⟨ inferInstance, by push_cast; linarith ⟩;
  · exact hG_no_C6

/-!
# Erdős Problem 1080

*Reference:* [erdosproblems.com/1080](https://www.erdosproblems.com/1080)
-/

open SimpleGraph

/-- `IsBipartition G X Y` means that `X` and `Y` form a bipartition of the vertices of `G`. -/
def IsBipartition {V : Type*} (G : SimpleGraph V) (X Y : Set V) : Prop :=
  Disjoint X Y ∧ X ∪ Y = Set.univ ∧ ∀ ⦃u v⦄, G.Adj u v → (u ∈ X ↔ v ∈ Y)

/--
Let $G$ be a bipartite graph on $n$ vertices such that one part has $\lfloor n^{2/3}\rfloor$
vertices. Is there a constant $c>0$ such that if $G$ has at least $cn$ edges then $G$ must
contain a $C_6$?
-/
def erdos_1080 : Prop :=
    ∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) (X Y : Set V),
      IsBipartition G X Y → X.ncard = ⌊(Fintype.card V : ℝ) ^ (2/3 : ℝ)⌋₊ →
      G.edgeSet.ncard ≥ c * Fintype.card V →
        ∃ (v : V) (walk : G.Walk v v), walk.IsCycle ∧ walk.length = 6

/-
No.
-/
def not_erdos_1080 : ¬erdos_1080 := by
  intro h;
  obtain ⟨ c, hc₀, hc ⟩ := h;
  apply thm_counterexamples_nonempty;
  refine' ⟨ c, hc₀, fun n G _ _ h1 h2 => _ ⟩;
  obtain ⟨ A, hA₁, hA₂, hA₃ ⟩ := h1;
  specialize hc ( Fin n ) G ( A : Set ( Fin n ) ) ( Aᶜ : Set ( Fin n ) ) ; simp_all +decide [ IsBipartition ];
  simp_all +decide [ Set.disjoint_left ];
  exact hc ( fun u v huv => by have := hA₁ u v; have := hA₂ u v; by_cases hu : u ∈ A <;> by_cases hv : v ∈ A <;> simp_all +decide [ SimpleGraph.adj_comm ] ) ( by simpa [ Set.ncard_eq_toFinset_card' ] using h2 )

#print axioms not_erdos_1080
-- 'not_erdos_1080' depends on axioms: [propext, Classical.choice, Quot.sound]
