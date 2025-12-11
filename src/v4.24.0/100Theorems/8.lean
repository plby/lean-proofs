/-

This is a Lean formalization of

8: The Impossibility of Trisecting the Angle and Doubling the Cube


This was proven by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7

-/

import Mathlib


/-- `Constructible x` means: the real number `x` can be obtained from rational
numbers by a finite sequence of field operations and extraction of square
roots of nonnegative reals.  This matches the classical notion of a
straightedge-and-compass constructible real length (starting from a unit
segment), up to the usual identifications. -/
inductive Constructible : ℝ → Prop
  | rat (q : ℚ) :
      Constructible (q : ℝ)
  | add {x y : ℝ} (hx : Constructible x) (hy : Constructible y) :
      Constructible (x + y)
  | neg {x : ℝ} (hx : Constructible x) :
      Constructible (-x)
  | mul {x y : ℝ} (hx : Constructible x) (hy : Constructible y) :
      Constructible (x * y)
  | inv {x : ℝ} (hx : Constructible x) (hx0 : x ≠ 0) :
      Constructible x⁻¹
  | sqrt {x : ℝ} (hx : Constructible x) (hx0 : 0 ≤ x) :
      Constructible (Real.sqrt x)

open Constructible

/-- A real angle `θ` (in radians) is (classically) constructible if its cosine
is a constructible real length. -/
def ConstructibleAngle (θ : ℝ) : Prop :=
  Constructible (Real.cos θ)

/- **Impossibility of doubling the cube**: there is no constructible real
length whose cube is `2`.  Equivalently, `∛2` is not straightedge-and-compass
constructible. -/
noncomputable section AristotleLemmas

/-
A field K has a quadratic tower if there is a finite sequence of fields starting from Q (bottom) to K, where each step is obtained by adjoining a square root of an element from the previous field.
-/
def HasQuadTower (K : IntermediateField ℚ ℝ) : Prop :=
  ∃ (k : ℕ) (F : ℕ → IntermediateField ℚ ℝ),
    F 0 = ⊥ ∧ F k = K ∧
    ∀ i, i < k → ∃ x : ℝ, x ^ 2 ∈ F i ∧ F (i + 1) = IntermediateField.adjoin ℚ (F i ∪ {x})

/-
If x^2 is in K, then the degree of K(x) over K is 1 or 2.
Proof: The minimal polynomial of x over K divides X^2 - x^2.
So the degree of the minimal polynomial is at most 2.
The degree of the extension is the degree of the minimal polynomial.
So it is at most 2.
Since it's a field extension, the degree is at least 1.
So it is 1 or 2.
-/
lemma degree_adjoin_sq (K : IntermediateField ℚ ℝ) (x : ℝ) (hx : x^2 ∈ K) :
    Module.finrank K (IntermediateField.adjoin K {x}) = 1 ∨ Module.finrank K (IntermediateField.adjoin K {x}) = 2 := by
  -- Since $x^2 \in K$, the minimal polynomial of $x$ over $K$ divides $X^2 - x^2$, which has degree 2.
  have h_min_deg : Polynomial.degree (minpoly K x) ≤ 2 := by
    have h_min_div : minpoly K x ∣ (Polynomial.X ^ 2 - Polynomial.C (⟨x ^ 2, hx⟩ : K)) := by
      refine' minpoly.dvd K x _;
      bound;
    exact le_trans ( Polynomial.degree_le_of_dvd h_min_div ( Polynomial.X_pow_sub_C_ne_zero ( by norm_num ) _ ) ) ( by erw [ Polynomial.degree_X_pow_sub_C ] <;> norm_num );
  -- Since the degree of the minimal polynomial is at most 2 and the extension is finite, it must be exactly 1 or 2.
  have h_finrank : Module.finrank (↥K) ↥(IntermediateField.adjoin K {x}) = (minpoly K x).natDegree := by
    convert ( IntermediateField.adjoin.finrank _ );
    refine' ⟨ Polynomial.X ^ 2 - Polynomial.C ( ⟨ x ^ 2, hx ⟩ : K ), _, _ ⟩;
    · rw [ Polynomial.Monic, Polynomial.leadingCoeff_X_pow_sub_C ] ; norm_num;
    · aesop;
  have h_deg_pos : 0 < (minpoly K x).natDegree := by
    by_cases h : minpoly K x = 0;
    · have := minpoly.ne_zero ( show IsIntegral K x from ?_ ) ; aesop;
      exact ⟨ Polynomial.X ^ 2 - Polynomial.C ( ⟨ x ^ 2, hx ⟩ : K ), Polynomial.monic_X_pow_sub_C _ two_ne_zero, by aesop ⟩;
    · exact Polynomial.natDegree_pos_iff_degree_pos.mpr ( Polynomial.degree_pos_of_irreducible ( minpoly.irreducible ( show IsIntegral K x from by exact ( show IsIntegral K x from by exact ( by by_contra h; simp_all +decide [ minpoly.eq_zero ] ) ) ) ) );
  have := Polynomial.natDegree_le_of_degree_le h_min_deg; interval_cases ( minpoly K x |> Polynomial.natDegree ) <;> simp_all +decide ;

set_option maxHeartbeats 0 in
/-
If K has degree 2^n over Q and x^2 is in K, then K(x) has degree a power of 2 over Q.
Proof:
Let L = K(x).
We know [L:K] is 1 or 2.
We know [L:Q] = [L:K] * [K:Q].
So [L:Q] is 1 * 2^n = 2^n or 2 * 2^n = 2^(n+1).
Both are powers of 2.
-/
lemma finrank_adjoin_sq {K : IntermediateField ℚ ℝ} {x : ℝ} (hx : x^2 ∈ K)
    (hK : ∃ n : ℕ, Module.finrank ℚ K = 2 ^ n) :
    ∃ m : ℕ, Module.finrank ℚ (IntermediateField.adjoin ℚ ((K : Set ℝ) ∪ {x})) = 2 ^ m := by
  -- Let L = K(x).
  set L := IntermediateField.adjoin K {x};
  have hL : Module.finrank ℚ ↥(IntermediateField.adjoin K {x}) = Module.finrank K L * Module.finrank ℚ K := by
    bound;
    have hL : Module.finrank ℚ L = Module.finrank ℚ K * Module.finrank K L := by
      have hL : Module.finrank ℚ L = Module.finrank ℚ K * Module.finrank K L := by
        have hL : ∀ (E F G : Type) [Field E] [Field F] [Field G] [Algebra E F] [Algebra F G] [Algebra E G] [IsScalarTower E F G], Module.finrank E G = Module.finrank E F * Module.finrank F G := by
          exact?
        convert hL ℚ K L
      exact hL;
    rw [ hL, mul_comm ];
  -- Since $x^2 \in K$, we know that $[L:K]$ is 1 or 2.
  have hLK : Module.finrank K L = 1 ∨ Module.finrank K L = 2 := by
    convert degree_adjoin_sq K x hx;
  aesop;
  · rw [ show ( IntermediateField.adjoin ℚ ( K ∪ { x } ) : IntermediateField ℚ ℝ ) = K from _ ];
    · use w;
    · refine' le_antisymm _ _;
      · rw [ IntermediateField.adjoin_le_iff ] ; aesop;
        cases h_1 ; aesop;
      · exact fun y hy => IntermediateField.subset_adjoin _ _ <| Set.mem_union_left _ hy;
  · -- Since $L = K(x)$, we have $Module.finrank ℚ (IntermediateField.adjoin ℚ ((K : Set ℝ) ∪ {x})) = Module.finrank ℚ L$.
    have hL_eq : Module.finrank ℚ (IntermediateField.adjoin ℚ ((K : Set ℝ) ∪ {x})) = Module.finrank ℚ L := by
      have hL_eq : IntermediateField.adjoin ℚ ((K : Set ℝ) ∪ {x}) = IntermediateField.restrictScalars ℚ (IntermediateField.adjoin K {x}) := by
        refine' le_antisymm _ _;
        · simp +decide [ IntermediateField.adjoin_le_iff ];
          rintro y ( rfl | hy ) <;> aesop;
          · exact IntermediateField.mem_adjoin_simple_self _ _;
          · exact Subfield.mem_closure.mpr fun z hz => by aesop;
        · simp ( config := { decide := Bool.true } ) [ IntermediateField.restrictScalars, IntermediateField.adjoin ];
          simp ( config := { decide := Bool.true } ) [ Set.insert_subset_iff, Subfield.closure ];
          intro y hy;
          simp_all ( config := { decide := Bool.true } ) [ Set.subset_def, Subfield.mem_iInf ];
          simp_all ( config := { decide := Bool.true } ) [ Subring.mem_iInf ];
      exact hL_eq ▸ rfl;
    exact ⟨ w + 1, by rw [ hL_eq, hL ] ; ring ⟩

/-
If a field K has a quadratic tower, then its degree over Q is a power of 2.
Proof:
We proceed by induction on the length of the tower, say k.
Base case: k=0. Then K = Q, so the degree is 1 = 2^0.
Inductive step: Suppose the tower has length k+1. Let F be the tower.
Then F k has degree 2^n for some n by the inductive hypothesis.
F (k+1) is obtained from F k by adjoining a square root of some x, i.e., F (k+1) = (F k)(x) where x^2 is in F k.
By the lemma `finrank_adjoin_sq`, since F k has degree 2^n and x^2 is in F k, F (k+1) has degree a power of 2.
Thus, by induction, any field in the tower has degree a power of 2.
Since K is the last field in the tower, it has degree a power of 2.
-/
lemma hasQuadTower_finrank (K : IntermediateField ℚ ℝ) (h : HasQuadTower K) :
    ∃ n : ℕ, Module.finrank ℚ K = 2 ^ n := by
  obtain ⟨ k, F, hF₁, hF₂, hF₃ ⟩ := h;
  -- By induction on $i$, we can show that for each $i$, the degree of $F i$ over $\mathbb{Q}$ is a power of 2.
  have h_ind : ∀ i ≤ k, ∃ n : ℕ, Module.finrank ℚ (F i) = 2 ^ n := by
    intro i hi;
    induction' i with i ih;
    · use 0;
      aesop;
    · simp +zetaDelta at *;
      obtain ⟨ x, hx₁, hx₂ ⟩ := hF₃ i ( Nat.lt_of_succ_le hi );
      have := finrank_adjoin_sq hx₁;
      convert this ( ih ( Nat.le_of_succ_le hi ) ) using 1;
      rw [ hx₂, Set.union_comm ];
      rfl;
  cases k <;> aesop

/-
The field of rational numbers (bottom field) has a quadratic tower.
Proof: The tower of length 0 consisting just of the bottom field works.
-/
lemma hasQuadTower_bot : HasQuadTower ⊥ := by
  exact ⟨ 0, fun _ => ⊥, rfl, rfl, by intros; aesop ⟩

/-
If K has a quadratic tower and x is in K, then K(sqrt(x)) has a quadratic tower.
Proof:
Let F be the tower for K.
We can extend this tower by one step: F (k+1) = K(sqrt(x)).
Since x is in K, x^2 is in K? No, (sqrt(x))^2 = x is in K.
So K(sqrt(x)) is obtained by adjoining a square root of an element in K.
Thus, the extended sequence is a quadratic tower.
-/
lemma hasQuadTower_adjoin_sqrt {K : IntermediateField ℚ ℝ} (hK : HasQuadTower K) {x : ℝ} (hx : x ∈ K) :
    HasQuadTower (K ⊔ IntermediateField.adjoin ℚ {Real.sqrt x}) := by
  unfold HasQuadTower at *;
  obtain ⟨ k, F, hF₀, hF₁, hF₂ ⟩ := hK;
  refine' ⟨ k + 1, fun i ↦ if i ≤ k then F i else K ⊔ IntermediateField.adjoin ℚ { Real.sqrt x }, _, _, _ ⟩ <;> simp ( config := { decide := Bool.true } ) [ * ];
  intro i hi; split_ifs <;> simp_all ( config := { decide := Bool.true } ) [ Nat.lt_succ_iff ] ;
  · exact hF₂ i ( Nat.lt_of_succ_le ‹_› );
  · cases le_antisymm ‹_› ‹_› ; use Real.sqrt x ; aesop;
    · by_cases hx_nonneg : 0 ≤ x;
      · rwa [ Real.sq_sqrt hx_nonneg ];
      · norm_num [ Real.sqrt_eq_zero_of_nonpos ( le_of_not_ge hx_nonneg ) ];
    · refine' le_antisymm _ _;
      · simp +decide [ IntermediateField.adjoin_le_iff, Set.insert_subset_iff ];
        exact ⟨ fun y hy => IntermediateField.subset_adjoin _ _ <| Set.mem_insert_of_mem _ hy, IntermediateField.subset_adjoin _ _ <| Set.mem_insert _ _ ⟩;
      · rw [ IntermediateField.adjoin_le_iff ];
        aesop_cat

set_option maxHeartbeats 0 in
/-
If K and L have quadratic towers, then their compositum K ⊔ L has a quadratic tower.
Proof:
Let F be the tower for K (length k).
Let G be the tower for L (length m).
We extend F by adjoining the elements that build L.
Define H_i = F_i for i <= k.
Define H_{k+j} = K ⊔ G_j for j <= m.
Then H_k = K = K ⊔ Q = K ⊔ G_0.
For the step from H_{k+j} to H_{k+j+1}:
G_{j+1} is obtained from G_j by adjoining sqrt(y) where y in G_j.
Then H_{k+j+1} = K ⊔ G_{j+1} = K ⊔ G_j(sqrt(y)) = (K ⊔ G_j)(sqrt(y)) = H_{k+j}(sqrt(y)).
Since y in G_j and G_j subset H_{k+j}, y is in H_{k+j}.
So each step is a quadratic extension (or trivial).
Thus H is a quadratic tower ending at K ⊔ L.
-/
lemma hasQuadTower_sup {K L : IntermediateField ℚ ℝ} (hK : HasQuadTower K) (hL : HasQuadTower L) :
    HasQuadTower (K ⊔ L) := by
  -- Let F be the tower for K (length k).
  obtain ⟨k, F, hF⟩ := hK;
  -- There exists a tower for $L$ that extends $F$.
  obtain ⟨m, G, hG⟩ := hL;
  obtain ⟨hF0, hFk, hF_step⟩ := hF;
  obtain ⟨hG0, hGm, hG_step⟩ := hG;
  use k + m; (
  refine' ⟨ fun i => if i < k then F i else if i = k then K else IntermediateField.adjoin ℚ ( ( F k : Set ℝ ) ∪ ( G ( i - k ) : Set ℝ ) ), _, _, _ ⟩ <;> simp_all +decide;
  · aesop;
  · aesop;
  · intro i hi;
    split_ifs <;> simp_all +decide [ Nat.lt_succ_iff ];
    any_goals omega;
    · grind;
    · rcases hG_step 0 hi with ⟨ x, hx, hx' ⟩ ; use x ; aesop;
      · induction' i with i ih;
        · aesop;
        · exact hF_step i ( Nat.lt_succ_self i ) |> fun ⟨ y, hy, hy' ⟩ => hy'.symm ▸ IntermediateField.subset_adjoin ℚ _ ( Set.mem_insert_of_mem _ ( ih fun j hj => hF_step j ( Nat.lt_succ_of_lt hj ) ) );
      · refine' le_antisymm _ _ <;> simp_all +decide [ IntermediateField.adjoin_le_iff, Set.insert_subset_iff ];
        · exact ⟨ fun y hy => IntermediateField.subset_adjoin ℚ _ <| Set.mem_insert_of_mem _ <| by aesop, IntermediateField.subset_adjoin ℚ _ <| Set.mem_insert _ _ ⟩;
        · exact ⟨ IntermediateField.subset_adjoin _ _ <| Set.mem_union_right _ <| IntermediateField.subset_adjoin _ _ <| Set.mem_insert _ _, fun y hy => IntermediateField.subset_adjoin _ _ <| Set.mem_union_left _ hy ⟩;
    · obtain ⟨ x, hx₁, hx₂ ⟩ := hG_step ( i - k ) ( by omega );
      refine' ⟨ x, _, _ ⟩;
      · exact IntermediateField.subset_adjoin _ _ ( Set.mem_union_right _ hx₁ );
      · rw [ show i + 1 - k = i - k + 1 by omega, hx₂ ];
        refine' le_antisymm _ _ <;> simp_all +decide [ IntermediateField.adjoin_le_iff, Set.insert_subset_iff ];
        · exact ⟨ fun y hy => IntermediateField.subset_adjoin _ _ <| by aesop, IntermediateField.subset_adjoin _ _ <| by aesop, fun y hy => IntermediateField.subset_adjoin _ _ <| by aesop ⟩;
        · refine' ⟨ _, _, _ ⟩;
          · exact IntermediateField.subset_adjoin _ _ ( Set.mem_union_right _ ( IntermediateField.subset_adjoin _ _ ( Set.mem_insert _ _ ) ) );
          · exact fun x hx => IntermediateField.subset_adjoin _ _ ( Set.mem_union_left _ hx );
          · intro y hy; exact IntermediateField.subset_adjoin _ _ ( Set.mem_union_right _ <| IntermediateField.subset_adjoin _ _ <| Set.mem_insert_of_mem _ hy ) ;)

/-
If x is constructible, then there exists a field K containing x such that K has a quadratic tower.
Proof:
Induction on the construction of x.
- If x is rational, take K = Q.
- If x = a + b, take K = K_a ⊔ K_b.
- If x = -a, take K = K_a.
- If x = a * b, take K = K_a ⊔ K_b.
- If x = a⁻¹, take K = K_a.
- If x = sqrt a, take K = K_a(sqrt a).
All these fields have quadratic towers by previous lemmas.
-/
lemma constructible_implies_hasQuadTower (x : ℝ) (hx : Constructible x) :
    ∃ (K : IntermediateField ℚ ℝ), x ∈ K ∧ HasQuadTower K := by
  -- By definition of constructibility, there exists a finite sequence of fields $K_0, K_1, \ldots, K_n$ such that $K_0 = \mathbb{Q}$, $K_n = \mathbb{R}$, and each $K_{i+1}$ is obtained from $K_i$ by adjoining the square root of some element in $K_i$.
  obtain ⟨K, hK⟩ : ∃ K : IntermediateField ℚ ℝ, x ∈ K ∧ K ∈ {K : IntermediateField ℚ ℝ | HasQuadTower K} := by
    -- We proceed by induction on the construction of x.
    induction' hx with x hx ih;
    exact ⟨ ⊥, by aesop, hasQuadTower_bot ⟩;
    · aesop;
      exact ⟨ _, add_mem ( IntermediateField.subset_adjoin ℚ _ <| Set.mem_union_left _ left ) ( IntermediateField.subset_adjoin ℚ _ <| Set.mem_union_right _ left_1 ), hasQuadTower_sup right right_1 ⟩;
    · aesop;
    · aesop;
      use w ⊔ w_1;
      exact ⟨ Subalgebra.mul_mem _ ( IntermediateField.subset_adjoin _ _ ( by aesop ) ) ( IntermediateField.subset_adjoin _ _ ( by aesop ) ), hasQuadTower_sup right right_1 ⟩;
    · aesop;
    · rcases ‹_› with ⟨ K, hK₁, hK₂ ⟩;
      exact ⟨ K ⊔ IntermediateField.adjoin ℚ { Real.sqrt ‹_› }, by aesop_cat, hasQuadTower_adjoin_sqrt hK₂ hK₁ ⟩;
  aesop

/-
If x is constructible, then the degree of Q(x) over Q is a power of 2.
Proof:
By `constructible_implies_hasQuadTower`, there exists a field K containing x with a quadratic tower.
By `hasQuadTower_finrank`, [K:Q] = 2^m for some m.
Since Q(x) is a subfield of K, [K:Q] = [K:Q(x)] * [Q(x):Q].
Thus [Q(x):Q] divides 2^m.
Therefore [Q(x):Q] is a power of 2.
-/
lemma degree_of_constructible (x : ℝ) (hx : Constructible x) :
    ∃ n : ℕ, Module.finrank ℚ (IntermediateField.adjoin ℚ {x}) = 2 ^ n := by
  have h_deg : ∃ (K : IntermediateField ℚ ℝ), x ∈ K ∧ HasQuadTower K := by
    exact?;
  have := h_deg.choose_spec.2;
  have := hasQuadTower_finrank _ this;
  have h_div : Module.finrank ℚ (↥(IntermediateField.adjoin ℚ {x})) ∣ Module.finrank ℚ (↥h_deg.choose) := by
    have h_div : IntermediateField.adjoin ℚ {x} ≤ h_deg.choose := by
      exact IntermediateField.adjoin_le_iff.mpr ( Set.singleton_subset_iff.mpr h_deg.choose_spec.1 );
    bound;
    have := h_div;
    exact?;
  rw [ this.choose_spec ] at h_div; rw [ Nat.dvd_prime_pow ] at h_div <;> norm_num at * ; tauto;

/-
The degree of the field extension Q(x) over Q, where x^3 = 2, is 3.
Proof:
The minimal polynomial of x over Q is X^3 - 2.
This polynomial is irreducible over Q because it has degree 3 and no rational roots (if p/q is a root, then p^3 = 2q^3, which is impossible for coprime p, q).
Since the minimal polynomial has degree 3, the degree of the extension is 3.
-/
lemma minpoly_degree_of_cube_root_two {x : ℝ} (h : x ^ 3 = 2) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ {x}) = 3 := by
  -- The minimal polynomial of $x$ over $\mathbb{Q}$ is $x^3 - 2$, which is irreducible over $\mathbb{Q}$.
  have h_min_poly : minpoly ℚ x = Polynomial.X^3 - 2 := by
    refine' Eq.symm ( minpoly.eq_of_irreducible_of_monic _ _ _ );
    · -- We'll use that $x^3 - 2$ is irreducible over $\mathbb{Q}$ because it has no rational roots and its degree is 3.
      have h_irred : Irreducible (Polynomial.X^3 - 2 : Polynomial ℚ) := by
        have h_no_rational_roots : ¬∃ (q : ℚ), q^3 = 2 := by
          aesop;
          -- If $x_1^3 = 2$, then $x_1$ must be of the form $p/q$ where $p^3 = 2q^3$.
          obtain ⟨p, q, hpq, h_coprime⟩ : ∃ p q : ℤ, Int.gcd p q = 1 ∧ x_1 = p / q ∧ p^3 = 2 * q^3 := by
            exact ⟨ x_1.num, x_1.den, x_1.reduced, x_1.num_div_den.symm, by simp ( config := { decide := Bool.true } ) [ ← @Int.cast_inj ℚ, ← a, ← mul_pow, Rat.num_div_den ] ⟩;
          -- Since $p^3 = 2q^3$, we see that $p$ must be a multiple of $q$. Let $p = kq$ for some integer $k$.
          obtain ⟨k, hk⟩ : ∃ k : ℤ, p = k * q := by
            exact exists_eq_mul_left_of_dvd <| Int.pow_dvd_pow_iff ( by decide ) |>.1 <| h_coprime.2.symm ▸ dvd_mul_left _ _;
          by_cases hq : q = 0 <;> simp_all +decide [ mul_pow ];
          cases le_or_lt 2 k <;> nlinarith [ sq_nonneg ( k^2 ) ]
        -- Since $x^3 - 2$ has no rational roots and its degree is 3, it must be irreducible over $\mathbb{Q}$.
        have h_irred : ∀ p q : Polynomial ℚ, p.degree > 0 → q.degree > 0 → p * q = Polynomial.X^3 - 2 → False := by
          intros p q hp hq h_factor
          have h_deg : p.degree + q.degree = 3 := by
            erw [ ← Polynomial.degree_mul, h_factor, Polynomial.degree_X_pow_sub_C ] <;> norm_num;
          -- Since $p$ and $q$ are non-constant polynomials with degrees adding up to 3, one of them must have degree 1.
          obtain (h_deg_p | h_deg_q) : p.degree = 1 ∨ q.degree = 1 := by
            erw [ Polynomial.degree_eq_natDegree ( Polynomial.ne_zero_of_degree_gt hp ), Polynomial.degree_eq_natDegree ( Polynomial.ne_zero_of_degree_gt hq ) ] at * ; norm_cast at * ; omega;
          · -- If $p$ has degree 1, then $p$ is a linear polynomial with a rational root.
            obtain ⟨r, hr⟩ : ∃ r : ℚ, p.eval r = 0 := by
              exact Polynomial.exists_root_of_degree_eq_one h_deg_p;
            replace h_factor := congr_arg ( Polynomial.eval r ) h_factor; norm_num [ hr ] at h_factor; exact h_no_rational_roots ⟨ r, by linarith ⟩ ;
          · -- If $q$ has degree 1, then it must have a rational root.
            obtain ⟨r, hr⟩ : ∃ r : ℚ, q.eval r = 0 := by
              exact Polynomial.exists_root_of_degree_eq_one h_deg_q;
            replace h_factor := congr_arg ( Polynomial.eval r ) h_factor; norm_num [ hr ] at h_factor; exact h_no_rational_roots ⟨ r, by linarith ⟩ ;
        constructor <;> contrapose! h_irred <;> aesop;
        · exact absurd ( Polynomial.degree_eq_zero_of_isUnit h_irred ) ( by erw [ Polynomial.degree_X_pow_sub_C ] <;> norm_num );
        · exact ⟨ w, not_le.mp fun h => left_1 <| Polynomial.isUnit_iff_degree_eq_zero.mpr <| le_antisymm h <| le_of_not_gt fun h' => by apply_fun Polynomial.eval 0 at left; aesop, w_1, not_le.mp fun h => right <| Polynomial.isUnit_iff_degree_eq_zero.mpr <| le_antisymm h <| le_of_not_gt fun h' => by apply_fun Polynomial.eval 0 at left; aesop, rfl ⟩;
      exact h_irred;
    · aesop;
      erw [ Polynomial.aeval_C ] ; norm_num;
    · erw [ Polynomial.Monic, Polynomial.leadingCoeff_X_pow_sub_C ] ; norm_num;
  have := IntermediateField.adjoin.finrank ( show IsIntegral ℚ x from by exact ( show IsIntegral ℚ x from by exact ( by exact ( by exact ( by exact ( by exact ( by exact ⟨ Polynomial.X ^ 3 - 2, Polynomial.monic_X_pow_sub_C _ ( by norm_num ), by aesop ⟩ ) ) ) ) ) ) ) ; aesop;
  erw [ Polynomial.natDegree_X_pow_sub_C ]

end AristotleLemmas

theorem doubling_the_cube_impossible :
    ¬ ∃ x : ℝ, x ^ 3 = (2 : ℝ) ∧ Constructible x := by
  by_contra h
  obtain ⟨x, hx_cube, hx_field⟩ := h;
  have := minpoly_degree_of_cube_root_two hx_cube;
  exact absurd ( degree_of_constructible x hx_field ) ( by rintro ⟨ n, hn ⟩ ; exact absurd ( this.symm.trans hn ) ( by intro H; linarith [ Nat.pow_le_pow_right ( show 1 ≤ 2 by decide ) ( show n ≥ 2 by contrapose! H; interval_cases n <;> norm_num ) ] ) )

/- **Impossibility of trisecting the angle** (in the classical sense): there is
no straightedge-and-compass construction which, for *every* constructible angle
`θ`, produces a constructible angle equal to `θ / 3`. -/
noncomputable section AristotleLemmas

/-
The number $\cos(\pi/9)$ is a root of the polynomial $8x^3 - 6x - 1$.
-/
lemma cos_pi_div_9_root : 8 * (Real.cos (Real.pi / 9))^3 - 6 * (Real.cos (Real.pi / 9)) - 1 = 0 := by
  have := Real.cos_three_mul ( Real.pi / 9 ) ; rw [ ( by ring : 3 * ( Real.pi / 9 ) = Real.pi / 3 ) ] at this ; rw [ Real.cos_pi_div_three ] at this ; linarith;

/-
The polynomial $X^3 - 3X - 1$ is irreducible over the rationals.
-/
open Polynomial in
lemma trisection_poly_irreducible : Irreducible (X^3 - 3 * X - 1 : ℚ[X]) := by
  -- To prove the irreducibility, we can use the fact that the polynomial $X^3 - 3X - 1$ has no rational roots and is of degree 3.
  have h_no_rational_roots : ¬∃ r : ℚ, r ^ 3 - 3 * r - 1 = 0 := by
    aesop;
    -- If $x$ were rational, then $x = \frac{p}{q}$ with $\gcd(p, q) = 1$ and $q \neq 0$.
    obtain ⟨p, q, h_gcd, h_eq⟩ : ∃ p q : ℤ, Int.gcd p q = 1 ∧ q ≠ 0 ∧ x = p / q := by
      exact ⟨ x.num, x.den, x.reduced, Nat.cast_ne_zero.mpr x.pos.ne', x.num_div_den.symm ⟩;
    -- Substitute $x = \frac{p}{q}$ into the polynomial equation to get $p^3 - 3pq^2 - q^3 = 0$.
    have h_poly_eq : p ^ 3 - 3 * p * q ^ 2 - q ^ 3 = 0 := by
      bound;
      field_simp at a;
      norm_cast at a; linarith;
    apply_fun Even at *; simp_all +decide [ parity_simps ];
    by_cases hq : Even q <;> simp_all +decide [ parity_simps ];
    exact absurd ( h_gcd ) ( by simpa [ h_poly_eq, hq, even_iff_two_dvd ] using Int.dvd_gcd ( even_iff_two_dvd.mp h_poly_eq ) ( even_iff_two_dvd.mp hq ) );
  -- Since $f(x)$ has no rational roots and is of degree 3, it must be irreducible over the rationals.
  have h_irr : ∀ p q : Polynomial ℚ, p.degree > 0 → q.degree > 0 → (Polynomial.X ^ 3 - 3 * Polynomial.X - 1) = p * q → False := by
    -- Since $f(x)$ is of degree 3, if it factors into polynomials of lower degrees, one of them must be linear.
    intros p q hp hq h_factor
    have h_deg : p.degree = 1 ∨ q.degree = 1 := by
      have h_deg : p.degree + q.degree = 3 := by
        rw [ ← Polynomial.degree_mul, ← h_factor, Polynomial.degree_sub_eq_left_of_degree_lt ] <;> erw [ Polynomial.degree_sub_eq_left_of_degree_lt ] <;> norm_num;
        · erw [ Polynomial.degree_C ] <;> norm_num;
        · erw [ Polynomial.degree_C ] <;> norm_num;
      erw [ Polynomial.degree_eq_natDegree ( Polynomial.ne_zero_of_degree_gt hp ), Polynomial.degree_eq_natDegree ( Polynomial.ne_zero_of_degree_gt hq ) ] at * ; norm_cast at * ; omega;
    obtain h | h := h_deg <;> obtain ⟨ r, hr ⟩ := Polynomial.exists_root_of_degree_eq_one h <;> replace h_factor := congr_arg ( Polynomial.eval r ) h_factor <;> aesop;
  constructor <;> contrapose! h_irr <;> aesop;
  · exact absurd ( Polynomial.degree_eq_zero_of_isUnit h_irr ) ( by repeat ( first | erw [ Polynomial.degree_add_eq_left_of_degree_lt ] | erw [ Polynomial.degree_C ] ) <;> norm_num );
  · exact ⟨ w, not_le.mp fun h => left_1 <| Polynomial.isUnit_iff_degree_eq_zero.mpr <| le_antisymm h <| le_of_not_gt fun h' => by apply_fun Polynomial.eval 0 at left; aesop, w_1, not_le.mp fun h => right <| Polynomial.isUnit_iff_degree_eq_zero.mpr <| le_antisymm h <| le_of_not_gt fun h' => by apply_fun Polynomial.eval 0 at left; aesop, rfl ⟩

/-
The number $2\cos(\pi/9)$ is a root of the polynomial $X^3 - 3X - 1$.
-/
open Polynomial in
lemma trisection_poly_root : aeval (2 * Real.cos (Real.pi / 9)) (X^3 - 3 * X - 1 : ℚ[X]) = 0 := by
  -- Substitute $x = 2 \cos(\pi/9)$ into the polynomial $X^3 - 3X - 1$ and show that it evaluates to zero.
  have h_subst : (2 * Real.cos (Real.pi / 9))^3 - 3 * (2 * Real.cos (Real.pi / 9)) - 1 = 0 := by
    have := Real.cos_three_mul ( Real.pi / 9 ) ; rw [ ( by ring : 3 * ( Real.pi / 9 ) = Real.pi / 3 ) ] at this ; rw [ Real.cos_pi_div_three ] at this ; nlinarith;
  convert h_subst using 1;
  norm_num [ Polynomial.aeval_def ]

/-
If $x^2 \in K$, then the degree of the extension $K(x)/K$ is either 1 or 2.
-/
open IntermediateField Polynomial

lemma degree_adjoin_sq' (K : IntermediateField ℚ ℝ) (x : ℝ) (hx : x^2 ∈ K) :
    Module.finrank K (adjoin K {x}) = 1 ∨ Module.finrank K (adjoin K {x}) = 2 := by
      -- Let $L = K(x)$.
      set L : IntermediateField K ℝ := IntermediateField.adjoin K {x};
      have h_deg : (minpoly K x).degree ≤ 2 := by
        have h_deg : minpoly K x ∣ Polynomial.X^2 - Polynomial.C (⟨x^2, hx⟩ : K) := by
          exact minpoly.dvd K x ( by aesop );
        exact le_trans ( Polynomial.degree_le_of_dvd h_deg <| by exact ne_of_apply_ne Polynomial.degree <| by erw [ Polynomial.degree_X_pow_sub_C ] <;> norm_num ) <| by erw [ Polynomial.degree_X_pow_sub_C ] <;> norm_num;
      have h_deg : Module.finrank K L = (minpoly K x).natDegree := by
        convert ( IntermediateField.adjoin.finrank <| show IsIntegral K x from ?_ );
        refine' ⟨ Polynomial.X ^ 2 - Polynomial.C ( ⟨ x ^ 2, hx ⟩ : K ), _, _ ⟩ <;> norm_num;
        erw [ Polynomial.Monic, Polynomial.leadingCoeff_X_pow_sub_C ] ; norm_num;
      have h_deg_pos : 0 < (minpoly K x).natDegree := by
        apply minpoly.natDegree_pos;
        refine' ⟨ Polynomial.X ^ 2 - Polynomial.C ( ⟨ x ^ 2, hx ⟩ : K ), _, _ ⟩ <;> aesop;
        erw [ Polynomial.Monic, Polynomial.leadingCoeff_X_pow_sub_C ] ; norm_num;
      have := Polynomial.natDegree_le_of_degree_le ‹_›; interval_cases _ : Polynomial.natDegree ( minpoly K x ) <;> aesop;

/-
Define `DyadicExtension` as a field obtained by a sequence of square root adjunctions.
Prove that any dyadic extension has degree a power of 2.
-/
open IntermediateField Polynomial

inductive DyadicExtension : IntermediateField ℚ ℝ → Prop
  | base : DyadicExtension ⊥
  | step {K : IntermediateField ℚ ℝ} {x : ℝ} (hK : DyadicExtension K) (hx : x^2 ∈ K) :
      DyadicExtension (K ⊔ adjoin ℚ {x})

lemma dyadic_degree_pow2 (K : IntermediateField ℚ ℝ) (h : DyadicExtension K) :
    ∃ n : ℕ, Module.finrank ℚ K = 2 ^ n := by
      induction h;
      · -- The finrank of the bottom field (which is ℚ) over itself is 1.
        use 0
        simp;
      · rename_i K x hK hx ih; obtain ⟨ n, hn ⟩ := ih; have := degree_adjoin_sq K x hx; aesop;
        · -- Since $x \in \bot$, we have $K \supseteq \mathbb{Q}(x) = \mathbb{Q}$, so $K \supseteq K$.
          have h_sup : K ⊔ IntermediateField.adjoin ℚ {x} = K := by
            rw [ eq_comm ] ; aesop;
            cases h ; aesop;
          aesop;
          exact ⟨ n, by rw [ show K ⊔ IntermediateField.adjoin ℚ { x } = K from sup_eq_left.mpr <| by aesop ] ; exact hn ⟩;
        · -- By the tower law, we have $[K(x) : \mathbb{Q}] = [K(x) : K] \cdot [K : \mathbb{Q}]$.
          have h_tower : Module.finrank ℚ (↥(IntermediateField.adjoin K {x})) = Module.finrank K (↥(IntermediateField.adjoin K {x})) * Module.finrank ℚ K := by
            have h_tower : ∀ (L M N : Type) [Field L] [Field M] [Field N] [Algebra L M] [Algebra M N] [Algebra L N] [IsScalarTower L M N], Module.finrank L N = Module.finrank M N * Module.finrank L M := by
              intros L M N _ _ _ _ _ _ _; exact (by
              rw [ mul_comm, Module.finrank_mul_finrank ]);
            convert h_tower ℚ K ( IntermediateField.adjoin K { x } ) using 1;
          rw [ ← IntermediateField.restrictScalars_adjoin_eq_sup ];
          exact ⟨ n + 1, by erw [ h_tower, h_1, hn ] ; ring ⟩

/-
If $K$ and $L$ are dyadic extensions, there exists a dyadic extension $M$ containing both $K$ and $L$.
-/
open IntermediateField

lemma dyadic_sup (K L : IntermediateField ℚ ℝ) (hK : DyadicExtension K) (hL : DyadicExtension L) :
    ∃ M : IntermediateField ℚ ℝ, DyadicExtension M ∧ K ≤ M ∧ L ≤ M := by
      induction' hL with L' L' hL' x hx hM' ; aesop;
      obtain ⟨ M, hM₁, hM₂, hM₃ ⟩ := hx; use M ⊔ IntermediateField.adjoin ℚ { L' } ; aesop;
      · exact DyadicExtension.step hM₁ ( by simpa using hM₃ x );
      · exact le_trans hM₂ le_sup_left;
      · exact le_sup_of_le_left hM₃

/-
Every constructible number is contained in some dyadic extension field.
-/
open IntermediateField

lemma constructible_in_dyadic (x : ℝ) (hx : Constructible x) :
    ∃ K : IntermediateField ℚ ℝ, DyadicExtension K ∧ x ∈ K := by
      -- Apply the induction hypothesis to each constructor of `Constructible`.
      have h_construction : ∀ {x : ℝ}, Constructible x → ∃ K : IntermediateField ℚ ℝ, DyadicExtension K ∧ x ∈ K := by
        intro x hx
        induction' hx with x hx ihx;
        exact ⟨ ⊥, DyadicExtension.base, by aesop ⟩;
        · case _ hx₁ hx₂ => obtain ⟨ K₁, hK₁, hK₁' ⟩ := hx₁; obtain ⟨ K₂, hK₂, hK₂' ⟩ := hx₂; obtain ⟨ M, hM₁, hM₂, hM₃ ⟩ := dyadic_sup K₁ K₂ hK₁ hK₂; exact ⟨ M, hM₁, add_mem ( hM₂ hK₁' ) ( hM₃ hK₂' ) ⟩ ;
        · aesop;
        · field_simp;
          rename_i hx hy ihx ihy; rcases ihx with ⟨ K, hK, hxK ⟩ ; rcases ihy with ⟨ L, hL, hyL ⟩ ; rcases dyadic_sup K L hK hL with ⟨ M, hM, hKM, hLM ⟩ ; exact ⟨ M, hM, by exact M.mul_mem ( hKM hxK ) ( hLM hyL ) ⟩ ;
        · aesop;
        · obtain ⟨ K, hK₁, hK₂ ⟩ := ‹_›;
          bound;
          refine' ⟨ K ⊔ IntermediateField.adjoin ℚ { Real.sqrt x_2 }, _, _ ⟩;
          · exact DyadicExtension.step hK₁ ( by aesop );
          · exact IntermediateField.subset_adjoin ℚ _ ( Set.mem_singleton _ ) |> fun h => SetLike.le_def.mp ( le_sup_right ) h;
      exact h_construction hx

end AristotleLemmas

theorem angle_trisection_impossible :
    ¬ (∀ θ : ℝ, ConstructibleAngle θ → ConstructibleAngle (θ / 3)) := by
  -- Assume for contradiction that trisection is always possible.
  by_contra h_contra

  -- Then for $\theta = \pi/3$, $\theta/3 = \pi/9$ is constructible.
  have h_pi_9 : Constructible (2 * Real.cos (Real.pi / 9)) := by
    -- Since $\pi/3$ is constructible, by the assumption, $\pi/9$ is also constructible.
    have h_pi_9 : ConstructibleAngle (Real.pi / 9) := by
      -- Since $\cos(\pi/3) = 1/2$, which is rational, hence constructible.
      have h_pi_3 : ConstructibleAngle (Real.pi / 3) := by
        -- Since $\cos(\pi/3) = 1/2$, which is rational, hence constructible.
        have h_cos_pi_3 : Constructible (Real.cos (Real.pi / 3)) := by
          convert Constructible.rat ( 1 / 2 ) using 1 ; norm_num;
        exact h_cos_pi_3;
      convert h_contra _ h_pi_3 using 1 ; ring;
    -- By definition of ConstructibleAngle, we know that Real.cos (Real.pi / 9) is constructible.
    have h_cos_pi_9 : Constructible (Real.cos (Real.pi / 9)) := by
      exact h_pi_9;
    convert Constructible.mul ( Constructible.rat 2 ) h_cos_pi_9 using 1;
  -- Let $x = 2\cos(\pi/9)$. Since $\cos(\pi/9)$ is constructible, $x$ is constructible.
  set x := 2 * Real.cos (Real.pi / 9)
  have hx : Constructible x := by
    exact h_pi_9;
  -- By `constructible_in_dyadic`, $x$ lies in a dyadic extension $K$.
  obtain ⟨K, hK⟩ : ∃ K : IntermediateField ℚ ℝ, DyadicExtension K ∧ x ∈ K := by
    apply_rules [ constructible_in_dyadic ];
  -- By `dyadic_degree_pow2`, $[K:\mathbb{Q}] = 2^n$ for some $n$.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Module.finrank ℚ K = 2 ^ n := by
    exact dyadic_degree_pow2 K hK.1;
  -- The minimal polynomial of $x$ over $\mathbb{Q}$ is $P(X) = X^3 - 3X - 1$.
  have h_min_poly : minpoly ℚ x = Polynomial.X^3 - 3 * Polynomial.X - 1 := by
    refine' Eq.symm ( minpoly.eq_of_irreducible_of_monic _ _ _ );
    · convert trisection_poly_irreducible using 1;
    · norm_num +zetaDelta at *;
      erw [ Polynomial.aeval_C ] ; norm_num ; have := Real.cos_three_mul ( Real.pi / 9 ) ; rw [ ( by ring : 3 * ( Real.pi / 9 ) = Real.pi / 3 ) ] at this ; norm_num at this ; nlinarith [ Real.cos_sq' ( Real.pi / 9 ) ];
    · erw [ Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_sub_C, Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> norm_num;
      norm_num [ Polynomial.coeff_one, Polynomial.coeff_X ];
  -- Therefore, $[\mathbb{Q}(x):\mathbb{Q}] = 3$.
  have h_deg : Module.finrank ℚ (IntermediateField.adjoin ℚ {x}) = 3 := by
    have := IntermediateField.adjoin.finrank ( show IsIntegral ℚ x from ?_ );
    · erw [ this, h_min_poly, Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> erw [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> norm_num;
    · refine' ⟨ Polynomial.X ^ 3 - 3 * Polynomial.X - 1, _, _ ⟩ <;> aesop;
      · erw [ Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_sub_C, Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> norm_num;
        norm_num [ Polynomial.coeff_one, Polynomial.coeff_X ];
      · have := Real.cos_three_mul ( Real.pi / 9 ) ; rw [ ( by ring : 3 * ( Real.pi / 9 ) = Real.pi / 3 ) ] at this ; rw [ Real.cos_pi_div_three ] at this ; linarith;
  -- Since $x \in K$, $\mathbb{Q}(x) \subseteq K$.
  have h_sub : IntermediateField.adjoin ℚ {x} ≤ K := by
    aesop;
  -- Therefore, $[\mathbb{Q}(x):\mathbb{Q}]$ divides $[K:\mathbb{Q}]$.
  have h_div : Module.finrank ℚ (IntermediateField.adjoin ℚ {x}) ∣ Module.finrank ℚ K := by
    have h_div : ∀ (L M : IntermediateField ℚ ℝ), L ≤ M → Module.finrank ℚ L ∣ Module.finrank ℚ M := by
      exact?;
    exact h_div _ _ h_sub;
  simp_all +decide [ Nat.Prime.dvd_iff_one_le_factorization ]

/-- Freek Wiedijk’s theorem 8: “The Impossibility of Trisecting the Angle and
Doubling the Cube”, packaged as a single statement. -/
theorem freek_08 :
    (¬ (∀ θ : ℝ, ConstructibleAngle θ → ConstructibleAngle (θ / 3))) ∧
    (¬ ∃ x : ℝ, x ^ 3 = (2 : ℝ) ∧ Constructible x) := by
  exact ⟨ fun h => angle_trisection_impossible h, fun ⟨ x, hx₁, hx₂ ⟩ => doubling_the_cube_impossible ⟨ x, hx₁, hx₂ ⟩ ⟩
