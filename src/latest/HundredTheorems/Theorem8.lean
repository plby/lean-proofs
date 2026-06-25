/- leanprover/lean4:v4.30.0  mathlib v4.30.0 -/
/-
This is a Lean formalization of
8: The Impossibility of Trisecting the Angle and Doubling the Cube
interpreted as a statement about constructible real numbers in
`freek_08` AND also in terms of ruler-compass constructions in
`freek_08_plane`.

This was proven formally by Aristotle (from Harmonic), given an
informal proof by ChatGPT-5.2 Pro (from OpenAI).
-/
import Mathlib
set_option linter.style.setOption false
set_option linter.dupNamespace false
set_option linter.style.cases false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.flexible false
namespace Theorem8
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
If x ^ 2 is in K, then the degree of K(x) over K is 1 or 2.
Proof: The minimal polynomial of x over K divides X ^ 2 - x ^ 2.
So the degree of the minimal polynomial is at most 2.
The degree of the extension is the degree of the minimal polynomial.
So it is at most 2.
Since it's a field extension, the degree is at least 1.
So it is 1 or 2.
-/
lemma degree_adjoin_sq (K : IntermediateField ℚ ℝ) (x : ℝ) (hx : x ^ 2 ∈ K) :
    Module.finrank K (IntermediateField.adjoin K {x}) = 1 ∨ Module.finrank K (IntermediateField.adjoin K {x}) = 2 := by
  have hxint : IsIntegral K x := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (⟨x ^ 2, hx⟩ : K), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub_C _ two_ne_zero
    · simp
  haveI : FiniteDimensional K (IntermediateField.adjoin K {x}) :=
    IntermediateField.adjoin.finiteDimensional hxint
  haveI : Module.Free K (IntermediateField.adjoin K {x}) :=
    Module.Free.of_divisionRing K (IntermediateField.adjoin K {x})
  -- Since $x ^ 2 \in K$, the minimal polynomial of $x$ over $K$ divides $X ^ 2 - x ^ 2$, which has degree 2.
  have h_min_deg : Polynomial.degree (minpoly K x) ≤ 2 := by
    have h_min_div : minpoly K x ∣ (Polynomial.X ^ 2 - Polynomial.C (⟨x ^ 2, hx⟩ : K)) := by
      refine minpoly.dvd K x ?_
      bound
    exact le_trans ( Polynomial.degree_le_of_dvd h_min_div ( Polynomial.X_pow_sub_C_ne_zero ( by norm_num ) _ ) ) ( by erw [ Polynomial.degree_X_pow_sub_C ] <;> norm_num )
  -- Since the degree of the minimal polynomial is at most 2 and the extension is finite, it must be exactly 1 or 2.
  have h_finrank : Module.finrank (↥K) ↥(IntermediateField.adjoin K {x}) = (minpoly K x).natDegree := by
    convert ( IntermediateField.adjoin.finrank _ )
    refine ⟨ Polynomial.X ^ 2 - Polynomial.C ( ⟨ x ^ 2, hx ⟩ : K ), ?_, ?_ ⟩
    · rw [ Polynomial.Monic, Polynomial.leadingCoeff_X_pow_sub_C ] ; norm_num
    · aesop
  have h_deg_pos : 0 < (minpoly K x).natDegree := by
    by_cases h : minpoly K x = 0
    · have := minpoly.ne_zero ( show IsIntegral K x from ?_ )
      · aesop
      · exact ⟨ Polynomial.X ^ 2 - Polynomial.C ( ⟨ x ^ 2, hx ⟩ : K ), Polynomial.monic_X_pow_sub_C _ two_ne_zero, by aesop ⟩
    · exact Polynomial.natDegree_pos_iff_degree_pos.mpr ( Polynomial.degree_pos_of_irreducible ( minpoly.irreducible ( show IsIntegral K x from by exact ( show IsIntegral K x from by exact ( by by_contra h; simp_all +decide [] ) ) ) ) )
  have := Polynomial.natDegree_le_of_degree_le h_min_deg; interval_cases ( minpoly K x |> Polynomial.natDegree ) <;> simp_all +decide
set_option maxHeartbeats 8000000 in
-- The adjoining-square-root degree argument needs an expanded heartbeat budget.
/-
If K has degree 2 ^ n over Q and x ^ 2 is in K, then K(x) has degree a power of 2 over Q.
Proof:
Let L = K(x).
We know [L:K] is 1 or 2.
We know [L:Q] = [L:K] * [K:Q].
So [L:Q] is 1 * 2 ^ n = 2 ^ n or 2 * 2 ^ n = 2 ^ (n+1).
Both are powers of 2.
-/
lemma finrank_adjoin_sq {K : IntermediateField ℚ ℝ} {x : ℝ} (hx : x ^ 2 ∈ K)
    (hK : ∃ n : ℕ, Module.finrank ℚ K = 2 ^ n) :
    ∃ m : ℕ, Module.finrank ℚ (IntermediateField.adjoin ℚ ((K : Set ℝ) ∪ {x})) = 2 ^ m := by
  have hxint : IsIntegral K x := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (⟨x ^ 2, hx⟩ : K), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub_C _ two_ne_zero
    · simp
  haveI : FiniteDimensional K (IntermediateField.adjoin K {x}) :=
    IntermediateField.adjoin.finiteDimensional hxint
  haveI : Module.Free K (IntermediateField.adjoin K {x}) :=
    Module.Free.of_divisionRing K (IntermediateField.adjoin K {x})
  -- Let L = K(x).
  set L := IntermediateField.adjoin K {x}
  have hL : Module.finrank ℚ ↥(IntermediateField.adjoin K {x}) = Module.finrank K L * Module.finrank ℚ K := by
    rw [← Module.finrank_mul_finrank ℚ K L, mul_comm]
  -- Since $x ^ 2 \in K$, we know that $[L:K]$ is 1 or 2.
  have hLK : Module.finrank K L = 1 ∨ Module.finrank K L = 2 := by
    convert degree_adjoin_sq K x hx
  have hL_eq :
      IntermediateField.adjoin ℚ ((K : Set ℝ) ∪ {x}) =
        IntermediateField.restrictScalars ℚ (IntermediateField.adjoin K {x}) := by
    exact (IntermediateField.restrictScalars_adjoin ℚ K ({x} : Set ℝ)).symm
  have hfin :
      Module.finrank ℚ (IntermediateField.adjoin ℚ ((K : Set ℝ) ∪ {x})) =
        Module.finrank K L * Module.finrank ℚ K := by
    rw [hL_eq]
    exact hL
  rcases hK with ⟨n, hn⟩
  rcases hLK with hLK | hLK
  · exact ⟨n, by rw [hfin, hLK, hn, one_mul]⟩
  · exact ⟨n + 1, by rw [hfin, hLK, hn, pow_succ]; ring⟩
/-
If a field K has a quadratic tower, then its degree over Q is a power of 2.
Proof:
We proceed by induction on the length of the tower, say k.
Base case: k=0. Then K = Q, so the degree is 1 = 2 ^ 0.
Inductive step: Suppose the tower has length k+1. Let F be the tower.
Then F k has degree 2 ^ n for some n by the inductive hypothesis.
F (k+1) is obtained from F k by adjoining a square root of some x, i.e., F (k+1) = (F k)(x) where x ^ 2 is in F k.
By the lemma `finrank_adjoin_sq`, since F k has degree 2 ^ n and x ^ 2 is in F k, F (k+1) has degree a power of 2.
Thus, by induction, any field in the tower has degree a power of 2.
Since K is the last field in the tower, it has degree a power of 2.
-/
lemma hasQuadTower_finrank (K : IntermediateField ℚ ℝ) (h : HasQuadTower K) :
    ∃ n : ℕ, Module.finrank ℚ K = 2 ^ n := by
  obtain ⟨ k, F, hF₁, hF₂, hF₃ ⟩ := h
  -- By induction on $i$, we can show that for each $i$, the degree of $F i$ over $\mathbb{Q}$ is a power of 2.
  have h_ind : ∀ i ≤ k, ∃ n : ℕ, Module.finrank ℚ (F i) = 2 ^ n := by
    intro i hi
    induction i with
    | zero =>
      use 0
      aesop
    | succ i ih =>
      simp +zetaDelta at *
      obtain ⟨ x, hx₁, hx₂ ⟩ := hF₃ i ( Nat.lt_of_succ_le hi )
      have := finrank_adjoin_sq hx₁
      convert this ( ih ( Nat.le_of_succ_le hi ) ) using 1
      rw [ hx₂, Set.union_comm ]
      rfl
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
Since x is in K, x ^ 2 is in K? No, (sqrt(x)) ^ 2 = x is in K.
So K(sqrt(x)) is obtained by adjoining a square root of an element in K.
Thus, the extended sequence is a quadratic tower.
-/
lemma hasQuadTower_adjoin_sqrt {K : IntermediateField ℚ ℝ} (hK : HasQuadTower K) {x : ℝ} (hx : x ∈ K) :
    HasQuadTower (K ⊔ IntermediateField.adjoin ℚ {Real.sqrt x}) := by
  unfold HasQuadTower at *
  rcases hK with ⟨k, F, hF₀, hFk, hFstep⟩
  refine ⟨k + 1, fun i => if i ≤ k then F i else K ⊔ IntermediateField.adjoin ℚ {Real.sqrt x}, ?_, ?_, ?_⟩
  · simp [hF₀]
  · simp
  · intro i hi
    by_cases hik : i < k
    · rcases hFstep i hik with ⟨y, hy, hstep⟩
      refine ⟨y, ?_, ?_⟩
      · simpa [hik.le] using hy
      · have hi_succ : i + 1 ≤ k := Nat.succ_le_of_lt hik
        simp [hik.le, hi_succ, hstep]
    · have hi_eq : i = k := Nat.eq_of_lt_succ_of_not_lt hi hik
      refine ⟨Real.sqrt x, ?_, ?_⟩
      · have hsx : Real.sqrt x ^ 2 ∈ K := by
          by_cases hx_nonneg : 0 ≤ x
          · simpa [Real.sq_sqrt hx_nonneg] using hx
          · have hsqrt : Real.sqrt x = 0 :=
              Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hx_nonneg)
            simp [hsqrt]
        simpa [hi_eq, hFk] using hsx
      · simp [hi_eq, hFk]
        calc
          K ⊔ IntermediateField.adjoin ℚ {Real.sqrt x}
              = IntermediateField.adjoin ℚ ((K : Set ℝ) ∪ {Real.sqrt x}) := by
                rw [IntermediateField.adjoin_union, IntermediateField.adjoin_self]
          _ = IntermediateField.adjoin ℚ (insert (Real.sqrt x) (K : Set ℝ)) := by
                congr 1
                ext y
                simp [or_comm]
set_option maxHeartbeats 8000000 in
-- Combining two quadratic towers produces a large generated field-inclusion proof.
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
  obtain ⟨k, F, hF⟩ := hK
  -- There exists a tower for $L$ that extends $F$.
  obtain ⟨m, G, hG⟩ := hL
  obtain ⟨hF0, hFk, hF_step⟩ := hF
  obtain ⟨hG0, hGm, hG_step⟩ := hG
  use k + m; (
  refine ⟨ fun i => if i < k then F i else if i = k then K else IntermediateField.adjoin ℚ ( ( F k : Set ℝ ) ∪ ( G ( i - k ) : Set ℝ ) ), ?_, ?_, ?_ ⟩ <;> simp_all +decide
  · aesop
  · aesop
  · intro i hi
    split_ifs <;> simp_all +decide [ Nat.lt_succ_iff ]
    any_goals omega
    · grind
    · rcases hG_step 0 hi with ⟨ x, hx, hx' ⟩
      use x
      rename_i h
      subst hFk hGm h
      simp_all only [zero_add]
      apply And.intro
      · induction i with
        | zero =>
          aesop
        | succ i ih =>
          exact hF_step i ( Nat.lt_succ_self i ) |> fun ⟨ y, hy, hy' ⟩ => hy'.symm ▸ IntermediateField.subset_adjoin ℚ _ ( Set.mem_insert_of_mem _ ( ih fun j hj => hF_step j ( Nat.lt_succ_of_lt hj ) ) )
      · refine le_antisymm ?_ ?_ <;> simp_all +decide [ IntermediateField.adjoin_le_iff, Set.insert_subset_iff ]
        · exact ⟨ fun y hy => IntermediateField.subset_adjoin ℚ _ <| Set.mem_insert_of_mem _ <| by aesop, IntermediateField.subset_adjoin ℚ _ <| Set.mem_insert _ _ ⟩
        · exact ⟨ IntermediateField.subset_adjoin _ _ <| Set.mem_union_right _ <| IntermediateField.subset_adjoin _ _ <| Set.mem_insert _ _, fun y hy => IntermediateField.subset_adjoin _ _ <| Set.mem_union_left _ hy ⟩
    · obtain ⟨ x, hx₁, hx₂ ⟩ := hG_step ( i - k ) ( by omega )
      refine ⟨ x, ?_, ?_ ⟩
      · exact IntermediateField.subset_adjoin _ _ ( Set.mem_union_right _ hx₁ )
      · rw [ show i + 1 - k = i - k + 1 by omega, hx₂ ]
        refine le_antisymm ?_ ?_ <;> simp_all +decide [ IntermediateField.adjoin_le_iff, Set.insert_subset_iff ]
        · exact ⟨ fun y hy => IntermediateField.subset_adjoin _ _ <| by aesop, IntermediateField.subset_adjoin _ _ <| by aesop, fun y hy => IntermediateField.subset_adjoin _ _ <| by aesop ⟩
        · refine ⟨ ?_, ?_, ?_ ⟩
          · exact IntermediateField.subset_adjoin _ _ ( Set.mem_union_right _ ( IntermediateField.subset_adjoin _ _ ( Set.mem_insert _ _ ) ) )
          · exact fun x hx => IntermediateField.subset_adjoin _ _ ( Set.mem_union_left _ hx )
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
    induction hx with
    | rat q =>
      exact ⟨ ⊥, by simp_all only [SubfieldClass.ratCast_mem], hasQuadTower_bot ⟩
    | add hx hy hx_ih hy_ih =>
      simp_all only [Set.mem_setOf_eq]
      obtain ⟨w, h⟩ := hx_ih
      obtain ⟨w_1, h_1⟩ := hy_ih
      obtain ⟨left, right⟩ := h
      obtain ⟨left_1, right_1⟩ := h_1
      exact ⟨ _, add_mem ( IntermediateField.subset_adjoin ℚ _ <| Set.mem_union_left _ left ) ( IntermediateField.subset_adjoin ℚ _ <| Set.mem_union_right _ left_1 ), hasQuadTower_sup right right_1 ⟩
    | neg hx hx_ih =>
      simp_all only [Set.mem_setOf_eq, neg_mem_iff]
    | mul hx hy hx_ih hy_ih =>
      simp_all only [Set.mem_setOf_eq]
      obtain ⟨w, h⟩ := hx_ih
      obtain ⟨w_1, h_1⟩ := hy_ih
      obtain ⟨left, right⟩ := h
      obtain ⟨left_1, right_1⟩ := h_1
      use w ⊔ w_1
      exact ⟨ Subalgebra.mul_mem _ ( IntermediateField.subset_adjoin _ _ ( by aesop ) ) ( IntermediateField.subset_adjoin _ _ ( by aesop ) ), hasQuadTower_sup right right_1 ⟩
    | inv hx hx0 hx_ih =>
      aesop
    | sqrt hx hx0 hx_ih =>
      rename_i y
      rcases hx_ih with ⟨ K, hK₁, hK₂ ⟩
      exact ⟨ K ⊔ IntermediateField.adjoin ℚ { Real.sqrt ‹_› }, by aesop_cat, hasQuadTower_adjoin_sqrt hK₂ hK₁ ⟩
  aesop
/-
If x is constructible, then the degree of Q(x) over Q is a power of 2.
Proof:
By `constructible_implies_hasQuadTower`, there exists a field K containing x with a quadratic tower.
By `hasQuadTower_finrank`, [K:Q] = 2 ^ m for some m.
Since Q(x) is a subfield of K, [K:Q] = [K:Q(x)] * [Q(x):Q].
Thus [Q(x):Q] divides 2 ^ m.
Therefore [Q(x):Q] is a power of 2.
-/
lemma degree_of_constructible (x : ℝ) (hx : Constructible x) :
    ∃ n : ℕ, Module.finrank ℚ (IntermediateField.adjoin ℚ {x}) = 2 ^ n := by
  have h_deg : ∃ (K : IntermediateField ℚ ℝ), x ∈ K ∧ HasQuadTower K := by
    exact constructible_implies_hasQuadTower x hx
  have := h_deg.choose_spec.2
  have := hasQuadTower_finrank _ this
  have h_div : Module.finrank ℚ (↥(IntermediateField.adjoin ℚ {x})) ∣ Module.finrank ℚ (↥h_deg.choose) := by
    have h_div : IntermediateField.adjoin ℚ {x} ≤ h_deg.choose := by
      exact IntermediateField.adjoin_le_iff.mpr ( Set.singleton_subset_iff.mpr h_deg.choose_spec.1 )
    exact IntermediateField.finrank_dvd_of_le_right h_div
  rw [ this.choose_spec ] at h_div; rw [ Nat.dvd_prime_pow ] at h_div <;> norm_num at * ; tauto
/-
The degree of the field extension Q(x) over Q, where x ^ 3 = 2, is 3.
Proof:
The minimal polynomial of x over Q is X ^ 3 - 2.
This polynomial is irreducible over Q because it has degree 3 and no rational roots (if p/q is a root, then p ^ 3 = 2q ^ 3, which is impossible for coprime p, q).
Since the minimal polynomial has degree 3, the degree of the extension is 3.
-/
lemma minpoly_degree_of_cube_root_two {x : ℝ} (h : x ^ 3 = 2) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ {x}) = 3 := by
  -- The minimal polynomial of $x$ over $\mathbb{Q}$ is $x ^ 3 - 2$, which is irreducible over $\mathbb{Q}$.
  have h_min_poly : minpoly ℚ x = Polynomial.X ^ 3 - 2 := by
    refine Eq.symm ( minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_ )
    · -- We'll use that $x ^ 3 - 2$ is irreducible over $\mathbb{Q}$ because it has no rational roots and its degree is 3.
      have h_irred : Irreducible (Polynomial.X ^ 3 - 2 : Polynomial ℚ) := by
        have h_no_rational_roots : ¬∃ (q : ℚ), q ^ 3 = 2 := by
          simp_all only [not_exists]
          intro x_1
          apply Aesop.BuiltinRules.not_intro
          intro a
          -- If $x_1 ^ 3 = 2$, then $x_1$ must be of the form $p/q$ where $p ^ 3 = 2q ^ 3$.
          obtain ⟨p, q, hpq, h_coprime⟩ : ∃ p q : ℤ, Int.gcd p q = 1 ∧ x_1 = p / q ∧ p ^ 3 = 2 * q ^ 3 := by
            exact ⟨ x_1.num, x_1.den, x_1.reduced, x_1.num_div_den.symm, by simp ( config := { decide := Bool.true } ) [ ← @Int.cast_inj ℚ, ← a, ← mul_pow ] ⟩
          -- Since $p ^ 3 = 2q ^ 3$, we see that $p$ must be a multiple of $q$. Let $p = kq$ for some integer $k$.
          obtain ⟨k, hk⟩ : ∃ k : ℤ, p = k * q := by
            exact exists_eq_mul_left_of_dvd <| Int.pow_dvd_pow_iff ( by decide ) |>.1 <| h_coprime.2.symm ▸ dvd_mul_left _ _
          by_cases hq : q = 0 <;> simp_all +decide [ mul_pow ]
          have hk_lt_two : k < 2 := by
            by_contra hge
            push Not at hge
            nlinarith [h_coprime.2, sq_nonneg k]
          have hk_gt_one : 1 < k := by
            by_contra hle
            push Not at hle
            have hcases : k ≤ 0 ∨ k = 1 := by omega
            rcases hcases with hk_nonpos | rfl
            · nlinarith [h_coprime.2, sq_nonneg k]
            · norm_num at h_coprime
          omega
        -- Since $x ^ 3 - 2$ has no rational roots and its degree is 3, it must be irreducible over $\mathbb{Q}$.
        have h_irred : ∀ p q : Polynomial ℚ, p.degree > 0 → q.degree > 0 → p * q = Polynomial.X ^ 3 - 2 → False := by
          intros p q hp hq h_factor
          have h_deg : p.degree + q.degree = 3 := by
            erw [ ← Polynomial.degree_mul, h_factor, Polynomial.degree_X_pow_sub_C ] <;> norm_num
          -- Since $p$ and $q$ are non-constant polynomials with degrees adding up to 3, one of them must have degree 1.
          obtain (h_deg_p | h_deg_q) : p.degree = 1 ∨ q.degree = 1 := by
            erw [ Polynomial.degree_eq_natDegree ( Polynomial.ne_zero_of_degree_gt hp ), Polynomial.degree_eq_natDegree ( Polynomial.ne_zero_of_degree_gt hq ) ] at * ; norm_cast at * ; omega
          · -- If $p$ has degree 1, then $p$ is a linear polynomial with a rational root.
            obtain ⟨r, hr⟩ : ∃ r : ℚ, p.eval r = 0 := by
              exact Polynomial.exists_root_of_degree_eq_one h_deg_p
            replace h_factor := congr_arg ( Polynomial.eval r ) h_factor; norm_num [ hr ] at h_factor; exact h_no_rational_roots ⟨ r, by linarith ⟩
          · -- If $q$ has degree 1, then it must have a rational root.
            obtain ⟨r, hr⟩ : ∃ r : ℚ, q.eval r = 0 := by
              exact Polynomial.exists_root_of_degree_eq_one h_deg_q
            replace h_factor := congr_arg ( Polynomial.eval r ) h_factor; norm_num [ hr ] at h_factor; exact h_no_rational_roots ⟨ r, by linarith ⟩
        constructor <;> contrapose! h_irred <;> aesop (config := {warnOnNonterminal := false})
        · exact absurd ( Polynomial.degree_eq_zero_of_isUnit h_irred ) ( by erw [ Polynomial.degree_X_pow_sub_C ] <;> norm_num )
        · exact ⟨ w, not_le.mp fun h => left_1 <| Polynomial.isUnit_iff_degree_eq_zero.mpr <| le_antisymm h <| le_of_not_gt fun h' => by apply_fun Polynomial.eval 0 at left; aesop, w_1, not_le.mp fun h => right <| Polynomial.isUnit_iff_degree_eq_zero.mpr <| le_antisymm h <| le_of_not_gt fun h' => by apply_fun Polynomial.eval 0 at left; aesop, rfl ⟩
      exact h_irred
    · simp_all only [Polynomial.aeval_sub, map_pow, Polynomial.aeval_X]
      erw [ Polynomial.aeval_C ] ; norm_num
    · erw [ Polynomial.Monic, Polynomial.leadingCoeff_X_pow_sub_C ] ; norm_num
  have := IntermediateField.adjoin.finrank ( show IsIntegral ℚ x from by exact ( show IsIntegral ℚ x from by exact ( by exact ( by exact ( by exact ( by exact ( by exact ⟨ Polynomial.X ^ 3 - 2, Polynomial.monic_X_pow_sub_C _ ( by norm_num ), by aesop ⟩ ) ) ) ) ) ) )
  simp_all only
  erw [ Polynomial.natDegree_X_pow_sub_C ]
end AristotleLemmas
theorem doubling_the_cube_impossible :
    ¬ ∃ x : ℝ, x ^ 3 = (2 : ℝ) ∧ Constructible x := by
  by_contra h
  obtain ⟨x, hx_cube, hx_field⟩ := h
  have := minpoly_degree_of_cube_root_two hx_cube
  exact absurd ( degree_of_constructible x hx_field ) ( by rintro ⟨ n, hn ⟩ ; exact absurd ( this.symm.trans hn ) ( by intro H; linarith [ Nat.pow_le_pow_right ( show 1 ≤ 2 by decide ) ( show n ≥ 2 by contrapose! H; interval_cases n <;> norm_num ) ] ) )
/- **Impossibility of trisecting the angle** (in the classical sense): there is
no straightedge-and-compass construction which, for *every* constructible angle
`θ`, produces a constructible angle equal to `θ / 3`. -/
noncomputable section AristotleLemmas
/-
The number $\cos(\pi/9)$ is a root of the polynomial $8x ^ 3 - 6x - 1$.
-/
lemma cos_pi_div_9_root : 8 * (Real.cos (Real.pi / 9)) ^ 3 - 6 * (Real.cos (Real.pi / 9)) - 1 = 0 := by
  have := Real.cos_three_mul ( Real.pi / 9 ) ; rw [ ( by ring : 3 * ( Real.pi / 9 ) = Real.pi / 3 ) ] at this ; rw [ Real.cos_pi_div_three ] at this ; linarith
/-
The polynomial $X ^ 3 - 3X - 1$ is irreducible over the rationals.
-/
open Polynomial in
lemma trisection_poly_irreducible : Irreducible (X ^ 3 - 3 * X - 1 : ℚ[X]) := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · rw [show (X ^ 3 - 3 * X - 1 : ℚ[X]).natDegree = 3 by compute_degree!]
    norm_num
  · intro r hr
    have hroot_int : aeval r (X ^ 3 - 3 * X - C (1 : ℤ) : ℤ[X]) = 0 := by
      simpa [aeval_def] using hr
    have hmonic : (X ^ 3 - 3 * X - C (1 : ℤ) : ℤ[X]).Monic := by
      monicity!
    rcases exists_integer_of_is_root_of_monic (A := ℤ) (K := ℚ) hmonic hroot_int with
      ⟨z, hz, hzdiv⟩
    have hzroot : z ^ 3 - 3 * z - 1 = (0 : ℤ) := by
      have hzq : (z : ℚ) ^ 3 - 3 * (z : ℚ) - 1 = 0 := by
        rw [show (z : ℚ) = r from hz.symm]
        simpa [aeval_def] using hr
      exact_mod_cast hzq
    rcases hzdiv with ⟨u, hu⟩
    have hzu : z * (-u) = 1 := by
      norm_num at hu ⊢
      linarith
    have hz_cases : z = 1 ∨ z = -1 := Int.eq_one_or_neg_one_of_mul_eq_one hzu
    rcases hz_cases with rfl | rfl <;> norm_num at hzroot
/-
The number $2\cos(\pi/9)$ is a root of the polynomial $X ^ 3 - 3X - 1$.
-/
open Polynomial in
lemma trisection_poly_root : aeval (2 * Real.cos (Real.pi / 9)) (X ^ 3 - 3 * X - 1 : ℚ[X]) = 0 := by
  -- Substitute $x = 2 \cos(\pi/9)$ into the polynomial $X ^ 3 - 3X - 1$ and show that it evaluates to zero.
  have h_subst : (2 * Real.cos (Real.pi / 9)) ^ 3 - 3 * (2 * Real.cos (Real.pi / 9)) - 1 = 0 := by
    have := Real.cos_three_mul ( Real.pi / 9 ) ; rw [ ( by ring : 3 * ( Real.pi / 9 ) = Real.pi / 3 ) ] at this ; rw [ Real.cos_pi_div_three ] at this ; nlinarith
  convert h_subst using 1
  norm_num [ Polynomial.aeval_def ]
/-
If $x ^ 2 \in K$, then the degree of the extension $K(x)/K$ is either 1 or 2.
-/
open IntermediateField Polynomial
lemma degree_adjoin_sq' (K : IntermediateField ℚ ℝ) (x : ℝ) (hx : x ^ 2 ∈ K) :
    Module.finrank K (adjoin K {x}) = 1 ∨ Module.finrank K (adjoin K {x}) = 2 := by
      have hxint : IsIntegral K x := by
        refine ⟨Polynomial.X ^ 2 - Polynomial.C (⟨x ^ 2, hx⟩ : K), ?_, ?_⟩
        · exact Polynomial.monic_X_pow_sub_C _ two_ne_zero
        · simp
      haveI : FiniteDimensional K (adjoin K {x}) :=
        IntermediateField.adjoin.finiteDimensional hxint
      haveI : Module.Free K (adjoin K {x}) :=
        Module.Free.of_divisionRing K (adjoin K {x})
      -- Let $L = K(x)$.
      set L : IntermediateField K ℝ := IntermediateField.adjoin K {x}
      have h_deg : (minpoly K x).degree ≤ 2 := by
        have h_deg : minpoly K x ∣ Polynomial.X ^ 2 - Polynomial.C (⟨x ^ 2, hx⟩ : K) := by
          exact minpoly.dvd K x ( by aesop )
        exact le_trans ( Polynomial.degree_le_of_dvd h_deg <| by exact ne_of_apply_ne Polynomial.degree <| by erw [ Polynomial.degree_X_pow_sub_C ] <;> norm_num ) <| by erw [ Polynomial.degree_X_pow_sub_C ] <;> norm_num
      have h_deg : Module.finrank K L = (minpoly K x).natDegree := by
        convert ( IntermediateField.adjoin.finrank <| show IsIntegral K x from ?_ )
        refine ⟨ Polynomial.X ^ 2 - Polynomial.C ( ⟨ x ^ 2, hx ⟩ : K ), ?_, ?_ ⟩ <;> norm_num
        erw [ Polynomial.Monic, Polynomial.leadingCoeff_X_pow_sub_C ] ; norm_num
      have h_deg_pos : 0 < (minpoly K x).natDegree := by
        apply minpoly.natDegree_pos
        refine ⟨ Polynomial.X ^ 2 - Polynomial.C ( ⟨ x ^ 2, hx ⟩ : K ), ?_, ?_ ⟩
        · erw [ Polynomial.Monic, Polynomial.leadingCoeff_X_pow_sub_C ] ; norm_num
        · simp_all only [eval₂_sub, eval₂_X_pow, eval₂_C, IntermediateField.algebraMap_apply, sub_self, L]
      have := Polynomial.natDegree_le_of_degree_le ‹_›; interval_cases _ : Polynomial.natDegree ( minpoly K x ) <;> aesop
/-
Define `DyadicExtension` as a field obtained by a sequence of square root adjunctions.
Prove that any dyadic extension has degree a power of 2.
-/
open IntermediateField Polynomial
inductive DyadicExtension : IntermediateField ℚ ℝ → Prop
  | base : DyadicExtension ⊥
  | step {K : IntermediateField ℚ ℝ} {x : ℝ} (hK : DyadicExtension K) (hx : x ^ 2 ∈ K) :
      DyadicExtension (K ⊔ adjoin ℚ {x})
lemma dyadic_degree_pow2 (K : IntermediateField ℚ ℝ) (h : DyadicExtension K) :
    ∃ n : ℕ, Module.finrank ℚ K = 2 ^ n := by
  induction h
  · exact ⟨0, by simp⟩
  · rename_i K x hK hx ih
    rcases ih with ⟨n, hn⟩
    rcases finrank_adjoin_sq hx ⟨n, hn⟩ with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have hfield :
        K ⊔ adjoin ℚ {x} = adjoin ℚ ((K : Set ℝ) ∪ {x}) := by
      rw [IntermediateField.adjoin_union, IntermediateField.adjoin_self]
    rw [hfield]
    exact hm
/-
If $K$ and $L$ are dyadic extensions, there exists a dyadic extension $M$ containing both $K$ and $L$.
-/
open IntermediateField
lemma dyadic_sup (K L : IntermediateField ℚ ℝ) (hK : DyadicExtension K) (hL : DyadicExtension L) :
    ∃ M : IntermediateField ℚ ℝ, DyadicExtension M ∧ K ≤ M ∧ L ≤ M := by
      induction hL with
      | base =>
        simp_all only [bot_le, and_true]
        apply Exists.intro
        · apply And.intro
          on_goal 2 => { rfl
          }
          · simp_all only
      | @step L' x hL' hx ih =>
        obtain ⟨ M, hM₁, hM₂, hM₃ ⟩ := ih
        use M ⊔ IntermediateField.adjoin ℚ { x }
        simp_all only [sup_le_iff, le_sup_right, and_true]
        apply And.intro
        · exact DyadicExtension.step hM₁ ( by simpa using hM₃ hx )
        · apply And.intro
          · exact le_trans hM₂ le_sup_left
          · exact le_sup_of_le_left hM₃
/-
Every constructible number is contained in some dyadic extension field.
-/
open IntermediateField
lemma constructible_in_dyadic (x : ℝ) (hx : Constructible x) :
    ∃ K : IntermediateField ℚ ℝ, DyadicExtension K ∧ x ∈ K := by
  induction hx with
  | rat q =>
      exact ⟨⊥, DyadicExtension.base, by simp⟩
  | add hx hy ihx ihy =>
      rcases ihx with ⟨K, hK, hxK⟩
      rcases ihy with ⟨L, hL, hyL⟩
      rcases dyadic_sup K L hK hL with ⟨M, hM, hKM, hLM⟩
      exact ⟨M, hM, M.add_mem (hKM hxK) (hLM hyL)⟩
  | neg hx ihx =>
      rcases ihx with ⟨K, hK, hxK⟩
      exact ⟨K, hK, K.neg_mem hxK⟩
  | mul hx hy ihx ihy =>
      rcases ihx with ⟨K, hK, hxK⟩
      rcases ihy with ⟨L, hL, hyL⟩
      rcases dyadic_sup K L hK hL with ⟨M, hM, hKM, hLM⟩
      exact ⟨M, hM, M.mul_mem (hKM hxK) (hLM hyL)⟩
  | inv hx hx0 ihx =>
      rcases ihx with ⟨K, hK, hxK⟩
      exact ⟨K, hK, K.inv_mem hxK⟩
  | sqrt hx hx0 ihx =>
      rename_i y
      rcases ihx with ⟨K, hK, hxK⟩
      refine ⟨K ⊔ adjoin ℚ {Real.sqrt y}, DyadicExtension.step hK ?_, ?_⟩
      · simpa [Real.sq_sqrt hx0] using hxK
      · exact SetLike.le_def.mp le_sup_right
          (IntermediateField.subset_adjoin ℚ {Real.sqrt y} (by simp))
end AristotleLemmas
theorem angle_trisection_impossible :
    ¬ (∀ θ : ℝ, ConstructibleAngle θ → ConstructibleAngle (θ / 3)) := by
  by_contra h_contra
  have h_pi_9 : Constructible (2 * Real.cos (Real.pi / 9)) := by
    have h_pi_9 : ConstructibleAngle (Real.pi / 9) := by
      have h_pi_3 : ConstructibleAngle (Real.pi / 3) := by
        have h_cos_pi_3 : Constructible (Real.cos (Real.pi / 3)) := by
          convert Constructible.rat (1 / 2) using 1
          norm_num
        exact h_cos_pi_3
      convert h_contra _ h_pi_3 using 1
      ring
    exact Constructible.mul (Constructible.rat 2) h_pi_9
  let x := 2 * Real.cos (Real.pi / 9)
  have hx : Constructible x := h_pi_9
  rcases constructible_in_dyadic x hx with ⟨K, hK, hxK⟩
  rcases dyadic_degree_pow2 K hK with ⟨n, hn⟩
  have h_min_poly : minpoly ℚ x = Polynomial.X ^ 3 - 3 * Polynomial.X - 1 := by
    refine Eq.symm (minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_)
    · convert trisection_poly_irreducible using 1
    · norm_num +zetaDelta at *
      erw [Polynomial.aeval_C]
      norm_num
      have hcos := Real.cos_three_mul (Real.pi / 9)
      rw [(by ring : 3 * (Real.pi / 9) = Real.pi / 3)] at hcos
      norm_num at hcos
      nlinarith [Real.cos_sq' (Real.pi / 9)]
    · erw [Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_sub_C,
        Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num
      norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  have h_deg : Module.finrank ℚ (IntermediateField.adjoin ℚ {x}) = 3 := by
    have hxint : IsIntegral ℚ x := by
      refine ⟨Polynomial.X ^ 3 - 3 * Polynomial.X - 1, ?_, ?_⟩
      · erw [Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_sub_C,
          Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num
        norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
      · have hcos := Real.cos_three_mul (Real.pi / 9)
        rw [(by ring : 3 * (Real.pi / 9) = Real.pi / 3), Real.cos_pi_div_three] at hcos
        norm_num +zetaDelta
        linarith
    rw [IntermediateField.adjoin.finrank hxint, h_min_poly]
    rw [show (Polynomial.X ^ 3 - 3 * Polynomial.X - 1 : Polynomial ℚ).natDegree = 3 by
      compute_degree!]
  have h_sub : IntermediateField.adjoin ℚ {x} ≤ K := by
    exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hxK)
  have h_div : Module.finrank ℚ (IntermediateField.adjoin ℚ {x}) ∣ Module.finrank ℚ K :=
    IntermediateField.finrank_dvd_of_le_right h_sub
  rw [h_deg, hn] at h_div
  have h_three_dvd_two : 3 ∣ 2 := by
    exact Nat.Prime.dvd_of_dvd_pow Nat.prime_three h_div
  norm_num at h_three_dvd_two
/-- Freek Wiedijk’s theorem 8: “The Impossibility of Trisecting the Angle and
Doubling the Cube”, packaged as a single statement. -/
theorem freek_08 :
    (¬ (∀ θ : ℝ, ConstructibleAngle θ → ConstructibleAngle (θ / 3))) ∧
    (¬ ∃ x : ℝ, x ^ 3 = (2 : ℝ) ∧ Constructible x) := by
  exact ⟨angle_trisection_impossible, doubling_the_cube_impossible⟩
open scoped EuclideanGeometry
noncomputable section
/-- The standard Euclidean plane, implemented as `ℝ²`. -/
abbrev Point : Type := EuclideanSpace ℝ (Fin 2)
namespace RulerCompass
/-- The (infinite) straight line through the points `A` and `B`. -/
def line (A B : Point) : Set Point :=
  { P : Point | ∃ t : ℝ, P = (1 - t) • A + t • B }
/-- The circle of radius `r` with center `C`. -/
def circle (C : Point) (r : ℝ) : Set Point :=
  { P : Point | (dist : Point → Point → ℝ) P C = r }
/-- The circle with center `C` and passing through the point `D`. -/
def circleThrough (C D : Point) : Set Point :=
  circle C ((dist : Point → Point → ℝ) C D)
/-- A base configuration for ruler-and-compass constructions in the Euclidean plane:
two distinct points `O` and `E`, with the segment `OE` declared to have unit length. -/
structure RCBase where
  O : Point
  E : Point
  hOE : O ≠ E
  unit : (dist : Point → Point → ℝ) O E = 1
/-- Points that are ruler-and-compass constructible in the Euclidean plane,
starting from a fixed base configuration. This inductive predicate is closed
under the usual straightedge-and-compass operations: intersections of lines,
line–circle intersections, and circle–circle intersections. -/
inductive RCPoint (cfg : RCBase) : Point → Prop
  | base_O :
      RCPoint cfg (RCBase.O cfg)
  | base_E :
      RCPoint cfg (RCBase.E cfg)
  | line_line
      {A B C D P : Point}
      (hA : RCPoint cfg A) (hB : RCPoint cfg B)
      (hC : RCPoint cfg C) (hD : RCPoint cfg D)
      (hAB : A ≠ B) (hCD : C ≠ D)
      -- Prevent the degenerate case where `line A B = line C D`,
      -- which would make *every* point on the line an "intersection".
      (hLines : line A B ≠ line C D)
      (hP₁ : P ∈ line A B) (hP₂ : P ∈ line C D) :
      RCPoint cfg P
  | line_circle
      {A B C D P : Point}
      (hA : RCPoint cfg A) (hB : RCPoint cfg B)
      (hC : RCPoint cfg C) (hD : RCPoint cfg D)
      (hAB : A ≠ B) (hCD : C ≠ D)
      (hP₁ : P ∈ line A B)
      (hP₂ : P ∈ circleThrough C D) :
      RCPoint cfg P
  | circle_circle
      {A B C D P : Point}
      (hA : RCPoint cfg A) (hB : RCPoint cfg B)
      (hC : RCPoint cfg C) (hD : RCPoint cfg D)
      (hAB : A ≠ B) (hCD : C ≠ D)
      -- Again avoid the degenerate case `circleThrough A B = circleThrough C D`,
      -- which would otherwise allow any point on that circle.
      (hCircles : circleThrough A B ≠ circleThrough C D)
      (hP₁ : P ∈ circleThrough A B)
      (hP₂ : P ∈ circleThrough C D) :
      RCPoint cfg P
namespace RCPoint
variable {cfg : RCBase}
/-! (API lemmas about `RCPoint` could go here.) -/
end RCPoint
/-- The length of the segment from the base point `O` to a point `P`. -/
def segmentLength (cfg : RCBase) (P : Point) : ℝ :=
  (dist : Point → Point → ℝ) (RCBase.O cfg) P
/-- A real number is realized as the length of a ruler-and-compass constructible
segment with one endpoint at the base point `O`. -/
def RCConstructibleLength (cfg : RCBase) (x : ℝ) : Prop :=
  ∃ P : Point, RCPoint cfg P ∧ segmentLength cfg P = x
/-- The angle at the base point `O` from the ray `OE` to the ray `OP`. -/
def baseAngle (cfg : RCBase) (P : Point) : ℝ :=
  ∠ (RCBase.E cfg) (RCBase.O cfg) P
/-- A real angle `θ` is (plane) constructible if there is a ruler-and-compass
constructible point whose base angle equals `θ`. -/
def RCConstructibleAngle (cfg : RCBase) (θ : ℝ) : Prop :=
  ∃ P : Point, RCPoint cfg P ∧ baseAngle cfg P = θ
noncomputable section AristotleLemmas
/-
The coordinates of a point P in the coordinate system defined by the base points O and E. O is the origin, and E is at (1, 0).
-/
open RulerCompass
noncomputable def RulerCompass.RC_coords (cfg : RCBase) (P : Point) : ℝ × ℝ :=
  let u := cfg.E - cfg.O
  let v : Point := EuclideanSpace.single (0 : Fin 2) (-(u (1 : Fin 2))) +
    EuclideanSpace.single (1 : Fin 2) (u (0 : Fin 2))
  let d := P - cfg.O
  (inner (𝕜 := ℝ) u d, inner (𝕜 := ℝ) v d)
/-
The solution to a 2x2 linear system with constructible coefficients is constructible, provided the determinant is non-zero.
-/
lemma Constructible.cramer_rule_2x2 {a b c d e f : ℝ}
  (ha : Constructible a) (hb : Constructible b) (hc : Constructible c)
  (hd : Constructible d) (he : Constructible e) (hf : Constructible f)
  (h_det : a * d - b * c ≠ 0) :
  Constructible ((e * d - b * f) / (a * d - b * c)) ∧
  Constructible ((a * f - e * c) / (a * d - b * c)) := by
    -- We'll use the fact that if the denominator is non-zero, then the division of constructible numbers is constructible.
    have h_div : ∀ x y : ℝ, Constructible x → Constructible y → y ≠ 0 → Constructible (x / y) := by
      exact fun x y hx hy hy0 => by simpa [ div_eq_mul_inv ] using Constructible.mul hx ( Constructible.inv hy hy0 )
    -- Since the numerator and denominator are constructible and the denominator is non-zero, the division is constructible.
    have h_num_denom : Constructible (e * d - b * f) ∧ Constructible (a * f - e * c) ∧ Constructible (a * d - b * c) := by
      exact ⟨ by exact Constructible.add ( Constructible.mul he hd ) ( Constructible.neg ( Constructible.mul hb hf ) ), by exact Constructible.add ( Constructible.mul ha hf ) ( Constructible.neg ( Constructible.mul he hc ) ), by exact Constructible.add ( Constructible.mul ha hd ) ( Constructible.neg ( Constructible.mul hb hc ) ) ⟩
    exact ⟨ h_div _ _ h_num_denom.1 h_num_denom.2.2 h_det, h_div _ _ h_num_denom.2.1 h_num_denom.2.2 h_det ⟩
/-
The roots of a quadratic equation with constructible coefficients are constructible, provided the discriminant is non-negative and the leading coefficient is non-zero.
-/
lemma Constructible.quadratic_roots {a b c : ℝ}
  (ha : Constructible a) (hb : Constructible b) (hc : Constructible c)
  (h_delta : 0 ≤ b ^ 2 - 4 * a * c) (ha_ne_zero : a ≠ 0) :
  Constructible ((-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)) ∧
  Constructible ((-b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)) := by
    -- The square root of a constructible non-negative number is constructible.
    have h_sqrt : Constructible (Real.sqrt (b ^ 2 - 4 * a * c)) := by
      apply_rules [ Constructible.sqrt, Constructible.mul, Constructible.add, Constructible.rat, Constructible.neg ]
      exact mod_cast Constructible.rat 1
    constructor
    · apply_rules [ Constructible.add, Constructible.neg, Constructible.inv, Constructible.mul, Constructible.rat ]
      positivity
    · apply_rules [ Constructible.add, Constructible.neg, Constructible.mul, Constructible.inv, Constructible.sqrt ]
      · exact Constructible.rat 2
      · positivity
/-
A point P has constructible coordinates if both its x and y coordinates (in the standard basis) are constructible numbers.
-/
open RulerCompass
def RulerCompass.IsConstructibleCoords (cfg : RCBase) (P : Point) : Prop :=
  Constructible (RulerCompass.RC_coords cfg P).1 ∧ Constructible (RulerCompass.RC_coords cfg P).2
/-
Points on the line passing through A and B satisfy the linear equation $(y_A - y_B)x + (x_B - x_A)y = x_B y_A - y_B x_A$.
-/
lemma RulerCompass.line_equation {cfg : RCBase} {A B P : Point} (h : P ∈ line A B) :
    let x := fun Q => (RulerCompass.RC_coords cfg Q).1
    let y := fun Q => (RulerCompass.RC_coords cfg Q).2
    (y A - y B) * x P + (x B - x A) * y P = x B * y A - y B * x A := by
  rcases h with ⟨t, rfl⟩
  unfold RulerCompass.RC_coords
  simp [inner_add_right, inner_smul_right, sub_eq_add_neg]
  ring
set_option maxHeartbeats 8000000 in
-- The determinant-zero line proof expands several coordinate algebra cases.
/-
If the determinant of the direction vectors of two lines is zero, and the lines intersect, then the lines are identical.
-/
lemma RulerCompass.lines_eq_of_det_eq_zero {cfg : RCBase} {A B C D P : Point}
    (hAB : A ≠ B) (hCD : C ≠ D)
    (hP₁ : P ∈ line A B) (hP₂ : P ∈ line C D)
    (h_det : let x := fun Q => (RulerCompass.RC_coords cfg Q).1
             let y := fun Q => (RulerCompass.RC_coords cfg Q).2
             (y A - y B) * (x D - x C) - (x B - x A) * (y C - y D) = 0) :
    line A B = line C D := by
  unfold RulerCompass.line at *
  have h_parallel : ∃ k : ℝ, D - C = k • (B - A) := by
    have h_linear_dep : (D - C) 0 * (B - A) 1 - (D - C) 1 * (B - A) 0 = 0 := by
      simp [RulerCompass.RC_coords, PiLp.sub_apply, Fin.sum_univ_two, inner] at h_det ⊢
      ring_nf at h_det ⊢
      have hunit : (cfg.E 0 - cfg.O 0) ^ 2 + (cfg.E 1 - cfg.O 1) ^ 2 = 1 := by
        have := cfg.unit
        norm_num [dist_eq_norm, EuclideanSpace.norm_eq] at this
        ring_nf at this
        ring_nf
        nlinarith
      nlinarith
    by_cases h_cases : (B - A) 0 = 0
    · use (D - C) 1 / (B - A) 1
      have hB1 : (B - A) 1 ≠ 0 := by
        intro hB1
        apply hAB
        exact PiLp.ext fun i => by
          fin_cases i
          · have hc := h_cases
            simp [PiLp.sub_apply] at hc
            exact (sub_eq_zero.mp hc).symm
          · have hc := hB1
            simp [PiLp.sub_apply] at hc
            exact (sub_eq_zero.mp hc).symm
      have hB1' : B 1 - A 1 ≠ 0 := by
        simpa [PiLp.sub_apply] using hB1
      ext i
      fin_cases i
      · have hDC0 : (D - C) (0 : Fin 2) = 0 := by
          rcases (by simpa [h_cases] using h_linear_dep :
              (D - C) (0 : Fin 2) = 0 ∨ (B - A) (1 : Fin 2) = 0) with h | h
          · exact h
          · exact False.elim (hB1 h)
        simpa [PiLp.smul_apply, h_cases] using hDC0
      · simp [PiLp.smul_apply]
        field_simp [hB1']
    · use (D - C) 0 / (B - A) 0
      have hB0' : B 0 - A 0 ≠ 0 := by
        simpa [PiLp.sub_apply] using h_cases
      ext i
      fin_cases i
      · simp [PiLp.smul_apply]
        field_simp [hB0']
      · simp [PiLp.smul_apply]
        field_simp [hB0']
        have hlin := h_linear_dep
        simp [PiLp.sub_apply] at hlin
        nlinarith
  rcases h_parallel with ⟨k, hk⟩
  ext Q
  constructor
  · rintro ⟨t, rfl⟩
    rcases hP₁ with ⟨s, hs⟩
    rcases hP₂ with ⟨u, hu⟩
    by_cases hk0 : k = 0
    · have hDC : D = C := by
        rw [hk0, zero_smul, sub_eq_zero] at hk
        exact hk
      exact False.elim (hCD (hDC.symm))
    · use u + (t - s) / k
      have hbase : (1 - s) • A + s • B = (1 - u) • C + u • D := by
        rw [← hs, ← hu]
      have hD : D = C + k • (B - A) := by
        rw [sub_eq_iff_eq_add] at hk
        simpa [add_comm] using hk
      ext i
      have hbase_i := congrArg (fun Z : Point => Z i) hbase
      have hD_i := congrArg (fun Z : Point => Z i) hD
      simp [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply] at hbase_i hD_i ⊢
      rw [hD_i] at hbase_i ⊢
      ring_nf at hbase_i hD_i ⊢
      field_simp [hk0] at *
      ring_nf at hbase_i ⊢
      nlinarith
  · rintro ⟨t, rfl⟩
    rcases hP₁ with ⟨s, hs⟩
    rcases hP₂ with ⟨u, hu⟩
    use s + k * (t - u)
    have hbase : (1 - s) • A + s • B = (1 - u) • C + u • D := by
      rw [← hs, ← hu]
    have hD : D = C + k • (B - A) := by
      rw [sub_eq_iff_eq_add] at hk
      simpa [add_comm] using hk
    ext i
    have hbase_i := congrArg (fun Z : Point => Z i) hbase
    have hD_i := congrArg (fun Z : Point => Z i) hD
    simp [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply] at hbase_i hD_i ⊢
    rw [hD_i] at hbase_i ⊢
    ring_nf at hbase_i hD_i ⊢
    nlinarith
/-
If two distinct lines intersect, the determinant of the linear system formed by their equations is non-zero.
-/
lemma RulerCompass.det_ne_zero_of_inter_distinct {cfg : RCBase} {A B C D P : Point}
    (hAB : A ≠ B) (hCD : C ≠ D)
    (hLines : line A B ≠ line C D)
    (hP₁ : P ∈ line A B) (hP₂ : P ∈ line C D) :
    let x := fun Q => (RulerCompass.RC_coords cfg Q).1
    let y := fun Q => (RulerCompass.RC_coords cfg Q).2
    (y A - y B) * (x D - x C) - (x B - x A) * (y C - y D) ≠ 0 := by
      -- Apply the lemma `lines_eq_of_det_eq_zero` with the equal determinant to derive that the lines are identical, which contradicts `hLines`.
      apply fun h_det => hLines (lines_eq_of_det_eq_zero hAB hCD hP₁ hP₂ h_det)
/-
If two lines are defined by points with constructible coordinates, their intersection point has constructible coordinates.
-/
lemma RulerCompass.line_line_coords_constructible {cfg : RCBase} {A B C D P : Point}
    (hA : IsConstructibleCoords cfg A) (hB : IsConstructibleCoords cfg B)
    (hC : IsConstructibleCoords cfg C) (hD : IsConstructibleCoords cfg D)
    (hAB : A ≠ B) (hCD : C ≠ D)
    (hLines : line A B ≠ line C D)
    (hP₁ : P ∈ line A B) (hP₂ : P ∈ line C D) :
    IsConstructibleCoords cfg P := by
      -- Let's express the coordinates of P in terms of the coordinates of A, B, C, and D.
      obtain ⟨a, b, c, d, e, f, ha, hb, hc, hd, he, hf, h_det⟩ : ∃ a b c d e f : ℝ, a * (RulerCompass.RC_coords cfg P).1 + b * (RulerCompass.RC_coords cfg P).2 = e ∧ c * (RulerCompass.RC_coords cfg P).1 + d * (RulerCompass.RC_coords cfg P).2 = f ∧ a * d - b * c ≠ 0 ∧ Constructible a ∧ Constructible b ∧ Constructible c ∧ Constructible d ∧ Constructible e ∧ Constructible f := by
        use (RulerCompass.RC_coords cfg A).2 - (RulerCompass.RC_coords cfg B).2, (RulerCompass.RC_coords cfg B).1 - (RulerCompass.RC_coords cfg A).1, (RulerCompass.RC_coords cfg C).2 - (RulerCompass.RC_coords cfg D).2, (RulerCompass.RC_coords cfg D).1 - (RulerCompass.RC_coords cfg C).1, (RulerCompass.RC_coords cfg B).1 * (RulerCompass.RC_coords cfg A).2 - (RulerCompass.RC_coords cfg B).2 * (RulerCompass.RC_coords cfg A).1, (RulerCompass.RC_coords cfg D).1 * (RulerCompass.RC_coords cfg C).2 - (RulerCompass.RC_coords cfg D).2 * (RulerCompass.RC_coords cfg C).1
        refine ⟨ ?_, ?_, ?_, ?_ ⟩
        · exact line_equation hP₁
        · field_simp
          convert RulerCompass.line_equation hP₂ using 1 ; ring
        · exact det_ne_zero_of_inter_distinct hAB hCD hLines hP₁ hP₂
        · -- By definition of constructible numbers, the difference of two constructible numbers is constructible.
          have h_diff : ∀ x y : ℝ, Constructible x → Constructible y → Constructible (x - y) := by
            exact fun x y hx hy => by simpa using Constructible.add hx ( Constructible.neg hy )
          have h_mul : ∀ x y : ℝ, Constructible x → Constructible y → Constructible (x * y) := by
            exact fun x y hx hy => Constructible.mul hx hy
          exact ⟨ h_diff _ _ hA.2 hB.2, h_diff _ _ hB.1 hA.1, h_diff _ _ hC.2 hD.2, h_diff _ _ hD.1 hC.1, h_diff _ _ ( h_mul _ _ hB.1 hA.2 ) ( h_mul _ _ hB.2 hA.1 ), h_diff _ _ ( h_mul _ _ hD.1 hC.2 ) ( h_mul _ _ hD.2 hC.1 ) ⟩
      have := Constructible.cramer_rule_2x2 hd he hf h_det.1 h_det.2.1 h_det.2.2 hc
      exact ⟨ by convert this.1 using 1; rw [ show ( RulerCompass.RulerCompass.RC_coords cfg P ).1 = ( e * d - b * f ) / ( a * d - b * c ) by rw [ eq_div_iff hc ] ; linear_combination ha * d - hb * b ], by convert this.2 using 1; rw [ show ( RulerCompass.RulerCompass.RC_coords cfg P ).2 = ( a * f - e * c ) / ( a * d - b * c ) by rw [ eq_div_iff hc ] ; linear_combination hb * a - ha * c ] ⟩
/-
The squared distance between two points is the sum of the squared differences of their coordinates in the standard basis.
-/
lemma RulerCompass.dist_sq_eq_coords_sq_add_sq (cfg : RCBase) (P Q : Point) :
    (dist P Q) ^ 2 = ((RulerCompass.RC_coords cfg P).1 - (RulerCompass.RC_coords cfg Q).1) ^ 2 + ((RulerCompass.RC_coords cfg P).2 - (RulerCompass.RC_coords cfg Q).2) ^ 2 := by
  have hunit : (cfg.E 0 - cfg.O 0) ^ 2 + (cfg.E 1 - cfg.O 1) ^ 2 = 1 := by
    have := cfg.unit
    norm_num [dist_eq_norm, EuclideanSpace.norm_eq] at this
    ring_nf at this
    ring_nf
    nlinarith
  calc
    (dist P Q) ^ 2 = (P 0 - Q 0) ^ 2 + (P 1 - Q 1) ^ 2 := by
      rw [dist_eq_norm, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      norm_num [Fin.sum_univ_two]
    _ =
        ((cfg.E 0 - cfg.O 0) * (P 0 - Q 0) +
            (cfg.E 1 - cfg.O 1) * (P 1 - Q 1)) ^ 2 +
          (-(cfg.E 1 - cfg.O 1) * (P 0 - Q 0) +
              (cfg.E 0 - cfg.O 0) * (P 1 - Q 1)) ^ 2 := by
      ring_nf
      linear_combination -((P 0 - Q 0) ^ 2 + (P 1 - Q 1) ^ 2) * hunit
    _ = ((RulerCompass.RC_coords cfg P).1 - (RulerCompass.RC_coords cfg Q).1) ^ 2 +
        ((RulerCompass.RC_coords cfg P).2 - (RulerCompass.RC_coords cfg Q).2) ^ 2 := by
      unfold RulerCompass.RC_coords
      norm_num [Fin.sum_univ_two, inner]
      ring
/-
If a point (x, y) lies on a line $ax + by = c$ and a circle $(x-x_0) ^ 2 + (y-y_0) ^ 2 = r ^ 2$ with constructible coefficients, then x and y are constructible.
-/
lemma Constructible.coords_of_line_circle_inter {a b c x0 y0 r2 x y : ℝ}
    (ha : Constructible a) (hb : Constructible b) (hc : Constructible c)
    (hx0 : Constructible x0) (hy0 : Constructible y0) (hr2 : Constructible r2)
    (h_line : a * x + b * y = c)
    (h_circle : (x - x0) ^ 2 + (y - y0) ^ 2 = r2)
    (h_ab : a ≠ 0 ∨ b ≠ 0) :
    Constructible x ∧ Constructible y := by
      by_cases ha' : a = 0 <;> by_cases hb' : b = 0 <;> simp_all ( config := { decide := Bool.true } )
      · -- Since $b \neq 0$, we can solve for $y$ in the line equation: $y = \frac{c}{b}$.
        have hy : y = c / b := by
          rw [ ← h_line, mul_div_cancel_left₀ _ hb' ]
        -- Since $y$ is constructible, we can solve for $x$ in the circle equation: $x = x0 \pm \sqrt{r ^ 2 - (y - y0) ^ 2}$.
        have hx : x = x0 + Real.sqrt (r2 - (y - y0) ^ 2) ∨ x = x0 - Real.sqrt (r2 - (y - y0) ^ 2) := by
          exact Classical.or_iff_not_imp_left.2 fun h => mul_left_cancel₀ ( sub_ne_zero_of_ne h ) <| by linarith [ Real.mul_self_sqrt ( show 0 ≤ r2 - ( y - y0 ) ^ 2 by linarith [ sq_nonneg ( x - x0 ) ] ) ]
        -- Since $r2 - (y - y0) ^ 2$ is constructible, its square root is also constructible.
        have h_sqrt : Constructible (Real.sqrt (r2 - (y - y0) ^ 2)) := by
          have h_sqrt : Constructible (r2 - (y - y0) ^ 2) := by
            have h_sqrt : Constructible (y - y0) := by
              have h_sqrt : Constructible y := by
                rw [ hy ]
                simpa using Constructible.mul hc ( Constructible.inv hb hb' )
              convert Constructible.add h_sqrt ( Constructible.neg hy0 ) using 1
            have h_sqrt : Constructible ((y - y0) ^ 2) := by
              simpa only [ sq ] using Constructible.mul h_sqrt h_sqrt
            have h_sqrt : Constructible (r2 + -((y - y0) ^ 2)) := by
              apply Constructible.add hr2
              apply Constructible.neg h_sqrt
            exact h_sqrt
          exact Constructible.sqrt h_sqrt ( by nlinarith )
        cases hx <;> simp_all ( config := { decide := Bool.true } )
        · exact ⟨ by exact Constructible.add hx0 h_sqrt, by exact Constructible.mul hc ( Constructible.inv hb hb' ) ⟩
        · exact ⟨ by exact Constructible.add hx0 ( Constructible.neg h_sqrt ), by exact Constructible.mul hc ( Constructible.inv hb hb' ) ⟩
      · -- Since $a \neq 0$, we can solve for $x$ in the line equation: $x = \frac{c}{a}$.
        have hx : Constructible x := by
          have hx : Constructible (c / a) := by
            exact Constructible.mul hc ( Constructible.inv ha ha' )
          rwa [ show x = c / a by rw [ eq_div_iff ha' ] ; linarith ]
        -- Since $a \neq 0$, we can solve for $y$ in the circle equation: $y = y0 \pm \sqrt{r2 - (x - x0) ^ 2}$.
        have hy : Constructible (y0 + Real.sqrt (r2 - (x - x0) ^ 2)) ∧ Constructible (y0 - Real.sqrt (r2 - (x - x0) ^ 2)) := by
          have hy : Constructible (r2 - (x - x0) ^ 2) := by
            -- By definition of constructible, if $x$ is constructible, then $x ^ 2$ is also constructible.
            have hx_sq : Constructible (x ^ 2) := by
              simpa only [ sq ] using hx.mul hx
            have hx_sub_sq : Constructible ((x - x0) ^ 2) := by
              have hx_sub_sq : Constructible (x - x0) := by
                convert Constructible.add hx ( Constructible.neg hx0 ) using 1
              simpa only [ sq ] using Constructible.mul hx_sub_sq hx_sub_sq
            have hx_sub_sq : Constructible (r2 - (x - x0) ^ 2) := by
              have h_sub : ∀ {a b : ℝ}, Constructible a → Constructible b → Constructible (a - b) := by
                intro a b ha hb; exact (by
                simpa using Constructible.add ha ( Constructible.neg hb ))
              exact h_sub hr2 hx_sub_sq
            exact hx_sub_sq
          have hy : Constructible (Real.sqrt (r2 - (x - x0) ^ 2)) := by
            exact Constructible.sqrt hy ( by nlinarith )
          exact ⟨ Constructible.add hy0 hy, Constructible.add hy0 ( Constructible.neg hy ) ⟩
        cases' eq_or_eq_neg_of_sq_eq_sq ( y - y0 ) ( Real.sqrt ( r2 - ( x - x0 ) ^ 2 ) ) ( by rw [ Real.sq_sqrt <| sub_nonneg_of_le <| by nlinarith ] ; linarith ) with h h <;> simp_all ( config := { decide := Bool.true } )
        · convert hy.1 using 1 ; linarith
        · convert hy.2 using 1 ; linarith
      · -- Substitute $y = \frac{c - ax}{b}$ into the circle equation to get a quadratic equation in $x$.
        have h_quad_x : ∃ A B C : ℝ, A ≠ 0 ∧ A * x ^ 2 + B * x + C = 0 ∧ Constructible A ∧ Constructible B ∧ Constructible C := by
          refine ⟨ 1 + ( a / b ) ^ 2, -2 * x0 - 2 * ( a / b ) * ( c / b - y0 ), x0 ^ 2 + ( c / b - y0 ) ^ 2 - r2, ?_, ?_, ?_, ?_, ?_ ⟩
          · positivity
          · rw [ ← h_circle ]
            grind +ring
          · apply_rules [ Constructible.add, Constructible.mul, Constructible.inv ]
            · subst h_line h_circle
              convert Constructible.rat 1
              norm_num
            · field_simp
              exact Constructible.rat 1 |> fun h => by simpa [ npowRec ] using h
          · apply_rules [ Constructible.add, Constructible.neg, Constructible.mul, Constructible.rat, Constructible.inv ]
          · -- Since $x0$, $c$, $b$, and $y0$ are constructible, their squares and differences are also constructible.
            have hx0_sq : Constructible (x0 ^ 2) := by
              rw [ pow_two ]
              exact Constructible.mul hx0 hx0
            have hc_div_b : Constructible (c / b) := by
              simpa only [ div_eq_mul_inv ] using Constructible.mul hc ( Constructible.inv hb hb' )
            have hc_div_b_sub_y0 : Constructible (c / b - y0) := by
              exact Constructible.add hc_div_b ( Constructible.neg hy0 )
            have hc_div_b_sub_y0_sq : Constructible ((c / b - y0) ^ 2) := by
              simpa only [ sq ] using Constructible.mul hc_div_b_sub_y0 hc_div_b_sub_y0
            have hr2 : Constructible r2 := by
              assumption
            exact Constructible.add ( Constructible.add hx0_sq hc_div_b_sub_y0_sq ) ( Constructible.neg hr2 )
        obtain ⟨ A, B, C, hA, hB, hA', hB', hC' ⟩ := h_quad_x; have h_x : Constructible x := by
          by_cases h_det : B ^ 2 - 4 * A * C ≥ 0
          · have := Constructible.quadratic_roots hA' hB' hC' h_det hA
            -- Since $x$ is a root of the quadratic equation, it must be equal to one of the roots given by the quadratic formula.
            have h_root : x = (-B + Real.sqrt (B ^ 2 - 4 * A * C)) / (2 * A) ∨ x = (-B - Real.sqrt (B ^ 2 - 4 * A * C)) / (2 * A) := by
              field_simp
              exact Classical.or_iff_not_imp_left.2 fun h => mul_left_cancel₀ ( sub_ne_zero_of_ne h ) <| by cases lt_or_gt_of_ne hA <;> nlinarith [ Real.mul_self_sqrt h_det ]
            exact h_root.elim ( fun h => h.symm ▸ this.1 ) fun h => h.symm ▸ this.2
          · cases lt_or_gt_of_ne hA <;> nlinarith [ sq_nonneg ( B + 2 * A * x ) ]
        -- Since $b \neq 0$, we can solve for $y$ in the line equation: $y = \frac{c - ax}{b}$.
        have h_y : y = (c - a * x) / b := by
          rw [ eq_div_iff hb' ] ; linarith
        -- Since $c$, $a$, and $x$ are constructible, their combination $(c - a * x)$ is also constructible.
        have h_comb : Constructible (c - a * x) := by
          exact Constructible.add ( hc ) ( Constructible.neg ( Constructible.mul ha h_x ) ) |> fun h => by simpa using h
        exact ⟨ h_x, h_y.symm ▸ by exact Constructible.mul h_comb ( Constructible.inv hb hb' ) ⟩
/-
If a point (x, y) lies on the intersection of two distinct circles with constructible centers and squared radii, then x and y are constructible.
-/
lemma Constructible.coords_of_circle_circle_inter {x1 y1 r1sq x2 y2 r2sq x y : ℝ}
    (hx1 : Constructible x1) (hy1 : Constructible y1) (hr1sq : Constructible r1sq)
    (hx2 : Constructible x2) (hy2 : Constructible y2) (hr2sq : Constructible r2sq)
    (h_circle1 : (x - x1) ^ 2 + (y - y1) ^ 2 = r1sq)
    (h_circle2 : (x - x2) ^ 2 + (y - y2) ^ 2 = r2sq)
    (h_centers_distinct : x1 ≠ x2 ∨ y1 ≠ y2) :
    Constructible x ∧ Constructible y := by
      -- Let $a = 2(x_2 - x_1)$, $b = 2(y_2 - y_1)$, $c = r_1 ^ 2 - r_2 ^ 2 - x_1 ^ 2 + x_2 ^ 2 - y_1 ^ 2 + y_2 ^ 2$. Since $x_1, y_1, r_1 ^ 2, x_2, y_2, r_2 ^ 2$ are constructible, $a, b, c$ are constructible.
      set a := 2 * (x2 - x1)
      set b := 2 * (y2 - y1)
      set c := r1sq - r2sq - x1 ^ 2 + x2 ^ 2 - y1 ^ 2 + y2 ^ 2
      -- Since $x_1, y_1, r_1 ^ 2, x_2, y_2, r_2 ^ 2$ are constructible, $a, b, c$ are constructible.
      have ha : Constructible a := by
        apply_rules [ Constructible.mul, Constructible.neg, Constructible.rat ]
        simpa using Constructible.add hx2 ( Constructible.neg hx1 )
      have hb : Constructible b := by
        apply_rules [ Constructible.mul, Constructible.neg, Constructible.add, Constructible.rat, hx1, hy1, hx2, hy2 ]
      have hc : Constructible c := by
        -- Since $x_1, y_1, r_1 ^ 2, x_2, y_2, r_2 ^ 2$ are constructible, their squares and differences are also constructible.
        have hx1_sq : Constructible (x1 ^ 2) := by
          simpa only [ sq ] using hx1.mul hx1
        have hy1_sq : Constructible (y1 ^ 2) := by
          simpa only [ sq ] using Constructible.mul hy1 hy1
        have hx2_sq : Constructible (x2 ^ 2) := by
          simpa only [ sq ] using Constructible.mul hx2 hx2
        have hy2_sq : Constructible (y2 ^ 2) := by
          simpa only [ sq ] using Constructible.mul hy2 hy2
        -- Since the sum and difference of constructible numbers are constructible, we can combine these to show that $c$ is constructible.
        have hc : Constructible (r1sq - r2sq) ∧ Constructible (-x1 ^ 2 + x2 ^ 2 - y1 ^ 2 + y2 ^ 2) := by
          constructor
          · simpa using Constructible.add hr1sq ( Constructible.neg hr2sq )
          · apply_rules [ Constructible.add, Constructible.neg ]
        convert hc.1.add hc.2 using 1 ; ring
      -- By `Constructible.coords_of_line_circle_inter`, $x$ and $y$ are constructible.
      apply Constructible.coords_of_line_circle_inter ha hb hc hx1 hy1 hr1sq
      · linear_combination h_circle1 - h_circle2
      · exact h_circle1
      · grind
set_option maxHeartbeats 8000000 in
-- The induction over ruler-compass constructions uses many generated algebraic cases.
/-
If a point is constructible, its coordinates are constructible numbers.
-/
lemma RulerCompass.RC_coords_constructible (cfg : RCBase) (P : Point) (h : RCPoint cfg P) :
    IsConstructibleCoords cfg P := by
      induction h
      · constructor
        · simp +decide [ RulerCompass.RulerCompass.RC_coords ]
          simpa using Constructible.rat 0
        · unfold RulerCompass.RulerCompass.RC_coords
          simp_all only [sub_self, Fin.isValue, PiLp.zero_apply]
          simpa using Constructible.rat 0
      · constructor
        · convert Constructible.rat 1
          unfold RulerCompass.RulerCompass.RC_coords
          simp_all only [Fin.isValue, PiLp.sub_apply, Rat.cast_one]
          have hunit := cfg.unit
          norm_num [dist_eq_norm, EuclideanSpace.norm_eq] at hunit
          norm_num [Fin.sum_univ_two, inner]
          nlinarith
        · convert Constructible.rat 0
          unfold RulerCompass.RulerCompass.RC_coords; norm_num
          norm_num [ Fin.sum_univ_succ, inner_sub_left, inner_sub_right ] ; ring_nf
          norm_num [Fin.sum_univ_two, inner]
          ring
      · aesop (config := {warnOnNonterminal := false})
        apply RulerCompass.line_line_coords_constructible hA_ih hB_ih hC_ih hD_ih hAB hCD hLines hP₁ hP₂
      · unfold RulerCompass.IsConstructibleCoords
        aesop (config := {warnOnNonterminal := false})
        · have hP₁_const : ∃ a b c : ℝ, Constructible a ∧ Constructible b ∧ Constructible c ∧ a * (RulerCompass.RC_coords cfg P_1).1 + b * (RulerCompass.RC_coords cfg P_1).2 = c ∧ (a ≠ 0 ∨ b ≠ 0) := by
            use (RulerCompass.RC_coords cfg A).2 - (RulerCompass.RC_coords cfg B).2, (RulerCompass.RC_coords cfg B).1 - (RulerCompass.RC_coords cfg A).1, (RulerCompass.RC_coords cfg B).1 * (RulerCompass.RC_coords cfg A).2 - (RulerCompass.RC_coords cfg B).2 * (RulerCompass.RC_coords cfg A).1
            simp_all only [ne_eq]
            apply And.intro
            · exact Constructible.add ( hA_ih.2 ) ( Constructible.neg hB_ih.2 )
            · apply And.intro
              · exact Constructible.add ( hB_ih.1 ) ( Constructible.neg ( hA_ih.1 ) )
              · apply And.intro
                · exact Constructible.add ( Constructible.mul hB_ih.1 hA_ih.2 ) ( Constructible.neg ( Constructible.mul hB_ih.2 hA_ih.1 ) )
                · apply And.intro
                  · unfold RulerCompass.RulerCompass.RC_coords; ring_nf
                    simp +decide [ Fin.sum_univ_two, inner ] ; ring_nf
                    rw [ show P_1 = ( 1 - hP₁.choose ) • A + hP₁.choose • B by simpa using hP₁.choose_spec ] ; norm_num ; ring
                  · unfold RulerCompass.RulerCompass.RC_coords
                    contrapose! hAB; simp_all ( config := { decide := Bool.true } ) [ sub_eq_iff_eq_add ]
                    have h_det_nonzero : (cfg.E 0 - cfg.O 0) ^ 2 + (cfg.E 1 - cfg.O 1) ^ 2 ≠ 0 := by
                      have := cfg.unit
                      norm_num [dist_eq_norm, EuclideanSpace.norm_eq] at this
                      nlinarith
                    have hunit := cfg.unit
                    norm_num [dist_eq_norm, EuclideanSpace.norm_eq] at hunit
                    obtain ⟨hperp, hpar⟩ := hAB
                    simp [Fin.sum_univ_two, inner, PiLp.sub_apply] at hperp hpar
                    ring_nf at hperp hpar hunit
                    have hdet_eq :
                        (cfg.E 0 - cfg.O 0) ^ 2 + (cfg.E 1 - cfg.O 1) ^ 2 = 1 := by
                      nlinarith
                    ext i
                    · fin_cases i
                      · have hdx :
                            (A 0 - B 0) *
                              ((cfg.E 0 - cfg.O 0) ^ 2 + (cfg.E 1 - cfg.O 1) ^ 2) = 0 := by
                          linear_combination
                            (-(cfg.E 0 - cfg.O 0)) * hpar - (cfg.E 1 - cfg.O 1) * hperp
                        rw [hdet_eq] at hdx
                        norm_num at hdx
                        exact sub_eq_zero.mp hdx
                      · have hdy :
                            (A 1 - B 1) *
                              ((cfg.E 0 - cfg.O 0) ^ 2 + (cfg.E 1 - cfg.O 1) ^ 2) = 0 := by
                          linear_combination
                            (-(cfg.E 1 - cfg.O 1)) * hpar + (cfg.E 0 - cfg.O 0) * hperp
                        rw [hdet_eq] at hdy
                        norm_num at hdy
                        exact sub_eq_zero.mp hdy
          have hP₂_const : ∃ x0 y0 r2 : ℝ, Constructible x0 ∧ Constructible y0 ∧ Constructible r2 ∧ ((RulerCompass.RulerCompass.RC_coords cfg P_1).1 - x0) ^ 2 + ((RulerCompass.RulerCompass.RC_coords cfg P_1).2 - y0) ^ 2 = r2 := by
            use (RulerCompass.RulerCompass.RC_coords cfg C).1, (RulerCompass.RulerCompass.RC_coords cfg C).2, ((RulerCompass.RulerCompass.RC_coords cfg C).1 - (RulerCompass.RulerCompass.RC_coords cfg D).1) ^ 2 + ((RulerCompass.RulerCompass.RC_coords cfg C).2 - (RulerCompass.RulerCompass.RC_coords cfg D).2) ^ 2
            simp +zetaDelta at *
            refine ⟨ hC_ih.1, hC_ih.2, ?_, ?_ ⟩
            · -- The square of a constructible number is constructible.
              have h_sq : ∀ x : ℝ, Constructible x → Constructible (x ^ 2) := by
                exact fun x hx => by simpa only [ sq ] using Constructible.mul hx hx
              -- The difference of two constructible numbers is constructible.
              have h_diff : ∀ x y : ℝ, Constructible x → Constructible y → Constructible (x - y) := by
                intros x y hx hy
                simpa using Constructible.add hx ( Constructible.neg hy )
              exact Constructible.add ( h_sq _ ( h_diff _ _ hC_ih.1 hD_ih.1 ) ) ( h_sq _ ( h_diff _ _ hC_ih.2 hD_ih.2 ) )
            · field_simp
              rw [ ← RulerCompass.dist_sq_eq_coords_sq_add_sq ]
              exact hP₂.symm ▸ by rw [ ← RulerCompass.dist_sq_eq_coords_sq_add_sq ]
          obtain ⟨ a, b, c, ha, hb, hc, h₁, h₂ ⟩ := hP₁_const; obtain ⟨ x0, y0, r2, hx0, hy0, hr2, h₃ ⟩ := hP₂_const; exact Constructible.coords_of_line_circle_inter ha hb hc hx0 hy0 hr2 h₁ h₃ h₂ |>.1
        · unfold RulerCompass.RulerCompass.IsConstructibleCoords at *
          have h_line : ∃ a b c : ℝ, Constructible a ∧ Constructible b ∧ Constructible c ∧ a * (RulerCompass.RulerCompass.RC_coords cfg P_1).1 + b * (RulerCompass.RulerCompass.RC_coords cfg P_1).2 = c ∧ (a ≠ 0 ∨ b ≠ 0) := by
            use (RulerCompass.RulerCompass.RC_coords cfg A).2 - (RulerCompass.RulerCompass.RC_coords cfg B).2, (RulerCompass.RulerCompass.RC_coords cfg B).1 - (RulerCompass.RulerCompass.RC_coords cfg A).1, (RulerCompass.RulerCompass.RC_coords cfg B).1 * (RulerCompass.RulerCompass.RC_coords cfg A).2 - (RulerCompass.RulerCompass.RC_coords cfg A).1 * (RulerCompass.RulerCompass.RC_coords cfg B).2
            refine ⟨ ?_, ?_, ?_, ?_, ?_ ⟩
            · exact Constructible.add ( hA_ih.2 ) ( Constructible.neg hB_ih.2 )
            · exact Constructible.add ( hB_ih.1 ) ( Constructible.neg ( hA_ih.1 ) )
            · exact Constructible.add ( Constructible.mul hB_ih.1 hA_ih.2 ) ( Constructible.neg ( Constructible.mul hA_ih.1 hB_ih.2 ) )
            · convert RulerCompass.line_equation hP₁ using 1 ; ring
            · contrapose! hAB
              unfold RulerCompass.RulerCompass.RC_coords at *
              simp_all +decide [ sub_eq_iff_eq_add, Fin.forall_fin_two, funext_iff ]
              obtain ⟨left, right⟩ := hC_ih
              obtain ⟨left_1, right_1⟩ := hD_ih
              obtain ⟨left_2, right_2⟩ := hAB
              -- Since the determinant is non-zero, the only solution to the system is A 0 = B 0 and A 1 = B 1.
              have h_det_nonzero : (cfg.E 0 - cfg.O 0) ^ 2 + (cfg.E 1 - cfg.O 1) ^ 2 ≠ 0 := by
                have := cfg.unit
                norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] at this
                linarith
              have hunit := cfg.unit
              norm_num [dist_eq_norm, EuclideanSpace.norm_eq] at hunit
              simp_all only [Fin.isValue, ne_eq]
              simp [Fin.sum_univ_two, inner, PiLp.sub_apply] at left_2 right_2
              ring_nf at left_2 right_2 hunit
              have hdet_eq :
                  (cfg.E 0 - cfg.O 0) ^ 2 + (cfg.E 1 - cfg.O 1) ^ 2 = 1 := by
                nlinarith
              ext i
              · fin_cases i
                · have hdx :
                      (A 0 - B 0) *
                        ((cfg.E 0 - cfg.O 0) ^ 2 + (cfg.E 1 - cfg.O 1) ^ 2) = 0 := by
                    linear_combination
                      (-(cfg.E 0 - cfg.O 0)) * right_2 - (cfg.E 1 - cfg.O 1) * left_2
                  rw [hdet_eq] at hdx
                  norm_num at hdx
                  exact sub_eq_zero.mp hdx
                · have hdy :
                      (A 1 - B 1) *
                        ((cfg.E 0 - cfg.O 0) ^ 2 + (cfg.E 1 - cfg.O 1) ^ 2) = 0 := by
                    linear_combination
                      (-(cfg.E 1 - cfg.O 1)) * right_2 + (cfg.E 0 - cfg.O 0) * left_2
                  rw [hdet_eq] at hdy
                  norm_num at hdy
                  exact sub_eq_zero.mp hdy
          have h_circle : ∃ x0 y0 r2 : ℝ, Constructible x0 ∧ Constructible y0 ∧ Constructible r2 ∧ ((RulerCompass.RulerCompass.RC_coords cfg P_1).1 - x0) ^ 2 + ((RulerCompass.RulerCompass.RC_coords cfg P_1).2 - y0) ^ 2 = r2 := by
            use (RulerCompass.RulerCompass.RC_coords cfg C).1, (RulerCompass.RulerCompass.RC_coords cfg C).2, ((RulerCompass.RulerCompass.RC_coords cfg D).1 - (RulerCompass.RulerCompass.RC_coords cfg C).1) ^ 2 + ((RulerCompass.RulerCompass.RC_coords cfg D).2 - (RulerCompass.RulerCompass.RC_coords cfg C).2) ^ 2
            simp_all only [↓existsAndEq, ne_eq, true_and, exists_and_left]
            obtain ⟨left, right⟩ := hA_ih
            obtain ⟨left_1, right_1⟩ := hB_ih
            obtain ⟨left_2, right_2⟩ := hC_ih
            obtain ⟨left_3, right_3⟩ := hD_ih
            obtain ⟨w, h⟩ := h_line
            obtain ⟨left_4, right_4⟩ := h
            obtain ⟨w_1, h⟩ := right_4
            obtain ⟨left_5, right_4⟩ := h
            obtain ⟨left_6, right_4⟩ := right_4
            cases right_4 with
            | inl h =>
              apply And.intro
              · have h_diff : Constructible ((RulerCompass.RulerCompass.RC_coords cfg D).1 - (RulerCompass.RulerCompass.RC_coords cfg C).1) ∧ Constructible ((RulerCompass.RulerCompass.RC_coords cfg D).2 - (RulerCompass.RulerCompass.RC_coords cfg C).2) := by
                  exact ⟨ by exact Constructible.add left_3 ( Constructible.neg left_2 ), by exact Constructible.add right_3 ( Constructible.neg right_2 ) ⟩
                have h_sq : Constructible ((RulerCompass.RulerCompass.RC_coords cfg D).1 - (RulerCompass.RulerCompass.RC_coords cfg C).1) ∧ Constructible ((RulerCompass.RulerCompass.RC_coords cfg D).2 - (RulerCompass.RulerCompass.RC_coords cfg C).2) → Constructible (((RulerCompass.RulerCompass.RC_coords cfg D).1 - (RulerCompass.RulerCompass.RC_coords cfg C).1) ^ 2 + ((RulerCompass.RulerCompass.RC_coords cfg D).2 - (RulerCompass.RulerCompass.RC_coords cfg C).2) ^ 2) := by
                  exact fun h => by simpa only [ sq ] using Constructible.add ( Constructible.mul h.1 h.1 ) ( Constructible.mul h.2 h.2 )
                exact h_sq h_diff
              · unfold RulerCompass.RulerCompass.RC_coords at *
                norm_num [ EuclideanSpace.dist_eq ] at *
                unfold RulerCompass.circleThrough at hP₂
                unfold RulerCompass.circle at hP₂
                simp_all only [Set.mem_setOf_eq, Fin.isValue]
                norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] at *
                rw [ Real.sqrt_inj ( by positivity ) ( by positivity ) ] at hP₂
                norm_num [ Fin.sum_univ_two, inner ] at *
                grind +ring
            | inr h_1 =>
              apply And.intro
              · have h_diff : ∀ {x y : ℝ}, Constructible x → Constructible y → Constructible (x - y) := by
                  intro x y hx hy; exact (by
                  simpa using Constructible.add hx ( Constructible.neg hy ))
                have h_sq : ∀ {x : ℝ}, Constructible x → Constructible (x ^ 2) := by
                  intro x hx; exact (by
                  simpa only [ sq ] using Constructible.mul hx hx)
                exact Constructible.add ( h_sq ( h_diff left_3 left_2 ) ) ( h_sq ( h_diff right_3 right_2 ) )
              · have h_dist_eq : (dist P_1 C) ^ 2 = (dist D C) ^ 2 := by
                  unfold RulerCompass.circleThrough at hP₂
                  simp_all only [dist_nonneg, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_left_inj₀]
                  exact hP₂.trans ( dist_comm _ _ )
                convert h_dist_eq using 1
                · field_simp
                  norm_num +zetaDelta at *
                  rw [ RulerCompass.dist_sq_eq_coords_sq_add_sq ]
                · rw [ ← RulerCompass.dist_sq_eq_coords_sq_add_sq ]
          obtain ⟨ a, b, c, ha, hb, hc, h₁, h₂ ⟩ := h_line
          obtain ⟨ x0, y0, r2, hx0, hy0, hr2, h ⟩ := h_circle
          have := Constructible.coords_of_line_circle_inter ha hb hc hx0 hy0 hr2 h₁ h
          exact this h₂ |>.2
      · rename_i A B C D P hA hB hC hD hAB hCD hCircles hP₁ hP₂ hA_ih hB_ih hC_ih hD_ih
        -- By definition of `RC_coords`, we know that `(RC_coords A).1`, `(RC_coords A).2`, `(RC_coords B).1`, `(RC_coords B).2`, `(RC_coords C).1`, `(RC_coords C).2`, `(RC_coords D).1`, and `(RC_coords D).2` are constructible.
        obtain ⟨hx_A, hy_A⟩ := hA_ih
        obtain ⟨hx_B, hy_B⟩ := hB_ih
        obtain ⟨hx_C, hy_C⟩ := hC_ih
        obtain ⟨hx_D, hy_D⟩ := hD_ih
        -- By definition of `RC_coords`, we know that `(RC_coords P).1` and `(RC_coords P).2` satisfy the equations of the circles.
        have hP₁_eq : ( (RC_coords cfg P).1 - (RC_coords cfg A).1 ) ^ 2 + ( (RC_coords cfg P).2 - (RC_coords cfg A).2 ) ^ 2 = ( dist A B ) ^ 2 := by
          convert RulerCompass.dist_sq_eq_coords_sq_add_sq cfg P A using 1
          · simp +zetaDelta at *
            rw [ ← RulerCompass.dist_sq_eq_coords_sq_add_sq ]
          · convert RulerCompass.dist_sq_eq_coords_sq_add_sq cfg P A using 1
            rw [ hP₁.symm ]
        have hP₂_eq : ( (RC_coords cfg P).1 - (RC_coords cfg C).1 ) ^ 2 + ( (RC_coords cfg P).2 - (RC_coords cfg C).2 ) ^ 2 = ( dist C D ) ^ 2 := by
          have := RulerCompass.dist_sq_eq_coords_sq_add_sq cfg P C
          rw [ ← this, ← hP₂ ]
        -- By definition of `RC_coords`, we know that `(RC_coords P).1` and `(RC_coords P).2` satisfy the equations of the circles, and thus are constructible.
        have hP₁_constr : Constructible (dist A B ^ 2) := by
          -- The sum of squares of constructible numbers is constructible.
          have h_sum_squares_constr : ∀ (x y : ℝ), Constructible x → Constructible y → Constructible (x ^ 2 + y ^ 2) := by
            intros x y hx hy
            have h_sum_squares_constr : ∀ (x y : ℝ), Constructible x → Constructible y → Constructible (x ^ 2) ∧ Constructible (y ^ 2) := by
              exact fun x y hx hy => ⟨ by simpa only [ sq ] using Constructible.mul hx hx, by simpa only [ sq ] using Constructible.mul hy hy ⟩
            exact Constructible.add ( h_sum_squares_constr x y hx hy |>.1 ) ( h_sum_squares_constr x y hx hy |>.2 )
          convert h_sum_squares_constr ( ( RulerCompass.RulerCompass.RC_coords cfg A |>.1 ) - ( RulerCompass.RulerCompass.RC_coords cfg B |>.1 ) ) ( ( RulerCompass.RulerCompass.RC_coords cfg A |>.2 ) - ( RulerCompass.RulerCompass.RC_coords cfg B |>.2 ) ) _ _ using 1
          · convert dist_sq_eq_coords_sq_add_sq cfg A B using 1
          · exact Constructible.add hx_A ( Constructible.neg hx_B )
          · exact Constructible.add hy_A ( Constructible.neg hy_B )
        have hP₂_constr : Constructible (dist C D ^ 2) := by
          -- By definition of `dist`, we know that `dist C D ^ 2` is constructible.
          have h_dist_sq : Constructible ((dist C D) ^ 2) := by
            have h_dist_sq_eq : (dist C D) ^ 2 = ((RC_coords cfg C).1 - (RC_coords cfg D).1) ^ 2 + ((RC_coords cfg C).2 - (RC_coords cfg D).2) ^ 2 := by
              norm_num +zetaDelta at *
              rw [ RulerCompass.dist_sq_eq_coords_sq_add_sq ]
            rw [h_dist_sq_eq]
            apply_rules [ Constructible.add, Constructible.mul, Constructible.neg, Constructible.sqrt ]
            · exact Constructible.rat 1 |> fun h => by simpa using h
            · exact Constructible.rat 1 |> fun h => by simpa using h
          exact h_dist_sq
        have hP₁_constr : Constructible (RC_coords cfg P).1 ∧ Constructible (RC_coords cfg P).2 := by
          apply Constructible.coords_of_circle_circle_inter hx_A hy_A hP₁_constr hx_C hy_C hP₂_constr hP₁_eq hP₂_eq
          contrapose! hCircles
          unfold RulerCompass.RulerCompass.RC_coords at *
          simp_all only [ne_eq, Fin.isValue, PiLp.sub_apply, neg_sub, dist_nonneg, OfNat.ofNat_ne_zero,
            not_false_eq_true, pow_left_inj₀]
          obtain ⟨left, right⟩ := hCircles
          unfold RulerCompass.circleThrough
          simp_all only [Fin.isValue]
          simp_all ( config := { decide := Bool.true } ) [ dist_eq_norm, EuclideanSpace.norm_eq ]
          simp_all ( config := { decide := Bool.true } ) [ Real.sqrt_inj ( add_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) ) ( add_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) ), inner ]
          -- Since the coordinates of A and C are the same, we have A = C.
          have hA_eq_C : A = C := by
            have hunit := cfg.unit
            norm_num [dist_eq_norm, EuclideanSpace.norm_eq] at hunit
            ring_nf at left right
            ring_nf at hunit
            have hdet_eq :
                (cfg.E 0 - cfg.O 0) ^ 2 + (cfg.E 1 - cfg.O 1) ^ 2 = 1 := by
              nlinarith
            apply PiLp.ext
            intro i
            fin_cases i
            · have hdx :
                  (A 0 - C 0) *
                    ((cfg.E 0 - cfg.O 0) ^ 2 + (cfg.E 1 - cfg.O 1) ^ 2) = 0 := by
                linear_combination
                  (cfg.E 0 - cfg.O 0) * left + (cfg.O 1 - cfg.E 1) * right
              rw [hdet_eq] at hdx
              norm_num at hdx
              exact sub_eq_zero.mp hdx
            · have hdy :
                  (A 1 - C 1) *
                    ((cfg.E 0 - cfg.O 0) ^ 2 + (cfg.E 1 - cfg.O 1) ^ 2) = 0 := by
                linear_combination
                  (cfg.E 1 - cfg.O 1) * left + (cfg.E 0 - cfg.O 0) * right
              rw [hdet_eq] at hdy
              norm_num at hdy
              exact sub_eq_zero.mp hdy
          rw [ hA_eq_C ]
        exact hP₁_constr
/-
If a point P is constructible, then the length of the segment OP is a constructible number.
-/
lemma RulerCompass.RC_length_constructible (cfg : RCBase) (P : Point) (h : RCPoint cfg P) :
    Constructible (segmentLength cfg P) := by
      have := RulerCompass.RC_coords_constructible cfg P h
      -- By definition of `segmentLength`, we have `segmentLength cfg P = Real.sqrt ((RulerCompass.RC_coords cfg P).1 ^ 2 + (RulerCompass.RC_coords cfg P).2 ^ 2)`.
      have h_segmentLength : RulerCompass.segmentLength cfg P = Real.sqrt ((RulerCompass.RC_coords cfg P).1 ^ 2 + (RulerCompass.RC_coords cfg P).2 ^ 2) := by
        unfold RulerCompass.segmentLength
        convert ( RulerCompass.dist_sq_eq_coords_sq_add_sq cfg cfg.O P ) |> congr_arg Real.sqrt using 1
        · rw [ Real.sqrt_sq ( dist_nonneg ) ]
        · unfold RulerCompass.RulerCompass.RC_coords
          norm_num
      obtain ⟨ h₁, h₂ ⟩ := this
      convert Constructible.sqrt ( h₁.mul h₁ |> Constructible.add <| h₂.mul h₂ ) _
      · rw [ h_segmentLength, sq, sq ]
      · nlinarith
end AristotleLemmas
/- **Doubling the cube is impossible (geometric version)**: starting from a
unit segment `OE`, there is no ruler-and-compass construction that produces a
point `P` such that the length `OP` satisfies `OP ^ 3 = 2`. -/
theorem doubling_the_cube_impossible_plane (cfg : RCBase) :
    ¬ ∃ P : Point, RCPoint cfg P ∧ (segmentLength cfg P) ^ 3 = (2 : ℝ) := by
  rintro ⟨P, hP, hcube⟩
  exact doubling_the_cube_impossible
    ⟨segmentLength cfg P, hcube, RulerCompass.RC_length_constructible cfg P hP⟩
/-- **Angle trisection is impossible (geometric version)**: it is *not* the case
that for every constructible angle `θ`, the angle `θ / 3` is also constructible. -/
theorem angle_trisection_impossible_plane (cfg : RCBase) :
    ¬ (∀ θ : ℝ,
          RCConstructibleAngle cfg θ →
          RCConstructibleAngle cfg (θ / 3)) := by
  intro h
  obtain ⟨P, hP⟩ : ∃ P : Point, RCPoint cfg P ∧ Real.cos (baseAngle cfg P) = Real.cos (Real.pi / 9) := by
    have hP : ∃ P : Point, RulerCompass.RCPoint cfg P ∧ RulerCompass.baseAngle cfg P = Real.pi / 3 := by
      -- Let's choose the point $P$ such that $OP = 1$ and $\angle POE = 60 ^ \circ$.
      obtain ⟨P, hP⟩ : ∃ P : Point, RulerCompass.RCPoint cfg P ∧ (dist (RulerCompass.RCBase.O cfg) P) = 1 ∧ (dist (RulerCompass.RCBase.E cfg) P) = 1 := by
        -- Let's choose the point $P$ as the intersection of the circles $circleThrough cfg.O cfg.E$ and $circleThrough cfg.E cfg.O$.
        obtain ⟨P, hP⟩ : ∃ P : Point, P ∈ RulerCompass.circleThrough cfg.O cfg.E ∧ P ∈ RulerCompass.circleThrough cfg.E cfg.O := by
          unfold RulerCompass.circleThrough
          unfold RulerCompass.circle
          norm_num [ Real.dist_eq, EuclideanSpace.dist_eq ]
          -- Let's choose the point $P$ such that $P = O + (E - O) \cdot \frac{1}{2} + (E - O) \cdot \frac{\sqrt{3}}{2} \cdot i$.
          simp_all only [Fin.isValue]
          let u : Point := cfg.E - cfg.O
          let v : Point := EuclideanSpace.single (0 : Fin 2) (-(u (1 : Fin 2))) +
            EuclideanSpace.single (1 : Fin 2) (u (0 : Fin 2))
          use cfg.O + (2⁻¹ : ℝ) • u + (Real.sqrt 3 / 2) • v
          have hunit : (cfg.E 0 - cfg.O 0) ^ 2 + (cfg.E 1 - cfg.O 1) ^ 2 = 1 := by
            have := cfg.unit
            norm_num [u, dist_eq_norm, EuclideanSpace.norm_eq] at this
            ring_nf at this
            ring_nf
            nlinarith
          constructor
          · norm_num [u, v, dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two]
            rw [Real.sqrt_inj (by positivity) (by positivity)]
            ring_nf
            nlinarith [Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
          · norm_num [u, v, dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two]
            rw [Real.sqrt_inj (by positivity) (by positivity)]
            ring_nf
            nlinarith [Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
        use P
        aesop (config := {warnOnNonterminal := false})
        · -- By definition of $P$, we know that $P$ is the intersection of the circles centered at $O$ and $E$ with radius $OE$.
          have hP : RulerCompass.RCPoint cfg P := by
            have h_circle_O : RulerCompass.RCPoint cfg cfg.O := by
              exact RulerCompass.RCPoint.base_O
            have h_circle_E : RulerCompass.RCPoint cfg cfg.E := by
              exact RulerCompass.RCPoint.base_E
            apply RulerCompass.RCPoint.circle_circle h_circle_O h_circle_E h_circle_E h_circle_O
            · exact cfg.hOE
            · exact cfg.hOE.symm
            · unfold RulerCompass.circleThrough
              unfold RulerCompass.circle; aesop (config := {warnOnNonterminal := false})
              rw [ Set.ext_iff ] at a ; specialize a cfg.O ; aesop (config := {warnOnNonterminal := false})
              exact cfg.hOE ( a.mpr ( dist_comm _ _ ) )
            · assumption
            · assumption
          exact hP
        · rw [ dist_comm, left, cfg.unit ]
        · unfold RulerCompass.circleThrough at *
          unfold RulerCompass.circle at * ; aesop (config := {warnOnNonterminal := false})
          simp_all +decide [ dist_comm ]
          exact cfg.unit
      use P
      aesop (config := {warnOnNonterminal := false})
      -- Since $OP = OE = EP = 1$, triangle $OPE$ is equilateral, and thus $\angle POE = 60 ^ \circ$.
      have h_eq : dist cfg.O P = 1 ∧ dist cfg.E P = 1 ∧ dist cfg.O cfg.E = 1 := by
        exact ⟨ left_1, right, cfg.unit ⟩
      -- Since $OP = OE = EP = 1$, triangle $OPE$ is equilateral, and thus $\angle POE = 60 ^ \circ$ by definition of equilateral triangles.
      have h_eq_triangle : EuclideanGeometry.angle cfg.E cfg.O P = Real.arccos ((dist cfg.O cfg.E ^ 2 + dist cfg.O P ^ 2 - dist cfg.E P ^ 2) / (2 * dist cfg.O cfg.E * dist cfg.O P)) := by
        rw [ EuclideanGeometry.angle, dist_eq_norm, dist_eq_norm, dist_eq_norm ]
        rw [ InnerProductGeometry.angle ]
        norm_num [ EuclideanSpace.norm_eq, dist_eq_norm ]
        norm_num [ Real.sq_sqrt ( add_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) ), inner ] ; ring_nf
      aesop (config := {warnOnNonterminal := false})
      exact h_eq_triangle.trans ( by rw [ show ( 2⁻¹ : ℝ ) = Real.cos ( Real.pi / 3 ) by norm_num, Real.arccos_cos ] <;> linarith [ Real.pi_pos ] )
    obtain ⟨ P, hP₁, hP₂ ⟩ := hP
    obtain ⟨ Q, hQ₁, hQ₂ ⟩ := h ( Real.pi / 3 ) ⟨ P, hP₁, hP₂ ⟩
    exact ⟨ Q, hQ₁, by rw [ hQ₂ ] ; ring_nf ⟩
  -- By the lemma, $2 \cos(\pi / 9)$ is constructible.
  have h_two_cos_pi_div_nine : Constructible (2 * Real.cos (Real.pi / 9)) := by
    -- The distance from O to P is constructible, and since the unit distance is 1, the coordinates of P are constructible.
    have h_dist_O_P : Constructible (dist (RulerCompass.RCBase.O cfg) P) := by
      apply RulerCompass.RC_length_constructible cfg P hP.1
    -- The x-coordinate of P in the coordinate system defined by O and E is constructible.
    have h_x_coord : Constructible (inner (𝕜 := ℝ) (cfg.E - cfg.O) (P - cfg.O)) := by
      have := RulerCompass.RC_coords_constructible cfg P hP.1
      simpa [RulerCompass.RC_coords] using this.1
    -- Since the inner product of (P - O) and (E - O) is equal to the distance from O to P times the cosine of the angle between them, we can write:
    have h_cos_eq : inner (𝕜 := ℝ) (cfg.E - cfg.O) (P - cfg.O) = (dist (RulerCompass.RCBase.O cfg) P) * Real.cos (baseAngle cfg P) := by
      unfold RulerCompass.baseAngle; simp +decide [ dist_eq_norm, EuclideanGeometry.angle ]
      rw [ InnerProductGeometry.cos_angle ] ; ring_nf ; aesop (config := {warnOnNonterminal := false})
      simp +decide [ norm_sub_rev, mul_assoc, mul_comm, mul_left_comm ]
      by_cases h : ‖P - cfg.O‖ = 0 <;> by_cases h' : ‖cfg.O - cfg.E‖ = 0 <;> simp_all +decide [ sub_eq_zero ]
      rw [ show ‖cfg.O - cfg.E‖ = 1 by simpa [ dist_eq_norm ] using cfg.unit ] ; ring
    have h_cos_eq : Constructible (Real.cos (RulerCompass.baseAngle cfg P)) := by
      have h_cos_eq : Constructible ((dist (RulerCompass.RCBase.O cfg) P) * Real.cos (baseAngle cfg P)) := by
        exact h_cos_eq ▸ h_x_coord
      have h_cos_eq : Constructible ((dist (RulerCompass.RCBase.O cfg) P)⁻¹ * ((dist (RulerCompass.RCBase.O cfg) P) * Real.cos (baseAngle cfg P))) := by
        apply_rules [ Constructible.mul, Constructible.inv ]
        aesop (config := {warnOnNonterminal := false})
        unfold RulerCompass.baseAngle at right ; norm_num at right
        exact ne_of_lt ( Real.cos_pos_of_mem_Ioo ⟨ by linarith [ Real.pi_pos ], by linarith [ Real.pi_pos ] ⟩ ) right
      by_cases h : Dist.dist cfg.O P = 0 <;> aesop (config := {warnOnNonterminal := false})
      unfold RulerCompass.baseAngle at right ; aesop (config := {warnOnNonterminal := false})
    aesop (config := {warnOnNonterminal := false})
    exact Constructible.mul ( Constructible.rat 2 ) h_cos_eq
  -- By the lemma, $2 \cos(\pi / 9)$ is a root of the polynomial $X ^ 3 - 3X - 1$.
  have h_root : Polynomial.eval (2 * Real.cos (Real.pi / 9)) (Polynomial.X ^ 3 - 3 * Polynomial.X - 1 : Polynomial ℝ) = 0 := by
    have := Real.cos_three_mul ( Real.pi / 9 ) ; ring_nf at *; norm_num [ mul_div ] at *; linarith
  -- Since $X ^ 3 - 3X - 1$ is irreducible over the rationals, $2 \cos(\pi / 9)$ cannot be constructible.
  have h_irreducible : Irreducible (Polynomial.X ^ 3 - 3 * Polynomial.X - 1 : Polynomial ℚ) := by
    exact trisection_poly_irreducible
  -- Since $X ^ 3 - 3X - 1$ is irreducible over the rationals, $2 \cos(\pi / 9)$ cannot be constructible, contradicting our assumption.
  have h_contradiction : ∀ {x : ℝ}, Constructible x → Polynomial.eval x (Polynomial.X ^ 3 - 3 * Polynomial.X - 1 : Polynomial ℝ) = 0 → False := by
    intros x hx h_root
    have h_deg : Module.finrank ℚ (IntermediateField.adjoin ℚ {x}) = 3 := by
      have h_deg : minpoly ℚ x = Polynomial.X ^ 3 - 3 * Polynomial.X - 1 := by
        refine Eq.symm ( minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_ )
        · exact h_irreducible
        · simp_all only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul,
            Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.aeval_sub, map_pow, Polynomial.aeval_X, map_mul, map_one]
          obtain ⟨left, right⟩ := hP
          erw [ Polynomial.aeval_C ] ; norm_num ; linarith
        · erw [ Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> erw [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> norm_num
          norm_num [ Polynomial.coeff_one, Polynomial.coeff_X ]
      rw [ IntermediateField.adjoin.finrank ]
      · erw [ h_deg, Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> erw [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> norm_num
      · exact ⟨ Polynomial.X ^ 3 - 3 * Polynomial.X - 1, by exact Polynomial.Monic.def.mpr <| by erw [ Polynomial.leadingCoeff ] ; erw [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> erw [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> norm_num [ Polynomial.coeff_one, Polynomial.coeff_X ], by aesop ⟩
    have := degree_of_constructible x hx
    rcases this with ⟨ n, hn ⟩ ; linarith [ Nat.pow_le_pow_right ( show 1 ≤ 2 by norm_num ) ( show n ≥ 2 by contrapose! hn; interval_cases n <;> linarith ) ]
  exact h_contradiction h_two_cos_pi_div_nine h_root
/-- Freek Wiedijk’s theorem 8, in a geometric formulation: the impossibility of
trisecting the angle and doubling the cube by ruler-and-compass constructions
in the Euclidean plane. -/
theorem freek_08_plane (cfg : RCBase) :
    (¬ (∀ θ : ℝ,
          RCConstructibleAngle cfg θ →
          RCConstructibleAngle cfg (θ / 3))) ∧
    (¬ ∃ P : Point, RCPoint cfg P ∧ (segmentLength cfg P) ^ 3 = (2 : ℝ)) := by
  exact ⟨ angle_trisection_impossible_plane cfg, fun ⟨ P, hP₁, hP₂ ⟩ ↦ doubling_the_cube_impossible_plane cfg ⟨ P, hP₁, hP₂ ⟩ ⟩
#print axioms freek_08
-- 'Theorem8.freek_08' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms freek_08_plane
-- 'Theorem8.RulerCompass.freek_08_plane' depends on axioms: [propext, Classical.choice, Quot.sound]
end RulerCompass
end
end Theorem8
