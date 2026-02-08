/-

This is a Lean formalization of a solution to Erdős Problem 1071.
https://www.erdosproblems.com/forum/thread/1071

The original proof was found by: Boris Alexeev
(see comment thread above)
(but I doubt this is actually original)


This proof was formalized by Aristotle (from Harmonic), ChatGPT (from
Open AI), and the original human author.


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


/-
We have proved Corollary 3, establishing the existence of a countable maximal disjoint collection of unit segments in the closed unit square [0,1] x [0,1]. This was achieved by defining the collection `S_cor3` as the union of `S_cor2` (from Corollary 2) and the four sides of the square, and proving that this collection is disjoint, contained in the square, and blocking (maximal).
-/

import Mathlib

namespace Erdos1071

set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.refine false
set_option linter.style.induction false
set_option linter.style.cases false
set_option linter.style.multiGoal false

open scoped Classical

set_option maxHeartbeats 0

abbrev Point := EuclideanSpace ℝ (Fin 2)

def IsUnitSegment (s : Set Point) : Prop :=
  ∃ x y : Point, dist x y = 1 ∧ s = openSegment ℝ x y

def IsDisjointCollection (S : Set (Set Point)) : Prop :=
  (∀ s ∈ S, IsUnitSegment s) ∧ (∀ s t, s ∈ S → t ∈ S → s ≠ t → Disjoint s t)

def IsInRegion (S : Set (Set Point)) (R : Set Point) : Prop :=
  ∀ s ∈ S, s ⊆ R

def IsMaximalDisjointCollection (S : Set (Set Point)) (R : Set Point) : Prop :=
  IsDisjointCollection S ∧ IsInRegion S R ∧
  ∀ S', IsDisjointCollection S' → IsInRegion S' R → S ⊆ S' → S = S'

def UnitSquare : Set Point := {p | ∀ i, 0 ≤ p i ∧ p i ≤ 1}

/-
A disjoint collection of unit segments in a region is maximal if and only if every unit segment in the region intersects at least one segment in the collection.
-/
def IsBlocking (S : Set (Set Point)) (R : Set Point) : Prop :=
  ∀ L, IsUnitSegment L → L ⊆ R → ∃ s ∈ S, ¬Disjoint s L

theorem maximal_iff_blocking (S : Set (Set Point)) (R : Set Point) (hS : IsDisjointCollection S) (hR : IsInRegion S R) :
  IsMaximalDisjointCollection S R ↔ IsBlocking S R := by
    unfold IsBlocking IsMaximalDisjointCollection;
    constructor;
    · intro hL L hL1 hL2
      by_contra h_contra
      push_neg at h_contra;
      -- Since $L$ is a unit segment in $R$ and is disjoint from all segments in $S$, the collection $S \cup \{L\}$ is a disjoint collection in $R$.
      have h_add_L : IsDisjointCollection (insert L S) := by
        refine' ⟨ _, _ ⟩;
        · exact fun s hs => hs.elim ( fun hs => hs.symm ▸ hL1 ) fun hs => hS.1 s hs;
        · rintro s t ( rfl | hs ) ( rfl | ht ) <;> simp_all +decide [ Set.disjoint_left ];
          · exact fun h x hx hx' => h_contra t ht hx' hx;
          · exact fun h => h_contra s hs;
          · exact fun hst x hx hx' => hL.1.2 s t hs ht hst |> fun h => h.le_bot ⟨ hx, hx' ⟩;
      -- Since $L$ is a unit segment in $R$ and is disjoint from all segments in $S$, the collection $S \cup \{L\}$ is a disjoint collection in $R$ and $S$ is a proper subset of $S \cup \{L\}$.
      have h_add_L_subset : S ⊂ insert L S := by
        simp_all +decide [ Set.ssubset_def, Set.subset_def ];
        intro hL3; specialize h_contra L hL3; rcases hL1 with ⟨ x, hx ⟩ ; simp_all +decide
        obtain ⟨ y, hy1, hy2 ⟩ := hx; rw [ eq_comm ] at hy2; simp_all +decide [ openSegment_eq_image ] ;
        exact Set.Nonempty.ne_empty ( Set.nonempty_Ioo.mpr zero_lt_one ) hy2;
      exact hL.2.2 ( Insert.insert L S ) h_add_L ( by exact fun s hs => by cases hs <;> aesop ) ( by exact fun s hs => by aesop ) |> fun h => h_add_L_subset.ne h;
    · intro h;
      refine' ⟨ hS, hR, fun S' hS' hR' hSS' => Set.Subset.antisymm hSS' _ ⟩;
      intro L hL;
      contrapose! h;
      cases hS' ; aesop

open Set

def V_L : Set Point := openSegment ℝ ![0, 0] ![0, 1]
def V_R : Set Point := openSegment ℝ ![1, 0] ![1, 1]
def H_mid : Set Point := openSegment ℝ ![0, 0.5] ![1, 0.5]

def H_bot : Set Point := openSegment ℝ ![0, 0] ![1, 0]
def H_top : Set Point := openSegment ℝ ![0, 1] ![1, 1]

/-
Define the points O(0,0), O'(1,1/2), and A_0(1,0).
-/
def O_point : Point := ![0, 0]

noncomputable def O_prime : Point := ![1, 1/2]

def A_0 : Point := ![1, 0]

/-
Define the reflection of a point through (1/2, 1/4) and state that it is an involution.
-/
noncomputable def reflection (p : Point) : Point := ![1 - p 0, 1/2 - p 1]

lemma reflection_involution (p : Point) : reflection (reflection p) = p := by
  unfold reflection;
  ext i; fin_cases i <;> norm_num;
  · rfl;
  · exact rfl

/-
Reflection preserves distance.
-/
lemma reflection_dist (p q : Point) : dist (reflection p) (reflection q) = dist p q := by
  unfold reflection; (
  norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
  ring_nf);

/-
Reflection of O is O'.
-/
lemma O_prime_reflection_O : reflection O_point = O_prime := by
  exact Eq.symm ( by ext i ; fin_cases i <;> norm_num [ reflection, O_point, O_prime ] )

/-
P is a valid next vertex if it lies on the segment O'A' (where A' is the reflection of A) and is at distance 1 from O.
-/
def is_next_vertex (A P : Point) : Prop :=
  P ∈ segment ℝ O_prime (reflection A) ∧ dist O_point P = 1

/-
There exists a point P on the segment O'A' such that dist(O, P) = 1, provided dist(O, A') <= 1.
-/
lemma exists_next_vertex (A : Point) (hA_side : dist O_point (reflection A) ≤ 1) :
  ∃ P, is_next_vertex A P := by
    unfold is_next_vertex;
    norm_num [ EuclideanSpace.dist_eq ] at *;
    unfold O_prime at * ; norm_num at *;
    unfold O_point at * ; norm_num [ dist_eq_norm ] at *;
    norm_num [ segment_eq_image ];
    apply_rules [ intermediate_value_Icc' ] <;> norm_num;
    · exact Continuous.continuousOn ( by continuity );
    · linarith

/-
Define the next vertex function and the sequence of vertices.
-/
noncomputable def next_vertex (A : Point) : Point :=
  if h : ∃ P, is_next_vertex A P then Classical.choose h else A

noncomputable def A_seq : ℕ → Point
| 0 => A_0
| n + 1 => next_vertex (A_seq n)

/-
Define the sequence of segments, their reflections, the limit segment, and the full collection.
-/
def S_seq (n : ℕ) : Set Point := openSegment ℝ O_point (A_seq (n + 1))

def S_seq_refl (n : ℕ) : Set Point := openSegment ℝ O_prime (reflection (A_seq (n + 1)))

noncomputable def A_inf : Point := ![2 / Real.sqrt 5, 1 / Real.sqrt 5]

def S_inf : Set Point := openSegment ℝ O_point A_inf

def S_collection : Set (Set Point) :=
  {s | ∃ n, s = S_seq n} ∪ {s | ∃ n, s = S_seq_refl n} ∪ {S_inf}

/-
Define the region R as the open rectangle (0,1) x (0,1/2).
-/
def Region_R : Set Point := {p | 0 < p 0 ∧ p 0 < 1 ∧ 0 < p 1 ∧ p 1 < 1/2}

/-
The collection S is countable.
-/
lemma S_collection_countable : Set.Countable S_collection := by
  -- Each of the sets {S_seq n | n : ℕ} and {S_seq_refl n | n : ℕ} is countable because they are indexed by the natural numbers.
  have h_countable_seq : Set.Countable {s : Set Point | ∃ n, s = S_seq n} := by
    exact Set.countable_range ( fun n => S_seq n ) |> Set.Countable.mono fun s => by aesop;
  have h_countable_refl : Set.Countable {s : Set Point | ∃ n, s = S_seq_refl n} := by
    exact Set.countable_range _ |> Set.Countable.mono fun x hx => hx.imp fun n hn => hn.symm;
  convert Set.Countable.union ( Set.Countable.union h_countable_seq h_countable_refl ) ( Set.countable_singleton S_inf ) using 1

/-
The distance between O and O' is greater than 1.
-/
lemma dist_O_O_prime : dist O_point O_prime > 1 := by
  norm_num [ EuclideanSpace.dist_eq, O_point, O_prime ];
  nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ]

/-
For all n, dist(O, A_n) = 1 and dist(O, A'_n) < 1.
-/
lemma A_seq_properties (n : ℕ) : dist O_point (A_seq n) = 1 ∧ dist O_point (reflection (A_seq n)) < 1 := by
  induction' n with n ih;
  · -- Let's calculate the distance from O to A_0.
    simp [O_point];
    norm_num [ dist_eq_norm, EuclideanSpace.norm_eq, A_seq, reflection ];
    exact ⟨ by norm_num [ A_0 ], by rw [ Real.sqrt_lt' ] <;> norm_num [ A_0 ] ⟩;
  · -- By definition of $A_{n+1}$, we know that $A_{n+1}$ is the next vertex of $A_n$.
    have h_next_vertex : is_next_vertex (A_seq n) (A_seq (n + 1)) := by
      convert Classical.choose_spec ( exists_next_vertex ( A_seq n ) ih.2.le );
      rw [ show A_seq ( n + 1 ) = next_vertex ( A_seq n ) from rfl, next_vertex ];
      grind;
    unfold is_next_vertex at h_next_vertex;
    rw [ segment_eq_image ] at h_next_vertex;
    obtain ⟨ ⟨ θ, hθ, h ⟩, h' ⟩ := h_next_vertex;
    simp_all +decide [ dist_eq_norm, EuclideanSpace.norm_eq ];
    rw [ Real.sqrt_lt' ] at * <;> norm_num [ ← h, reflection ] at *;
    norm_num [ O_point, O_prime ] at *;
    nlinarith [ mul_nonneg hθ.1 ( sq_nonneg ( A_seq n 0 - 1 / 2 ) ), mul_nonneg hθ.1 ( sq_nonneg ( A_seq n 1 - 1 / 4 ) ) ]

/-
The vertices A_n are in the closed region [0,1] x [0, 1/2].
-/
def ClosedRegion_R : Set Point := {p | 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1/2}

lemma A_seq_in_closed_region (n : ℕ) : A_seq n ∈ ClosedRegion_R := by
  -- By definition of $A_seq$, we know that $A_n$ is in the closed region $[0,1] \times [0, 1/2]$.
  have h_closed : ∀ n, A_seq n ∈ {p : Point | 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1/2} := by
    intro n
    induction' n with n ih;
    · exact ⟨ by rw [ show A_seq 0 = A_0 from rfl ] ; exact by rw [ show A_0 = ![1, 0] from rfl ] ; norm_num, by rw [ show A_seq 0 = A_0 from rfl ] ; exact by rw [ show A_0 = ![1, 0] from rfl ] ; norm_num, by rw [ show A_seq 0 = A_0 from rfl ] ; exact by rw [ show A_0 = ![1, 0] from rfl ] ; norm_num, by rw [ show A_seq 0 = A_0 from rfl ] ; exact by rw [ show A_0 = ![1, 0] from rfl ] ; norm_num ⟩;
    · -- By definition of $A_seq$, we know that $A_{n+1}$ is the next vertex from $A_n$, which lies on the segment $O'A'$ and is at distance 1 from $O$.
      have h_next_vertex : ∀ A : Point, dist O_point A = 1 → dist O_point (reflection A) < 1 → next_vertex A ∈ segment ℝ O_prime (reflection A) ∧ dist O_point (next_vertex A) = 1 := by
        intro A hA hA';
        have := Classical.choose_spec ( exists_next_vertex A hA'.le );
        unfold next_vertex; aesop;
      have := h_next_vertex ( A_seq n ) ( A_seq_properties n |>.1 ) ( A_seq_properties n |>.2 );
      rw [ segment_eq_image ] at this;
      norm_num +zetaDelta at *;
      rcases this.1 with ⟨ x, ⟨ hx₀, hx₁ ⟩, hx₂ ⟩ ; rw [ show A_seq ( n + 1 ) = next_vertex ( A_seq n ) by rfl ] ; rw [ ← hx₂ ] ; norm_num [ O_prime, reflection ] ;
      exact ⟨ by nlinarith, by nlinarith, by nlinarith, by nlinarith ⟩;
  convert h_closed n

/-
For all n, the coordinates of A_{n+1} are strictly positive.
-/
lemma A_seq_pos (n : ℕ) : 0 < (A_seq (n + 1)) 0 ∧ 0 < (A_seq (n + 1)) 1 := by
  -- By definition of A_seq, A_{n+1} is next_vertex of A_n and satisfies properties of being in the region.
  have h_prop : ∀ n, dist O_point (A_seq n) = 1 ∧ dist O_point (reflection (A_seq n)) < 1 := by
    intro n
    exact A_seq_properties n;
  -- By definition of $A_{n+1}$, we know that $A_{n+1}$ is the intersection of the circle centered at $O$ with radius 1 and the segment $O'A'_n$.
  have h_inter : ∃ P, P ∈ segment ℝ O_prime (reflection (A_seq n)) ∧ dist O_point P = 1 ∧ P = A_seq (n + 1) := by
    -- By definition of $next_vertex$, we know that $next_vertex (A_seq n)$ is the intersection of the circle centered at $O$ with radius 1 and the segment $O'A'_n$.
    have h_next_vertex : ∃ P, P ∈ segment ℝ O_prime (reflection (A_seq n)) ∧ dist O_point P = 1 ∧ P = next_vertex (A_seq n) := by
      unfold next_vertex;
      split_ifs with h;
      · exact ⟨ _, Classical.choose_spec h |>.1, Classical.choose_spec h |>.2, rfl ⟩;
      · contrapose! h;
        apply exists_next_vertex;
        · linarith [ h_prop n ];
    exact h_next_vertex;
  obtain ⟨ P, hP₁, hP₂, rfl ⟩ := h_inter;
  obtain ⟨ a, b, ha, hb, hab, h ⟩ := hP₁;
  -- Since $a$ and $b$ are non-negative and their sum is 1, and $O_prime$ has coordinates $(1, 1/2)$, which are positive, and $reflection (A_seq n)$ has coordinates $(1 - (A_seq n) 0, 1/2 - (A_seq n) 1)$, which are also positive because $(A_seq n) 0$ and $(A_seq n) 1$ are between 0 and 1, the resulting point from the linear combination should have positive coordinates.
  have h_pos : 0 < a * 1 + b * (1 - (A_seq n) 0) ∧ 0 < a * (1 / 2) + b * (1 / 2 - (A_seq n) 1) := by
    constructor <;> by_cases ha' : a = 0 <;> by_cases hb' : b = 0 <;> simp_all +decide;
    · grind;
    · have := A_seq_in_closed_region n;
      exact add_pos_of_pos_of_nonneg ( lt_of_le_of_ne ha ( Ne.symm ha' ) ) ( mul_nonneg hb ( sub_nonneg.mpr ( this.2.1.trans ( by norm_num ) ) ) );
    · have := h_prop n; rw [ dist_eq_norm ] at this; norm_num [ EuclideanSpace.norm_eq ] at this; aesop;
    · have := A_seq_in_closed_region n;
      cases lt_or_gt_of_ne ha' <;> cases lt_or_gt_of_ne hb' <;> nlinarith [ this.2.2.1, this.2.2.2 ];
  exact ⟨ by rw [ ← h ] ; exact h_pos.1, by rw [ ← h ] ; exact h_pos.2 ⟩

/-
The segments S_seq n are contained in the region R.
-/
lemma S_seq_in_region (n : ℕ) : S_seq n ⊆ Region_R := by
  -- By definition of $S_seq$, we know that $S_seq n = openSegment ℝ O_point (A_seq (n + 1))$.
  have h_S_seq_def : S_seq n = openSegment ℝ O_point (A_seq (n + 1)) := by
    rfl;
  -- Since $A_{n+1}$ is in the closed region $[0,1] \times [0,1/2]$, the open segment from $O$ to $A_{n+1}$ is contained in the region $R$.
  have h_A_seq_in_closed_region : A_seq (n + 1) ∈ ClosedRegion_R := by
    exact A_seq_in_closed_region _;
  rw [ h_S_seq_def, openSegment_eq_image ];
  intro x hxaesop;
  obtain ⟨ a, ⟨ ha₀, ha₁ ⟩, rfl ⟩ := hxaesop;
  have h_pos : 0 < (A_seq (n + 1)) 0 ∧ 0 < (A_seq (n + 1)) 1 := by
    exact A_seq_pos n;
  exact ⟨ by norm_num [ O_point ] ; nlinarith, by norm_num [ O_point ] ; nlinarith [ h_A_seq_in_closed_region.2.1 ], by norm_num [ O_point ] ; nlinarith, by norm_num [ O_point ] ; nlinarith [ h_A_seq_in_closed_region.2.2.2 ] ⟩

/-
The segments S_seq_refl n are contained in the region R.
-/
lemma S_seq_refl_in_region (n : ℕ) : S_seq_refl n ⊆ Region_R := by
  have hA_seq_refl_pos : 0 < (A_seq (n + 1)) 0 ∧ 0 < (A_seq (n + 1)) 1 := by
    exact A_seq_pos n;
  -- Since $A_{n+1}$ is in the closed region $[0,1] \times [0, 1/2]$, its reflection is also in the closed region.
  have hA_seq_refl_closed : reflection (A_seq (n + 1)) ∈ {p : Point | 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1/2} := by
    have hA_seq_refl_closed : A_seq (n + 1) ∈ {p : Point | 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1/2} := by
      exact A_seq_in_closed_region _;
    unfold reflection; aesop;
  intro p hp
  obtain ⟨t, ht⟩ := hp;
  rcases ht with ⟨ u, ht, hu, htu, rfl ⟩;
  constructor <;> norm_num;
  · exact add_pos_of_pos_of_nonneg ( mul_pos ht ( by norm_num [ O_prime ] ) ) ( mul_nonneg hu.le ( hA_seq_refl_closed.1 ) );
  · unfold O_prime reflection at * ; norm_num at *;
    exact ⟨ by nlinarith, by nlinarith, by nlinarith ⟩

/-
The limit segment S_inf is contained in the region R.
-/
lemma S_inf_in_region : S_inf ⊆ Region_R := by
  unfold S_inf Region_R;
  field_simp;
  rintro _ ⟨ a, b, ha, hb, hab, rfl ⟩;
  norm_num [ show a = 1 - b by linarith, O_point, A_inf ];
  exact ⟨ hb, by rw [ mul_div, div_lt_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ], hb, by rw [ ← div_eq_mul_inv ] ; rw [ div_mul_eq_mul_div, div_lt_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ⟩

/-
The collection S is contained in the region R.
-/
lemma S_collection_in_region : IsInRegion S_collection Region_R := by
  -- By definition of $S_collection$, we know that every element in $S_collection$ is either $S_seq n$, $S_seq_refl n$, or $S_inf$ for some $n$.
  intro s hs
  obtain ⟨n, rfl | rfl | rfl⟩ : ∃ n, s = S_seq n ∨ s = S_seq_refl n ∨ s = S_inf := by
    cases hs <;> aesop;
  · exact S_seq_in_region n;
  · -- Apply the lemma that states S_seq_refl n is contained in Region_R.
    apply S_seq_refl_in_region;
  · exact S_inf_in_region

/-
Every segment in the collection S is a unit segment.
-/
lemma S_collection_is_unit_segment : ∀ s ∈ S_collection, IsUnitSegment s := by
  intro s hs
  have hs_cases : ∃ n, s = S_seq n ∨ s = S_seq_refl n ∨ s = S_inf := by
    cases hs <;> aesop;
  rcases hs_cases with ⟨ n, rfl | rfl | rfl ⟩;
  · use O_point, A_seq ( n + 1 );
    exact ⟨ A_seq_properties _ |>.1, rfl ⟩;
  · use O_prime, reflection (A_seq (n + 1));
    -- By definition of $A_seq$, we know that $dist O_point (A_seq (n + 1)) = 1$.
    have h_dist : dist O_point (A_seq (n + 1)) = 1 := by
      exact A_seq_properties _ |>.1;
    exact ⟨ by simpa [ O_prime_reflection_O ] using reflection_dist O_point ( A_seq ( n + 1 ) ) |> fun h => h.trans h_dist, rfl ⟩;
  · use O_point, A_inf;
    unfold S_inf O_point A_inf;
    norm_num [ EuclideanSpace.dist_eq, openSegment_eq_image ];
    norm_num [ abs_of_pos, div_pow ]

/-
A_{n+1} is not equal to O'.
-/
lemma A_seq_ne_O_prime (n : ℕ) : A_seq (n + 1) ≠ O_prime := by
  -- By definition of $A_seq$, we know that $A_{n+1}$ lies on the segment from $O$ to $A_{n+1}$.
  have h_O_A_n1 : dist O_point (A_seq (n + 1)) = 1 := by
    exact A_seq_properties _ |>.1;
  rw [ dist_eq_norm ] at h_O_A_n1 ; norm_num [ EuclideanSpace.norm_eq, O_point, O_prime ] at h_O_A_n1 ⊢ ; aesop;

/-
A_{n+1} lies strictly between O' and A'_n.
-/
lemma A_seq_between (n : ℕ) : A_seq (n + 1) ∈ openSegment ℝ O_prime (reflection (A_seq n)) := by
  -- By definition of $next_vertex$, we know that $A_{n+1}$ is a point on the segment $O'A'_n$.
  have h_next_vertex : ∃ P, P ∈ segment ℝ O_prime (reflection (A_seq n)) ∧ dist O_point P = 1 := by
    convert exists_next_vertex ( A_seq n ) _ using 1;
    · exact le_of_lt ( A_seq_properties n |>.2 );
  -- By definition of $next_vertex$, we know that $A_{n+1}$ is a point on the segment $O'A'_n$ and satisfies $dist(O, A_{n+1}) = 1$.
  obtain ⟨P, hP_segment, hP_dist⟩ : ∃ P, P ∈ segment ℝ O_prime (reflection (A_seq n)) ∧ dist O_point P = 1 := h_next_vertex
  have h_next_vertex_def : A_seq (n + 1) = next_vertex (A_seq n) := rfl
  rw [h_next_vertex_def];
  unfold next_vertex;
  split_ifs with h;
  · have := Classical.choose_spec h;
    obtain ⟨ hP_segment, hP_dist ⟩ := this;
    have hP_ne_O_prime : Classical.choose h ≠ O_prime := by
      exact fun h' => by have := dist_O_O_prime; aesop;
    have hP_ne_reflection : Classical.choose h ≠ reflection (A_seq n) := by
      intro hP_eq_reflection;
      have := A_seq_properties n; simp_all +decide [ dist_comm ] ;
    exact
      mem_openSegment_of_ne_left_right (id (Ne.symm hP_ne_O_prime)) (id (Ne.symm hP_ne_reflection))
        hP_segment;
  · exact False.elim <| h ⟨ P, hP_segment, hP_dist ⟩

/-
A_{n+1} lies strictly between O' and A'_n.
-/
lemma A_seq_in_open_segment (n : ℕ) : A_seq (n + 1) ∈ openSegment ℝ O_prime (reflection (A_seq n)) := by
  exact A_seq_between n

/-
Define the parallelogram determined by A and its reflection, and show it is symmetric.
-/
def Parallelogram (A : Point) : Set Point := convexHull ℝ {O_point, A, O_prime, reflection A}

lemma Parallelogram_symmetric (A : Point) : ∀ p ∈ Parallelogram A, reflection p ∈ Parallelogram A := by
  unfold Parallelogram reflection;
  intro p hp;
  rw [ mem_convexHull_iff ] at *;
  intro t ht ht'; specialize hp ( ( fun x => reflection x ) ⁻¹' t ) ; simp_all +decide [ Set.subset_def ] ;
  convert hp _ _ _ _ _ using 1;
  all_goals norm_num [ reflection ] at *;
  · convert ht.2.2.1 using 1 ; ext i ; fin_cases i <;> norm_num [ O_point, O_prime ];
  · tauto;
  · convert ht.1 using 1 ; ext i ; fin_cases i <;> norm_num [ O_prime ];
    · exact rfl;
    · exact rfl;
  · convert ht.2.1 using 1;
    ext i; fin_cases i <;> rfl;
  · intro x hx y hy a b ha hb hab; simp_all +decide
    convert ht' hx hy ha hb hab using 1 ; ext i ; fin_cases i <;> norm_num <;> ring_nf;
    · grind;
    · linear_combination -hab * ( 1 / 2 )

/-
A_{n+1} lies on the closed segment [O', A'_n].
-/
lemma A_seq_mem_closed_segment (n : ℕ) : A_seq (n + 1) ∈ segment ℝ O_prime (reflection (A_seq n)) := by
  -- Since the open segment is a subset of the segment, we can conclude that A_seq (n + 1) is in the segment.
  apply openSegment_subset_segment; exact A_seq_in_open_segment n

/-
Define the triangle OA'P.
-/
def Triangle_OA_prime_P (n : ℕ) : Set Point := convexHull ℝ {O_point, reflection (A_seq n), A_seq (n + 1)}

/-
The distance from O to A_{n+1} is 1.
-/
lemma dist_O_A_seq_next_eq_one (n : ℕ) : dist O_point (A_seq (n + 1)) = 1 := by
  exact A_seq_properties _ |>.1

/-
The distance between A'_n and A_{n+1} is strictly less than 1.
-/
lemma dist_reflection_A_seq_A_seq_next_lt_one (n : ℕ) : dist (reflection (A_seq n)) (A_seq (n + 1)) < 1 := by
  -- Since $A_seq (n + 1)$ is in the open segment $(O', reflection (A_seq n))$, we have $dist (reflection (A_seq n)) (A_seq (n + 1)) < dist (reflection (A_seq n)) O'$.
  have h_dist_lt : dist (reflection (A_seq n)) (A_seq (n + 1)) < dist (reflection (A_seq n)) O_prime := by
    -- Since $A_{n+1}$ is in the open segment $(O', A'_n)$, we have $dist (reflection (A_seq n)) (A_seq (n + 1)) < dist (reflection (A_seq n)) O'$.
    have h_dist_lt : A_seq (n + 1) ∈ openSegment ℝ O_prime (reflection (A_seq n)) := by
      exact A_seq_between n;
    rw [ openSegment_eq_image ] at h_dist_lt;
    simp +zetaDelta at *;
    obtain ⟨ x, hx₁, hx₂ ⟩ := h_dist_lt; rw [ ← hx₂ ] ; norm_num [ dist_eq_norm ] ; ring_nf ;
    rw [ show reflection ( A_seq n ) - ( ( 1 - x ) • O_prime + x • reflection ( A_seq n ) ) = ( 1 - x ) • ( reflection ( A_seq n ) - O_prime ) by ext ; simpa using by ring ] ; rw [ norm_smul, Real.norm_of_nonneg ( by linarith ) ] ; exact mul_lt_of_lt_one_left ( norm_pos_iff.mpr <| sub_ne_zero.mpr <| by
          intro h; have := A_seq_ne_O_prime n; simp_all +decide [ reflection ] ;
          exact this ( by rw [ ← hx₂ ] ; ext i; fin_cases i <;> norm_num [ ← List.ofFn_inj ] at * <;> linarith! ) ) <| by linarith;
  refine lt_of_lt_of_le h_dist_lt ?_;
  -- Since reflection is an isometry, the distance between O' and A'_n is the same as the distance between O and A_n.
  have h_dist_eq : dist (reflection (A_seq n)) O_prime = dist O_point (A_seq n) := by
    convert reflection_dist ( A_seq n ) O_point using 1;
    · unfold reflection; norm_num;
      unfold O_prime O_point; norm_num;
    · exact dist_comm _ _;
  rw [ h_dist_eq, A_seq_properties n |>.1 ]

/-
The distance from O to A'_n is strictly less than 1.
-/
lemma dist_O_reflection_A_seq_lt_one (n : ℕ) : dist O_point (reflection (A_seq n)) < 1 := (A_seq_properties n).2

/-
If a triangle has one side of length 1 and the others strictly less than 1, then the only pair of points in the triangle at distance 1 is the pair of endpoints of the longest side.
-/
lemma unique_diam_of_triangle (A B C : Point) (hAB : dist A B = 1) (hBC : dist B C < 1) (hCA : dist C A < 1) :
  ∀ x, x ∈ convexHull ℝ {A, B, C} → ∀ y, y ∈ convexHull ℝ {A, B, C} → dist x y = 1 → (x = A ∧ y = B) ∨ (x = B ∧ y = A) := by
    -- Apply the lemma that states if the distance between two points in a convex set is 1, then they must be on the boundary.
    have h_boundary : ∀ x y : Point, x ∈ convexHull ℝ {A, B, C} → y ∈ convexHull ℝ {A, B, C} → dist x y = 1 → x = A ∧ y = B ∨ x = B ∧ y = A := by
      intros x y hx hy hxy
      have h_convex : convexHull ℝ {A, B, C} ⊆ {p | dist p A ≤ 1 ∧ dist p B ≤ 1 ∧ dist p C ≤ 1} := by
        intro p hp
        obtain ⟨t1, t2, t3, ht1, ht2, ht3, hp_convex⟩ : ∃ t1 t2 t3 : ℝ, 0 ≤ t1 ∧ 0 ≤ t2 ∧ 0 ≤ t3 ∧ t1 + t2 + t3 = 1 ∧ p = t1 • A + t2 • B + t3 • C := by
          rw [ convexHull_insert ] at hp;
          · norm_num [ segment_eq_image ] at hp;
            rcases hp with ⟨ i, hi, x, hx, rfl ⟩ ; exact ⟨ 1 - x, x * ( 1 - i ), x * i, by linarith, by nlinarith, by nlinarith, by linarith, by ext ; simpa using by ring ⟩ ;
          · norm_num;
        simp_all +decide [ dist_eq_norm ];
        refine' ⟨ _, _, _ ⟩;
        · -- By the properties of the norm, we can bound the expression.
          have h_norm_bound : ‖t1 • A + t2 • B + t3 • C - A‖ ≤ t2 * ‖B - A‖ + t3 * ‖C - A‖ := by
            convert norm_add_le ( t2 • ( B - A ) ) ( t3 • ( C - A ) ) using 1;
            · exact congr_arg Norm.norm ( by rw [ show t1 = 1 - t2 - t3 by linarith ] ; ext ; norm_num ; ring );
            · rw [ norm_smul, norm_smul, Real.norm_of_nonneg ht2, Real.norm_of_nonneg ht3 ];
          exact h_norm_bound.trans ( by rw [ norm_sub_rev B A ] at *; nlinarith );
        · -- By the properties of the norm, we can bound the distance.
          have h_norm_bound : ‖t1 • (A - B) + t3 • (C - B)‖ ≤ t1 * ‖A - B‖ + t3 * ‖C - B‖ := by
            exact norm_add_le_of_le ( by rw [ norm_smul, Real.norm_of_nonneg ht1 ] ) ( by rw [ norm_smul, Real.norm_of_nonneg ht3 ] );
          convert h_norm_bound.trans _ using 1;
          · exact congr_arg Norm.norm ( by ext i; simpa using by rw [ ← eq_sub_iff_add_eq' ] at hp_convex; rw [ hp_convex.1 ] ; ring );
          · rw [ norm_sub_rev C B ];
            nlinarith [ norm_nonneg ( A - B ), norm_nonneg ( B - C ) ];
        · rw [ show t1 • A + t2 • B + t3 • C - C = t1 • ( A - C ) + t2 • ( B - C ) by ext i; simpa using by rw [ show t3 = 1 - t1 - t2 by linarith ] ; simpa using by ring ];
          refine' le_trans ( norm_add_le _ _ ) _;
          rw [ norm_smul, norm_smul, Real.norm_of_nonneg ht1, Real.norm_of_nonneg ht2 ];
          rw [ norm_sub_rev C A ] at hCA;
          nlinarith [ norm_nonneg ( A - C ), norm_nonneg ( B - C ) ]
      -- Since $x$ and $y$ are in the convex hull of $\{A, B, C\}$, we can write them as convex combinations of $A$, $B$, and $C$.
      obtain ⟨a, b, c, ha, hb, hc, hx_comb⟩ : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ x = a • A + b • B + c • C := by
        rw [ convexHull_insert ] at hx;
        · norm_num [ segment_eq_image ] at hx;
          rcases hx with ⟨ i, hi, j, hj, rfl ⟩ ; exact ⟨ 1 - j, j * ( 1 - i ), j * i, by linarith, by nlinarith, by nlinarith, by linarith, by ext ; simpa using by ring ⟩ ;
        · norm_num
      obtain ⟨a', b', c', ha', hb', hc', hy_comb⟩ : ∃ a' b' c' : ℝ, 0 ≤ a' ∧ 0 ≤ b' ∧ 0 ≤ c' ∧ a' + b' + c' = 1 ∧ y = a' • A + b' • B + c' • C := by
        rw [ convexHull_insert ] at hy hy;
        · norm_num [ segment_eq_image ] at hy;
          rcases hy with ⟨ i, hi, x, hx, rfl ⟩ ; exact ⟨ 1 - x, x * ( 1 - i ), x * i, by nlinarith, by nlinarith, by nlinarith, by nlinarith, by ext ; simpa using by ring ⟩ ;
        · norm_num;
        · norm_num;
      -- By the properties of the convex hull and the triangle inequality, we can deduce that $x$ and $y$ must lie on the line segment $AB$.
      have h_line_segment : dist x y ≤ a * a' * dist A A + a * b' * dist A B + a * c' * dist A C + b * a' * dist B A + b * b' * dist B B + b * c' * dist B C + c * a' * dist C A + c * b' * dist C B + c * c' * dist C C := by
        rw [ dist_eq_norm, dist_eq_norm, dist_eq_norm, dist_eq_norm, dist_eq_norm, dist_eq_norm, dist_eq_norm, dist_eq_norm, dist_eq_norm ] at *;
        rw [ hx_comb.2, hy_comb.2 ];
        convert norm_sum_le ( Finset.range 9 ) ( fun i => if i = 0 then ( a * a' ) • ( A - A ) else if i = 1 then ( a * b' ) • ( A - B ) else if i = 2 then ( a * c' ) • ( A - C ) else if i = 3 then ( b * a' ) • ( B - A ) else if i = 4 then ( b * b' ) • ( B - B ) else if i = 5 then ( b * c' ) • ( B - C ) else if i = 6 then ( c * a' ) • ( C - A ) else if i = 7 then ( c * b' ) • ( C - B ) else ( c * c' ) • ( C - C ) ) using 1;
        · rw [ show a = 1 - b - c by linarith, show a' = 1 - b' - c' by linarith ] ; norm_num [ Finset.sum_range_succ ] ; ring_nf;
          exact congr_arg Norm.norm ( by ext ; norm_num ; ring );
        · norm_num [ Finset.sum_range_succ, norm_smul ] ; ring_nf;
          simpa only [ abs_of_nonneg ha, abs_of_nonneg hb, abs_of_nonneg hc, abs_of_nonneg ha', abs_of_nonneg hb', abs_of_nonneg hc' ] using by ring;
      simp_all +decide [ dist_comm ];
      -- Since $a + b + c = 1$ and $a' + b' + c' = 1$, we can simplify the inequality.
      have h_simplified : 1 ≤ a * b' + a * c' + b * a' + b * c' + c * a' + c * b' := by
        nlinarith [ mul_nonneg ha ha', mul_nonneg ha hb', mul_nonneg ha hc', mul_nonneg hb ha', mul_nonneg hb hb', mul_nonneg hb hc', mul_nonneg hc ha', mul_nonneg hc hb', mul_nonneg hc hc' ];
      have h_simplified : a * c' = 0 ∧ b * c' = 0 ∧ c * a' = 0 ∧ c * b' = 0 := by
        refine' ⟨ _, _, _, _ ⟩ <;> nlinarith only [ ha, hb, hc, ha', hb', hc', hx_comb, hy_comb, h_simplified, h_line_segment, hCA, hBC, hAB, mul_nonneg ha hc', mul_nonneg hb hc', mul_nonneg hc ha', mul_nonneg hc hb' ];
      cases lt_or_eq_of_le ha <;> cases lt_or_eq_of_le hb <;> cases lt_or_eq_of_le ha' <;> cases lt_or_eq_of_le hb' <;> first | nlinarith | aesop;
    exact fun x hx y hy hxy => h_boundary x y hx hy hxy

/-
The only points in the triangle OA'P at distance 1 are O and P.
-/
lemma Triangle_OA_prime_P_unique_diam' (n : ℕ) :
  ∀ x y, x ∈ Triangle_OA_prime_P n → y ∈ Triangle_OA_prime_P n → dist x y = 1 → (x = O_point ∧ y = A_seq (n + 1)) ∨ (x = A_seq (n + 1) ∧ y = O_point) := by
  intro x y hx hy hxy
  let A := O_point
  let B := A_seq (n + 1)
  let C := reflection (A_seq n)
  have hAB : dist A B = 1 := dist_O_A_seq_next_eq_one n
  have hBC : dist B C < 1 := by rw [dist_comm]; exact dist_reflection_A_seq_A_seq_next_lt_one n
  have hCA : dist C A < 1 := by rw [dist_comm]; exact dist_O_reflection_A_seq_lt_one n
  have h_hull : Triangle_OA_prime_P n = convexHull ℝ {A, B, C} := by
    unfold Triangle_OA_prime_P
    congr 1
    ext p
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor <;> aesop
  rw [h_hull] at hx hy
  exact unique_diam_of_triangle A B C hAB hBC hCA x hx y hy hxy

/-
Any unit segment contained in the triangle OA'P is equal to the segment OP.
-/
lemma Triangle_OA_prime_P_unit_segment_eq_S_seq (n : ℕ) :
  ∀ L, IsUnitSegment L → L ⊆ Triangle_OA_prime_P n → L = S_seq n := by
    intro L hL hL_sub
    obtain ⟨x, y, hxy⟩ := hL
    have hxy_eq : x ∈ Triangle_OA_prime_P n ∧ y ∈ Triangle_OA_prime_P n ∧ dist x y = 1 := by
      have hxy_in_triangle : ∀ p ∈ openSegment ℝ x y, p ∈ Triangle_OA_prime_P n := by
        grind;
      -- Since the open segment is dense in the closed segment, x and y must be in the closure of the open segment.
      have hx_closure : x ∈ closure (openSegment ℝ x y) := by
        -- Since the open segment is dense in the closed segment, the closure of the open segment is the closed segment.
        have h_closure : closure (openSegment ℝ x y) = segment ℝ x y := by
          exact closure_openSegment x y;
        exact h_closure.symm ▸ left_mem_segment _ _ _
      have hy_closure : y ∈ closure (openSegment ℝ x y) := by
        simp +zetaDelta at *;
        exact right_mem_segment _ _ _;
      have h_closed_triangle : IsClosed (Triangle_OA_prime_P n) := by
        -- The convex hull of a finite set of points in a finite-dimensional space is closed.
        have h_convex_hull_closed : ∀ (s : Finset Point), IsClosed (convexHull ℝ (s : Set Point)) := by
          intro s; exact (by
          have h_convex_hull_closed : ∀ (s : Finset Point), IsCompact (convexHull ℝ (s : Set Point)) := by
            exact fun s => s.finite_toSet.isCompact_convexHull;
          exact IsCompact.isClosed ( h_convex_hull_closed s ));
        exact h_convex_hull_closed { O_point, reflection ( A_seq n ), A_seq ( n + 1 ) } |> fun h => by simpa using h;
      have hy_in_triangle : y ∈ closure (Triangle_OA_prime_P n) := by
        exact closure_mono ( Set.subset_def.mpr hxy_in_triangle ) hy_closure
      have hx_in_triangle' : x ∈ Triangle_OA_prime_P n := by
        exact h_closed_triangle.closure_subset_iff.mpr ( Set.subset_def.mpr fun p hp => hxy_in_triangle p hp ) hx_closure
      have hy_in_triangle' : y ∈ Triangle_OA_prime_P n := by
        exact h_closed_triangle.closure_subset hy_in_triangle
      exact ⟨hx_in_triangle', hy_in_triangle', hxy.left⟩;
    have hxy_eq : (x = O_point ∧ y = A_seq (n + 1)) ∨ (x = A_seq (n + 1) ∧ y = O_point) := by
      exact Triangle_OA_prime_P_unique_diam' n x y hxy_eq.1 hxy_eq.2.1 hxy_eq.2.2;
    cases hxy_eq <;> simp_all +decide [ S_seq ];
    exact openSegment_symm ℝ (A_seq (n + 1)) O_point

/-
The triangle OA'P is a closed set.
-/
lemma Triangle_OA_prime_P_isClosed (n : ℕ) : IsClosed (Triangle_OA_prime_P n) := by
  -- The convex hull of a finite set of points is closed.
  have h_convex_hull_closed : ∀ (s : Finset Point), IsClosed (convexHull ℝ (s : Set Point)) := by
    intro s;
    convert ( s.finite_toSet.isCompact_convexHull.isClosed ) using 1;
  convert h_convex_hull_closed { O_point, reflection ( A_seq n ), A_seq ( n + 1 ) } using 1;
  aesop

/-
Any unit segment contained in the triangle OA'P is equal to the segment OP.
-/
lemma Triangle_OA_prime_P_unit_segment_eq_S_seq_v2 (n : ℕ) :
  ∀ L, IsUnitSegment L → L ⊆ Triangle_OA_prime_P n → L = S_seq n := by
    exact fun L a a_1 ↦ Triangle_OA_prime_P_unit_segment_eq_S_seq n L a a_1

/-
The sequence of parallelograms is nested.
-/
def Parallelogram_seq (n : ℕ) : Set Point := Parallelogram (A_seq n)

lemma Parallelogram_seq_subset (n : ℕ) : Parallelogram_seq (n + 1) ⊆ Parallelogram_seq n := by
  -- By definition of $A_seq$, we know that $A_{n+1}$ lies on the segment $O'A'_n$.
  have h_A_seq_succ : A_seq (n + 1) ∈ segment ℝ O_prime (reflection (A_seq n)) := by
    exact A_seq_mem_closed_segment n;
  -- Since $A_{n+1}$ is strictly between $O'$ and $A'_n$, we have $A'_{n+1} \in [O, A_n]$.
  have h_A_seq_succ_reflection : reflection (A_seq (n + 1)) ∈ segment ℝ O_point (A_seq n) := by
    obtain ⟨ a, b, ha, hb, hab, h ⟩ := h_A_seq_succ;
    rw [ ← h, segment_eq_image ];
    refine' ⟨ b, ⟨ hb, by linarith ⟩, _ ⟩ ; ext i ; fin_cases i <;> norm_num [ reflection ] <;> ring_nf;
    · rw [ show O_prime 0 = 1 by exact rfl ] ; rw [ show O_point ⟨ 0, by decide ⟩ = 0 by exact rfl ] ; rw [ show a = 1 - b by linarith ] ; ring!;
    · rw [ show O_prime 1 = 1 / 2 by exact rfl ] ; rw [ show O_point ⟨ 1, by norm_num ⟩ = 0 by exact rfl ] ; rw [ ← eq_sub_iff_add_eq' ] at hab ; subst_vars ; ring_nf;
      rfl;
  -- By definition of $A_seq$, we know that $A_{n+1}$ lies on the segment $O'A'_n$, and $A'_{n+1}$ lies on the segment $OA_n$.
  have h_vertices : {O_point, A_seq (n + 1), O_prime, reflection (A_seq (n + 1))} ⊆ {O_point, A_seq n, O_prime, reflection (A_seq n)} ∪ segment ℝ O_point (A_seq n) ∪ segment ℝ O_prime (reflection (A_seq n)) := by
    simp_all +decide [ Set.insert_subset_iff ];
  -- By definition of $A_seq$, we know that $A_{n+1}$ lies on the segment $O'A'_n$, and $A'_{n+1}$ lies on the segment $OA_n$. Therefore, the convex hull of $\{O, A_{n+1}, O', A'_{n+1}\}$ is contained in the convex hull of $\{O, A_n, O', A'_n\}$.
  have h_convex_hull : convexHull ℝ {O_point, A_seq (n + 1), O_prime, reflection (A_seq (n + 1))} ⊆ convexHull ℝ ({O_point, A_seq n, O_prime, reflection (A_seq n)} ∪ segment ℝ O_point (A_seq n) ∪ segment ℝ O_prime (reflection (A_seq n))) := by
    exact convexHull_mono h_vertices;
  -- Since the convex hull of the union of the segments is contained in the convex hull of the vertices, we have:
  have h_convex_hull_union : convexHull ℝ ({O_point, A_seq n, O_prime, reflection (A_seq n)} ∪ segment ℝ O_point (A_seq n) ∪ segment ℝ O_prime (reflection (A_seq n))) ⊆ convexHull ℝ {O_point, A_seq n, O_prime, reflection (A_seq n)} := by
    refine' convexHull_min _ _;
    · simp +decide [ Set.insert_subset_iff, segment_subset_convexHull ];
      exact ⟨ subset_convexHull ℝ _ <| Set.mem_insert _ _, subset_convexHull ℝ _ <| Set.mem_insert_of_mem _ <| Set.mem_insert _ _, subset_convexHull ℝ _ <| Set.mem_insert_of_mem _ <| Set.mem_insert_of_mem _ <| Set.mem_insert _ _, subset_convexHull ℝ _ <| Set.mem_insert_of_mem _ <| Set.mem_insert_of_mem _ <| Set.mem_insert_of_mem _ <| Set.mem_singleton _ ⟩;
    · exact convex_convexHull ℝ _;
  exact h_convex_hull.trans h_convex_hull_union

/-
Define the reflected triangle T'_n.
-/
def Triangle_seq_refl (n : ℕ) : Set Point := reflection '' (Triangle_OA_prime_P n)

/-
The union of the triangle, the next parallelogram, and the reflected triangle is contained in the current parallelogram.
-/
lemma Parallelogram_decomposition_subset (n : ℕ) :
  Triangle_OA_prime_P n ∪ Parallelogram_seq (n + 1) ∪ Triangle_seq_refl n ⊆ Parallelogram_seq n := by
    have h_Tn_sub_Pn : Triangle_OA_prime_P n ⊆ Parallelogram_seq n := by
      refine' convexHull_min _ _;
      · rintro x ( rfl | rfl | rfl ) <;> norm_num [ Parallelogram_seq ];
        · exact subset_convexHull ℝ _ ( Set.mem_insert _ _ );
        · exact subset_convexHull ℝ _ ( by norm_num [ Parallelogram ] );
        · -- By definition of $A_{n+1}$, we know that $A_{n+1}$ lies on the segment $O'A'_n$.
          have h_A_seq_in_segment : A_seq (n + 1) ∈ segment ℝ O_prime (reflection (A_seq n)) := by
            exact A_seq_mem_closed_segment n;
          refine' segment_subset_convexHull _ _ h_A_seq_in_segment;
          · norm_num;
          · grind;
      · exact convex_convexHull ℝ _
    have h_Pn_sub_Pn : Parallelogram_seq (n + 1) ⊆ Parallelogram_seq n := by
      exact Parallelogram_seq_subset n
    have h_Tn'_sub_Pn : Triangle_seq_refl n ⊆ Parallelogram_seq n := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hy_in_Pn : y ∈ Parallelogram_seq n := by
        exact h_Tn_sub_Pn hy
      exact Parallelogram_symmetric (A_seq n) y hy_in_Pn |> fun h => by simpa [Parallelogram] using h;
    exact Set.union_subset (Set.union_subset h_Tn_sub_Pn h_Pn_sub_Pn) h_Tn'_sub_Pn

/-
Any unit segment contained in the reflected triangle is equal to the reflected segment.
-/
lemma Triangle_seq_refl_unit_segment_eq_S_seq_refl (n : ℕ) :
  ∀ L, IsUnitSegment L → L ⊆ Triangle_seq_refl n → L = S_seq_refl n := by
    intro L hL hL_sub
    have hrefl_L : reflection '' L ⊆ Triangle_OA_prime_P n := by
      intro x hx; obtain ⟨ y, hy, rfl ⟩ := hx; obtain ⟨ z, hz, rfl ⟩ := hL_sub hy; exact (by
      convert hz using 1;
      exact reflection_involution z);
    -- Since reflection is an isometry, the unit segments within T'_n and T_n are congruent.
    have h_unit_segment_cong : ∀ (L : Set Point), IsUnitSegment L → L ⊆ Triangle_OA_prime_P n → L = S_seq n := by
      exact fun L a a_1 ↦ Triangle_OA_prime_P_unit_segment_eq_S_seq_v2 n L a a_1;
    convert congr_arg ( reflection '' · ) ( h_unit_segment_cong ( reflection '' L ) ?_ ?_ ) using 1;
    · simp +decide [ ← Set.image_comp, reflection_involution ];
    · ext; simp [S_seq_refl, S_seq];
      constructor;
      · rintro ⟨ a, b, ha, hb, hab, rfl ⟩;
        refine' ⟨ a • O_point + b • A_seq ( n + 1 ), _, _ ⟩ <;> norm_num [ openSegment_eq_image ];
        · exact ⟨ b, ⟨ hb, by linarith ⟩, by rw [ ← eq_sub_iff_add_eq' ] at hab; subst hab; ext i; fin_cases i <;> norm_num ⟩;
        · ext i ; fin_cases i <;> norm_num [ reflection ] <;> ring_nf;
          · rw [ show O_point 0 = 0 by rfl, show O_prime ⟨ 0, by norm_num ⟩ = 1 by rfl ] ; rw [ ← eq_sub_iff_add_eq' ] at hab ; subst_vars ; ring;
          · rw [ show O_prime ⟨ 1, by norm_num ⟩ = 1 / 2 by rfl ] ; rw [ show O_point 1 = 0 by rfl ] ; rw [ ← eq_sub_iff_add_eq' ] at hab ; subst_vars ; ring;
      · rintro ⟨ x, hx, rfl ⟩;
        obtain ⟨ a, b, ha, hb, hab, rfl ⟩ := hx;
        refine' ⟨ a, b, ha, hb, hab, _ ⟩;
        ext i; fin_cases i <;> norm_num [ reflection ] <;> ring_nf;
        · rw [ show O_prime ⟨ 0, by norm_num ⟩ = 1 by exact rfl, show O_point 0 = 0 by exact rfl ] ; linarith;
        · rw [ show O_prime ⟨ 1, by norm_num ⟩ = 1 / 2 by rfl, show O_point 1 = 0 by rfl ] ; rw [ ← eq_sub_iff_add_eq' ] at hab ; subst_vars ; ring;
    · obtain ⟨ x, y, hxy, rfl ⟩ := hL;
      refine' ⟨ reflection x, reflection y, _, _ ⟩;
      · rw [ reflection_dist, hxy ];
      · ext; simp [openSegment];
        constructor;
        · rintro ⟨ z, ⟨ a, ha, b, hb, hab, rfl ⟩, rfl ⟩;
          refine' ⟨ a, ha, b, hb, hab, _ ⟩ ; ext i ; fin_cases i <;> norm_num [ reflection ] <;> ring_nf;
          · linarith;
          · linear_combination' hab * ( 1 / 2 );
        · rintro ⟨ a, ha, b, hb, hab, rfl ⟩;
          refine' ⟨ _, ⟨ a, ha, b, hb, hab, rfl ⟩, _ ⟩;
          ext i; fin_cases i <;> norm_num [ reflection ] <;> ring_nf;
          · linarith;
          · rw [ ← eq_sub_iff_add_eq' ] at hab ; subst_vars ; ring;
    · assumption

/-
The segment connecting O and O' is contained in the intersection of the sequence of parallelograms.
-/
lemma segment_O_O_prime_subset_inter_Parallelogram_seq : segment ℝ O_point O_prime ⊆ ⋂ n, Parallelogram_seq n := by
  -- Since O and O' are vertices of every parallelogram P_n, and P_n is convex, the segment OO' is contained in P_n for all n. Thus OO' is in the intersection.
  have h_segment_subset_parallelogram : ∀ n, segment ℝ O_point O_prime ⊆ Parallelogram_seq n := by
    intro n
    have h_segment_subset_parallelogram : segment ℝ O_point O_prime ⊆ convexHull ℝ {O_point, A_seq n, O_prime, reflection (A_seq n)} := by
      exact segment_subset_convexHull ( by norm_num ) ( by norm_num );
    exact h_segment_subset_parallelogram;
  exact Set.subset_iInter h_segment_subset_parallelogram

/-
The distance of a point p from the line x - 2y = 0 (scaled by sqrt(5)).
-/
def dist_from_diagonal (p : Point) : ℝ := |p 0 - 2 * p 1|

/-
For any point p in the n-th parallelogram, its distance from the diagonal is at most the distance of A_n from the diagonal.
-/
lemma dist_from_diagonal_le_A_seq (n : ℕ) :
  ∀ p ∈ Parallelogram_seq n, dist_from_diagonal p ≤ dist_from_diagonal (A_seq n) := by
    intro p hp;
    -- By definition of $Parallelogram_seq$, we know that $p$ is a convex combination of $O$, $A_n$, $O'$, and $A'_n$.
    obtain ⟨a, b, c, d, ha, hb, hc, hd, habcd⟩ : ∃ a b c d : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ a + b + c + d = 1 ∧ p = a • O_point + b • A_seq n + c • O_prime + d • reflection (A_seq n) := by
      unfold Parallelogram_seq at hp;
      unfold Parallelogram at hp;
      rw [ convexHull_insert ] at hp;
      · norm_num [ segment_eq_image ] at hp;
        rcases hp with ⟨ i, hi, x, hx, rfl ⟩;
        rw [ convexHull_insert ] at hi;
        · norm_num [ segment_eq_image ] at hi;
          rcases hi with ⟨ y, hy, z, hz, rfl ⟩;
          exact ⟨ 1 - x, x * ( 1 - z ), x * z * ( 1 - y ), x * z * y, by linarith, by nlinarith, by nlinarith [ mul_nonneg hx.1 hz.1 ], by nlinarith [ mul_nonneg hx.1 hz.1 ], by linarith, by ext i; norm_num; ring ⟩;
        · norm_num;
      · norm_num;
    unfold dist_from_diagonal at *;
    norm_num [ habcd, O_point, O_prime, reflection ];
    rw [ abs_le ];
    constructor <;> cases abs_cases ( A_seq n 0 - 2 * A_seq n 1 ) <;> nlinarith

/-
The distance of A_{n+1} from the diagonal is at most (2 - sqrt(3))/2 times the distance of A_n from the diagonal.
-/
lemma dist_from_diagonal_recurrence (n : ℕ) :
  dist_from_diagonal (A_seq (n + 1)) ≤ ((2 - Real.sqrt 3) / 2) * dist_from_diagonal (A_seq n) := by
    have := A_seq_properties n;
    -- Let $A_n = (x, y)$. Then $A_{n+1}$ lies on the segment connecting $O'(1, 1/2)$ and $A'_n(1-x, 1/2-y)$.
    set x := (A_seq n) 0
    set y := (A_seq n) 1
    have hA_n : x^2 + y^2 = 1 := by
      simp_all +decide [ dist_eq_norm, EuclideanSpace.norm_eq ];
      unfold O_point at this; aesop;
    -- The condition $|A_{n+1}| = 1$ implies $(1-tx)^2 + (1/2-ty)^2 = 1$, which simplifies to $t^2 - t(2x+y) + 1/4 = 0$ (using $x^2+y^2=1$).
    have ht_eq : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ (1 - t * x - (A_seq (n + 1)) 0)^2 + (1 / 2 - t * y - (A_seq (n + 1)) 1)^2 = 0 ∧ t^2 - t * (2 * x + y) + 1 / 4 = 0 := by
      -- By definition of $A_{n+1}$, we know that it lies on the segment connecting $O'$ and $A'_n$.
      obtain ⟨t, ht⟩ : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ (A_seq (n + 1)) 0 = 1 - t * x ∧ (A_seq (n + 1)) 1 = 1 / 2 - t * y := by
        have hA_n1 : A_seq (n + 1) ∈ openSegment ℝ O_prime (reflection (A_seq n)) := by
          exact A_seq_between n;
        obtain ⟨ a, b, ha, hb, hab, h ⟩ := hA_n1;
        use b;
        simp_all +decide [ ← h, ← eq_sub_iff_add_eq' ];
        unfold reflection O_prime; norm_num; exact ⟨ by linarith, by linarith, by ring, by ring ⟩ ;
      use t;
      have := dist_O_A_seq_next_eq_one n; simp_all +decide [ dist_eq_norm, EuclideanSpace.norm_eq ];
      unfold O_point at *; norm_num at *; nlinarith;
    -- We need to bound $t$. Since $x, y > 0$ and $y < 1/2$, we have $x > \sqrt{3}/2$.
    obtain ⟨t, ht₀, ht₁, ht₂, ht₃⟩ := ht_eq
    have ht_bound : t ≤ (2 - Real.sqrt 3) / 2 := by
      have ht_bound : 2 * x + y ≥ 2 := by
        have := A_seq_in_closed_region n;
        nlinarith only [ this.1, this.2.1, this.2.2.1, this.2.2.2, hA_n, ht₃, ht₀, ht₁ ];
      nlinarith only [ ht₀, ht₁, ht₃, ht_bound, Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ), mul_le_mul_of_nonneg_left ht_bound ht₀ ];
    -- We have $dist\_from\_diagonal(A_{n+1}) = |(1-tx) - 2(1/2-ty)| = |t(2y-x)| = t |x-2y| = t \cdot dist\_from\_diagonal(A_n)$.
    have h_dist_eq : dist_from_diagonal (A_seq (n + 1)) = t * dist_from_diagonal (A_seq n) := by
      unfold dist_from_diagonal;
      rw [ show A_seq ( n + 1 ) 0 = 1 - t * x by nlinarith only [ ht₂ ], show A_seq ( n + 1 ) 1 = 1 / 2 - t * y by nlinarith only [ ht₂ ] ] ; ring_nf;
      rw [ show - ( t * x ) + t * y * 2 = t * ( -x + y * 2 ) by ring, abs_mul, abs_of_nonneg ht₀ ] ; ring_nf;
      rw [ ← abs_neg ] ; ring_nf;
      rfl;
    exact h_dist_eq ▸ mul_le_mul_of_nonneg_right ht_bound ( abs_nonneg _ )

/-
The contraction factor is less than 1.
-/
noncomputable def contraction_factor : ℝ := (2 - Real.sqrt 3) / 2

/-
The distance of A_n from the diagonal is bounded by the contraction factor raised to the power of n times the initial distance.
-/
lemma dist_from_diagonal_bound (n : ℕ) :
  dist_from_diagonal (A_seq n) ≤ contraction_factor ^ n * dist_from_diagonal (A_seq 0) := by
    induction' n with n ih;
    · norm_num;
    · rw [ pow_succ', mul_assoc ];
      exact le_trans ( dist_from_diagonal_recurrence n ) ( mul_le_mul_of_nonneg_left ih ( by exact div_nonneg ( sub_nonneg.mpr ( Real.sqrt_le_iff.mpr ⟨ by norm_num, by norm_num ⟩ ) ) zero_le_two ) )

/-
If a point is in the first parallelogram and has distance 0 from the diagonal, then it lies on the segment connecting O and O'.
-/
lemma dist_from_diagonal_eq_zero_implies_on_segment (p : Point) (hp : p ∈ Parallelogram_seq 0) (h : dist_from_diagonal p = 0) : p ∈ segment ℝ O_point O_prime := by
  unfold dist_from_diagonal at h;
  unfold Parallelogram_seq at hp;
  unfold Parallelogram at hp;
  rw [ convexHull_insert ] at hp <;> norm_num at *;
  rcases hp with ⟨ q, hq, hpq ⟩;
  rw [ segment_eq_image ] at *;
  rcases hpq with ⟨ θ, hθ, rfl ⟩ ; rw [ convexHull_insert ] at hq <;> norm_num at *;
  rcases hq with ⟨ i, hi, hq ⟩;
  rw [ segment_eq_image ] at hi hq;
  rcases hi with ⟨ x, hx, rfl ⟩ ; rcases hq with ⟨ y, hy, rfl ⟩ ; norm_num [ A_seq ] at *;
  unfold O_point O_prime A_0 reflection at * ; norm_num at *;
  exact ⟨ θ * ( 1 - y ) + θ * y * ( 1 - x ), ⟨ by nlinarith, by nlinarith ⟩, by ext i; fin_cases i <;> norm_num <;> linarith ⟩

/-
The intersection of the sequence of parallelograms is contained in the segment connecting O and O'.
-/
lemma inter_Parallelogram_seq_subset_segment_O_O_prime : (⋂ n, Parallelogram_seq n) ⊆ segment ℝ O_point O_prime := by
  -- If a point p is in the intersection of all Parallelogram_seq n, then for every n, p is in Parallelogram_seq n. By the lemma dist_from_diagonal_le_A_seq, this implies that the distance of p from the diagonal is less than or equal to the distance of A_seq n from the diagonal.
  intro p hp
  have h_dist_zero : dist_from_diagonal p = 0 := by
    -- By the lemma dist_from_diagonal_le_A_seq, this implies that the distance of p from the diagonal is less than or equal to the distance of A_seq n from the diagonal.
    have h_dist_le : ∀ n, dist_from_diagonal p ≤ dist_from_diagonal (A_seq n) := by
      exact fun n => dist_from_diagonal_le_A_seq n p <| Set.mem_iInter.mp hp n;
    have h_dist_zero : Filter.Tendsto (fun n => dist_from_diagonal (A_seq n)) Filter.atTop (nhds 0) := by
      exact squeeze_zero ( fun n => abs_nonneg _ ) ( fun n => dist_from_diagonal_bound n ) ( by simpa using tendsto_pow_atTop_nhds_zero_of_lt_one ( by exact div_nonneg ( sub_nonneg.mpr <| Real.sqrt_le_iff.mpr <| by norm_num ) zero_le_two ) ( show ( 2 - Real.sqrt 3 ) / 2 < 1 by nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt <| show 0 ≤ 3 by norm_num ] ) |> Filter.Tendsto.mul_const _ );
    exact le_antisymm ( le_of_tendsto_of_tendsto' tendsto_const_nhds h_dist_zero h_dist_le ) ( abs_nonneg _ );
  exact dist_from_diagonal_eq_zero_implies_on_segment p ( Set.mem_iInter.mp hp 0 ) h_dist_zero

/-
The intersection of the sequence of parallelograms is exactly the segment connecting O and O'.
-/
lemma Inter_Parallelogram_seq_eq_segment_O_O_prime : (⋂ n, Parallelogram_seq n) = segment ℝ O_point O_prime := by
  exact Set.Subset.antisymm ( inter_Parallelogram_seq_subset_segment_O_O_prime ) ( segment_O_O_prime_subset_inter_Parallelogram_seq )

/-
If an open interval (a, b) of length 1 is contained in [0, d] where d < 2, then it intersects (0, 1).
-/
lemma interval_intersection_of_length_one (d : ℝ) (hd : d < 2) (a b : ℝ) (hab : b - a = 1) (h_subset : Set.Ioo a b ⊆ Set.Icc 0 d) : (Set.Ioo 0 1 ∩ Set.Ioo a b).Nonempty := by
  have h_lower : 0 ≤ a := by
    have h_lower : Filter.Tendsto (fun n : ℕ => a + (1 / (n + 2))) Filter.atTop (nhds a) := by
      exact le_trans ( tendsto_const_nhds.add ( tendsto_const_nhds.div_atTop ( Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) ) ) ( by norm_num );
    exact le_of_tendsto_of_tendsto tendsto_const_nhds h_lower ( Filter.eventually_atTop.mpr ⟨ 0, fun n hn => h_subset ⟨ by linarith [ show ( 1 : ℝ ) / ( n + 2 ) > 0 by positivity ], by linarith [ show ( 1 : ℝ ) / ( n + 2 ) < 1 by rw [ div_lt_iff₀ ] <;> linarith ] ⟩ |>.1 ⟩ )
  have h_upper : b ≤ d := by
    have h_upper : ∀ x ∈ Set.Ioo a b, x ≤ d := by
      exact fun x hx => h_subset hx |>.2;
    contrapose! h_upper;
    exact ⟨ ( d + b ) / 2, ⟨ by linarith [ Set.mem_Icc.mp ( h_subset ( show ( a + ( b - a ) / 2 ) ∈ Ioo a b from ⟨ by linarith, by linarith ⟩ ) ) ], by linarith ⟩, by linarith ⟩
  have h_a_lt_one : a < 1 := by
    linarith;
  exact ⟨ ( a + 1 ) / 2, ⟨ by linarith, by linarith ⟩, ⟨ by linarith, by linarith ⟩ ⟩

/-
For any two points p and q on the segment connecting O and O', the distance between p and q is equal to the absolute difference of their distances from O.
-/
lemma dist_on_segment_O_O_prime (p q : Point) (hp : p ∈ segment ℝ O_point O_prime) (hq : q ∈ segment ℝ O_point O_prime) :
  dist p q = |dist O_point p - dist O_point q| := by
    -- Points on the segment OO' are of the form $t \cdot O' + (1-t) \cdot O = t \cdot O'$ (since $O=0$).
    obtain ⟨t, ht⟩ : ∃ t : ℝ, p = t • O_prime ∧ 0 ≤ t ∧ t ≤ 1 := by
      rw [ segment_eq_image ] at hp hq;
      obtain ⟨ t, ht, rfl ⟩ := hp; exact ⟨ t, by ext i; fin_cases i <;> norm_num [ O_point, O_prime ], ht.1, ht.2 ⟩ ;
    obtain ⟨s, hs⟩ : ∃ s : ℝ, q = s • O_prime ∧ 0 ≤ s ∧ s ≤ 1 := by
      obtain ⟨ s, hs ⟩ := hq;
      rcases hs with ⟨ b, hs, hb, h₁, rfl ⟩ ; exact ⟨ b, by ext i; fin_cases i <;> norm_num [ O_point, O_prime ], hb, by linarith ⟩;
    simp +decide [ ht, hs, dist_eq_norm', EuclideanSpace.norm_eq ];
    unfold O_point O_prime; norm_num ; ring_nf;
    rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> ring_nf <;> norm_num;
    · rw [ Real.sqrt_sq, Real.sqrt_sq ] <;> nlinarith [ Real.mul_self_sqrt ( show 0 ≤ 5 by norm_num ) ];
    · nlinarith [ sq_nonneg ( s - t ) ]

/-
The distance from O is injective on the segment connecting O and O'.
-/
lemma dist_O_injective_on_segment : ∀ p q, p ∈ segment ℝ O_point O_prime → q ∈ segment ℝ O_point O_prime → dist O_point p = dist O_point q → p = q := by
  intro p q hp hq h_eq
  have h_dist : dist p q = |dist O_point p - dist O_point q| := by
    exact dist_on_segment_O_O_prime p q hp hq;
  simp_all +decide [ dist_comm ]

/-
The distance from O is linear on the segment connecting O and O'.
-/
lemma dist_O_linear_on_segment (x y : Point) (hx : x ∈ segment ℝ O_point O_prime) (hy : y ∈ segment ℝ O_point O_prime) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
  dist O_point ((1 - t) • x + t • y) = (1 - t) * dist O_point x + t * dist O_point y := by
    -- By definition of $O_prime$, we know that $x$ and $y$ can be written as $x = k_x O'$ and $y = k_y O'$ for some $k_x, k_y \geq 0$.
    obtain ⟨k_x, hk_x⟩ : ∃ k_x : ℝ, x = k_x • O_prime ∧ 0 ≤ k_x := by
      obtain ⟨ a, b, ha, hb, hab, rfl ⟩ := hx;
      exact ⟨ b, by ext i; fin_cases i <;> norm_num [ O_point, O_prime ], hb ⟩
    obtain ⟨k_y, hk_y⟩ : ∃ k_y : ℝ, y = k_y • O_prime ∧ 0 ≤ k_y := by
      norm_num [ segment_eq_image ] at hy;
      rcases hy with ⟨ k, ⟨ hk₀, hk₁ ⟩, rfl ⟩ ; exact ⟨ k, by ext i; fin_cases i <;> norm_num [ O_point, O_prime ], hk₀ ⟩ ;
    simp_all +decide [ EuclideanSpace.norm_eq, dist_eq_norm ];
    unfold O_point O_prime; norm_num ; ring_nf;
    rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> ring_nf;
    · norm_num [ hk_x.2, hk_y.2 ] ; ring_nf;
      norm_num ; ring;
    · nlinarith [ sq_nonneg ( k_x - k_y ), mul_nonneg ht.1 hk_x.2, mul_nonneg ht.1 hk_y.2, mul_le_mul_of_nonneg_left ht.2 hk_x.2, mul_le_mul_of_nonneg_left ht.2 hk_y.2 ];
    · norm_num [ Real.sqrt_mul ( sq_nonneg _ ), Real.sqrt_sq_eq_abs ];
      cases abs_cases k_x <;> cases abs_cases k_y <;> nlinarith [ show 0 ≤ t * ( Real.sqrt 5 / 2 ) by exact mul_nonneg ht.1 ( by positivity ), show 0 ≤ |k_x| * ( Real.sqrt 5 / 2 ) by positivity, show 0 ≤ |k_y| * ( Real.sqrt 5 / 2 ) by positivity ]

/-
The image of the open segment between two distinct points on the segment connecting O and O' under the distance from O is the open interval between their distances from O.
-/
lemma image_dist_O_openSegment (x y : Point) (hx : x ∈ segment ℝ O_point O_prime) (hy : y ∈ segment ℝ O_point O_prime) (hxy : x ≠ y) :
  dist O_point '' (openSegment ℝ x y) = Set.Ioo (min (dist O_point x) (dist O_point y)) (max (dist O_point x) (dist O_point y)) := by
    have h_dist_O_injective_on_segment : ∀ x y : Point, x ∈ segment ℝ O_point O_prime → y ∈ segment ℝ O_point O_prime → x ≠ y → dist O_point x ≠ dist O_point y := by
      exact fun x y hx hy hxy => fun h => hxy <| dist_O_injective_on_segment x y hx hy h;
    apply Set.eq_of_subset_of_subset;
    · intro hz
      obtain ⟨t, ht⟩ := hz;
      rintro ⟨ z, ⟨ a, b, ha, hb, hab, rfl ⟩, hz ⟩;
      have h_dist_O_linear_on_segment : dist O_point (a • x + b • y) = (1 - b) * dist O_point x + b * dist O_point y := by
        convert dist_O_linear_on_segment x y hx hy b ⟨ hb.le, by linarith ⟩ using 1 ; rw [ ← eq_sub_iff_add_eq' ] at hab ; subst_vars ; ring_nf;
      cases le_total ( dist O_point x ) ( dist O_point y ) <;> simp_all +decide [ ← eq_sub_iff_add_eq' ] <;> first | exact ⟨ by nlinarith [ mul_self_pos.2 ( sub_ne_zero.2 <| h_dist_O_injective_on_segment x y hx hy hxy ) ], by nlinarith [ mul_self_pos.2 ( sub_ne_zero.2 <| h_dist_O_injective_on_segment x y hx hy hxy ) ] ⟩ | unreachable!;
    · intro z hz;
      -- By definition of $openSegment$, there exists $t \in (0, 1)$ such that $z = (1 - t) * dist O_point x + t * dist O_point y$.
      obtain ⟨t, ht⟩ : ∃ t ∈ Set.Ioo (0 : ℝ) 1, z = (1 - t) * dist O_point x + t * dist O_point y := by
        cases le_total ( dist O_point x ) ( dist O_point y ) <;> simp_all +decide;
        · exact ⟨ ( z - dist O_point x ) / ( dist O_point y - dist O_point x ), ⟨ div_pos ( by linarith ) ( by linarith ), by rw [ div_lt_iff₀ ] <;> linarith ⟩, by linarith [ mul_div_cancel₀ ( z - dist O_point x ) ( sub_ne_zero_of_ne <| Ne.symm <| h_dist_O_injective_on_segment x y hx hy hxy ) ] ⟩;
        · exact ⟨ ( z - dist O_point x ) / ( dist O_point y - dist O_point x ), ⟨ by nlinarith [ mul_div_cancel₀ ( z - dist O_point x ) ( sub_ne_zero_of_ne <| Ne.symm <| h_dist_O_injective_on_segment x y hx hy hxy ) ], by nlinarith [ mul_div_cancel₀ ( z - dist O_point x ) ( sub_ne_zero_of_ne <| Ne.symm <| h_dist_O_injective_on_segment x y hx hy hxy ) ] ⟩, by linarith [ mul_div_cancel₀ ( z - dist O_point x ) ( sub_ne_zero_of_ne <| Ne.symm <| h_dist_O_injective_on_segment x y hx hy hxy ) ] ⟩;
      use (1 - t) • x + t • y;
      rw [ openSegment_eq_image ];
      exact ⟨ ⟨ t, ht.1, rfl ⟩, by rw [ ht.2, dist_O_linear_on_segment x y hx hy t ⟨ ht.1.1.le, ht.1.2.le ⟩ ] ⟩

/-
The distance between O and O' is strictly less than 2.
-/
lemma dist_O_O_prime_lt_two : dist O_point O_prime < 2 := by
  norm_num [ dist_eq_norm, EuclideanSpace.norm_eq, O_point, O_prime ] at * ; nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ;

/-
If an open segment is contained in the segment connecting O and O', then its endpoints are also in the segment connecting O and O'.
-/
lemma endpoints_in_segment_of_subset (x y : Point) (h : openSegment ℝ x y ⊆ segment ℝ O_point O_prime) : x ∈ segment ℝ O_point O_prime ∧ y ∈ segment ℝ O_point O_prime := by
  -- Since the open Segment is a subset of the segment, and the segment is closed, the closure of the open Segment is also contained in the segment.
  have h_closure : closure (openSegment ℝ x y) ⊆ segment ℝ O_point O_prime := by
    -- Since the segment is closed, its closure is itself.
    have h_closed : IsClosed (segment ℝ O_point O_prime) := by
      -- The segment between two points is the continuous image of the closed interval [0, 1], which is compact.
      have h_compact : IsCompact (segment ℝ O_point O_prime) := by
        rw [ segment_eq_image ];
        exact CompactIccSpace.isCompact_Icc.image ( Continuous.add ( continuous_const.sub continuous_id' |> Continuous.smul <| continuous_const ) ( continuous_id'.smul <| continuous_const ) );
      exact h_compact.isClosed;
    exact h_closed.closure_subset_iff.mpr h;
  refine' ⟨ h_closure _, h_closure _ ⟩;
  · by_cases hx : x = y <;> simp_all +decide [ segment_eq_image ];
    exact ⟨ 0, by norm_num ⟩;
  · rw [ closure_openSegment ];
    exact right_mem_segment _ _ _

/-
The image of the open segment between two distinct points on the segment connecting O and O' under the distance from O is the open interval between their distances from O.
-/
lemma image_dist_O_openSegment_v2 (x y : Point) (hx : x ∈ segment ℝ O_point O_prime) (hy : y ∈ segment ℝ O_point O_prime) (hxy : x ≠ y) :
  dist O_point '' (openSegment ℝ x y) = Set.Ioo (min (dist O_point x) (dist O_point y)) (max (dist O_point x) (dist O_point y)) := by
    convert image_dist_O_openSegment x y hx hy hxy using 1

/-
The image of a unit segment contained in the segment connecting O and O' under the distance from O is an open interval of length 1.
-/
lemma image_dist_O_is_interval_of_length_one (L : Set Point) (hL : IsUnitSegment L) (hL_sub : L ⊆ segment ℝ O_point O_prime) :
  ∃ a b, dist O_point '' L = Set.Ioo a b ∧ b - a = 1 := by
    -- Since L is a unit segment, it must be the open segment between two points x and y on the segment connecting O and O'.
    obtain ⟨x, y, hx, hy, hxy⟩ : ∃ x y : Point, x ∈ segment ℝ O_point O_prime ∧ y ∈ segment ℝ O_point O_prime ∧ L = openSegment ℝ x y ∧ dist x y = 1 := by
      obtain ⟨ x, y, hxy ⟩ := hL;
      have := endpoints_in_segment_of_subset x y ?_ <;> aesop;
    -- By `image_dist_O_openSegment_v2`, `dist O '' L = Ioo (min (dist O x) (dist O y)) (max (dist O x) (dist O y))`.
    obtain ⟨a, b, hab⟩ : ∃ a b : ℝ, dist O_point '' L = Set.Ioo a b ∧ b - a = |dist O_point x - dist O_point y| := by
      have h_image : dist O_point '' L = Set.Ioo (min (dist O_point x) (dist O_point y)) (max (dist O_point x) (dist O_point y)) := by
        convert image_dist_O_openSegment_v2 x y hx hy _ using 1 ; aesop;
        rintro rfl; norm_num at hxy;
      cases le_total ( dist O_point x ) ( dist O_point y ) <;> simp +decide [ *, abs_of_nonneg, abs_of_nonpos ];
      · grind;
      · aesop;
    -- By `dist_on_segment_O_O_prime`, `|dist O x - dist O y| = dist x y = 1`.
    have h_dist_eq : |dist O_point x - dist O_point y| = dist x y := by
      exact Eq.symm (dist_on_segment_O_O_prime x y hx hy);
    grind

/-
If a point p is on the segment connecting O and O' and its distance from O is strictly between 0 and 1, then p is in S_inf.
-/
lemma mem_S_inf_of_mem_segment_and_dist (p : Point) (hp : p ∈ segment ℝ O_point O_prime) (h_pos : 0 < dist O_point p) (h_lt : dist O_point p < 1) : p ∈ S_inf := by
  -- Since $p$ is on the segment connecting $O$ and $O'$ and its distance from $O$ is strictly between $0$ and $1$, $p$ must lie on the segment connecting $O$ and $A_{\text{inf}}$.
  have h_segment : p ∈ segment ℝ O_point A_inf := by
    -- Since $p$ is on the segment connecting $O$ and $O'$ and its distance from $O$ is strictly between $0$ and $1$, $p$ must lie on the segment connecting $O$ and $A_{\text{inf}}$ by the properties of the segment.
    have h_segment : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ p = (1 - t) • O_point + t • O_prime := by
      rw [ segment_eq_image ] at hp; aesop;
    obtain ⟨ t, ht₀, ht₁, rfl ⟩ := h_segment;
    -- Since $t \leq \frac{2}{\sqrt{5}}$, we can write $t = s \cdot \frac{2}{\sqrt{5}}$ for some $s \in [0, 1]$.
    obtain ⟨ s, hs₀, hs₁ ⟩ : ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ t = s * (2 / Real.sqrt 5) := by
      refine' ⟨ t / ( 2 / Real.sqrt 5 ), _, _, _ ⟩ <;> norm_num;
      · positivity;
      · rw [ dist_eq_norm, EuclideanSpace.norm_eq ] at * ; norm_num at *;
        rw [ Real.sqrt_lt' ] at h_lt <;> norm_num [ O_point, O_prime ] at * ; nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
    use 1 - s, s, by linarith, by linarith, by
      ring;
    ext i ; fin_cases i <;> norm_num [ hs₁, O_point, O_prime, A_inf ] ; ring;
  rw [ segment_eq_image ] at *;
  rcases h_segment with ⟨ θ, ⟨ hθ₀, hθ₁ ⟩, rfl ⟩ ; simp_all +decide [ S_inf ] ;
  refine' ⟨ 1 - θ, θ, _, _, _ ⟩ <;> norm_num [ EuclideanSpace.norm_eq ] at *;
  · contrapose! h_lt;
    norm_num [ show θ = 1 by linarith, dist_eq_norm ];
    norm_num [ EuclideanSpace.norm_eq, O_point, A_inf ];
    norm_num [ div_pow ];
  · exact hθ₀.lt_of_ne' fun h => h_pos <| by norm_num [ h ] ;

/-
Any unit segment contained in the segment connecting O and O' must intersect S_inf.
-/
lemma S_inf_blocks_on_segment_O_O_prime :
  ∀ L, IsUnitSegment L → L ⊆ segment ℝ O_point O_prime → ¬Disjoint L S_inf := by
    -- Apply the interval intersection lemma to get the existence of `r`.
    intros L hL hL_subset
    obtain ⟨a, b, hab⟩ : ∃ a b : ℝ, dist O_point '' L = Set.Ioo a b ∧ b - a = 1 := by
      exact image_dist_O_is_interval_of_length_one L hL hL_subset;
    -- By `interval_intersection_of_length_one`, there exists $r \in (0, 1) \cap (a, b)$.
    obtain ⟨r, hr⟩ : ∃ r : ℝ, r ∈ Set.Ioo 0 1 ∧ r ∈ Set.Ioo a b := by
      have h_interval : Set.Ioo a b ⊆ Set.Icc 0 (dist O_point O_prime) := by
        intro x hxaesop;
        obtain ⟨ y, hy, rfl ⟩ := hab.1.symm.subset hxaesop;
        have := hL_subset hy;
        exact ⟨ dist_nonneg, by rcases this with ⟨ u, v, hu, hv, huv, rfl ⟩ ; exact (by
        norm_num [ show u = 1 - v by linarith, dist_eq_norm ];
        rw [ show O_point - ( ( 1 - v ) • O_point + v • O_prime ) = v • ( O_point - O_prime ) by ext i; fin_cases i <;> norm_num <;> ring ] ; rw [ norm_smul, Real.norm_of_nonneg hv ] ; exact mul_le_of_le_one_left ( norm_nonneg _ ) ( by linarith ) ;) ⟩;
      have h_interval_length : dist O_point O_prime < 2 := by
        exact dist_O_O_prime_lt_two;
      apply interval_intersection_of_length_one;
      exacts [ h_interval_length, hab.2, h_interval ];
    -- Since $r \in (a, b) = dist O '' L$, there exists $p \in L$ such that $dist O p = r$.
    obtain ⟨p, hp⟩ : ∃ p ∈ L, dist O_point p = r := by
      exact hab.1.symm.subset hr.2;
    exact Set.not_disjoint_iff_nonempty_inter.mpr ⟨ p, hp.1, mem_S_inf_of_mem_segment_and_dist p ( hL_subset hp.1 ) ( by linarith [ hr.1.1 ] ) ( by linarith [ hr.1.2 ] ) ⟩

/-
The reflection of A_{n+1} lies on the segment connecting O and A_n.
-/
lemma reflection_A_seq_next_mem_segment_O_A_seq (n : ℕ) :
  reflection (A_seq (n + 1)) ∈ segment ℝ O_point (A_seq n) := by
    -- By definition of $A_{n+1}$, we know that $A_{n+1} \in \text{openSegment} \, \mathbb{R} \, O' \, A'_n$.
    have h_A_n1_in_openSegment : A_seq (n + 1) ∈ openSegment ℝ O_prime (reflection (A_seq n)) := by
      exact A_seq_between n;
    rw [ openSegment_eq_image ] at h_A_n1_in_openSegment;
    obtain ⟨ θ, hθ, h ⟩ := h_A_n1_in_openSegment; simp_all +decide [ reflection, segment_eq_image ] ;
    refine' ⟨ θ, ⟨ hθ.1.le, hθ.2.le ⟩, _ ⟩ ; rw [ ← h ] ; ext i ; fin_cases i <;> norm_num [ O_prime, O_point ];
    · ring!;
    · ring!

/-
If a point E lies on the segment BC, then the convex hull of {A, B, C} is contained in the union of the convex hulls of {A, B, E} and {A, E, C}.
-/
lemma convex_hull_split_triangle (A B C : Point) (E : Point) (hE : E ∈ segment ℝ B C) :
  convexHull ℝ {A, B, C} ⊆ convexHull ℝ {A, B, E} ∪ convexHull ℝ {A, E, C} := by
    norm_num [ convexHull_insert ] at *;
    intro x hx hi; rw [ segment_eq_image ] at *;
    rintro ⟨ θ, ⟨ hθ₀, hθ₁ ⟩, rfl ⟩ ; rcases hE with ⟨ θ', ⟨ hθ'₀, hθ'₁ ⟩, rfl ⟩ ; rcases hx with ⟨ θ'', ⟨ hθ''₀, hθ''₁ ⟩, rfl ⟩ ; simp +decide [ segment_eq_image ] ;
    by_cases hθ''_le : θ'' ≤ θ';
    · refine' Or.inl ⟨ θ'' / θ', _, θ, _, _ ⟩;
      · exact ⟨ div_nonneg hθ''₀ hθ'₀, div_le_one_of_le₀ hθ''_le hθ'₀ ⟩;
      · grind;
      · by_cases h : θ' = 0 <;> simp_all +decide [ div_eq_inv_mul ];
        · norm_num [ show θ'' = 0 by linarith ];
        · ext i ; norm_num ; ring_nf;
          norm_num [ h ];
    · refine Or.inr ⟨ ( θ'' - θ' ) / ( 1 - θ' ), ⟨ by nlinarith [ mul_div_cancel₀ ( θ'' - θ' ) ( by linarith : ( 1 - θ' ) ≠ 0 ) ], by nlinarith [ mul_div_cancel₀ ( θ'' - θ' ) ( by linarith : ( 1 - θ' ) ≠ 0 ) ] ⟩, θ, ⟨ by linarith, by linarith ⟩, ?_ ⟩ ; ext ; norm_num ; ring_nf;
      grind

/-
The reflected triangle is the convex hull of O', A_n, and the reflection of A_{n+1}.
-/
lemma Triangle_seq_refl_eq_convexHull (n : ℕ) :
  Triangle_seq_refl n = convexHull ℝ {O_prime, A_seq n, reflection (A_seq (n + 1))} := by
    refine' Set.ext fun x => ⟨ _, _ ⟩ <;> intro hx;
    · obtain ⟨ y, hy, rfl ⟩ := hx;
      -- By definition of $Triangle\_OA\_prime\_P$, we know that $y$ is in the convex hull of $\{O\_point, reflection (A\_seq n), A\_seq (n + 1)\}$.
      have hy_convex : y ∈ convexHull ℝ {O_point, reflection (A_seq n), A_seq (n + 1)} := by
        exact hy;
      -- By definition of $Triangle\_OA\_prime\_P$, we know that $y$ is in the convex hull of $\{O\_point, reflection (A\_seq n), A\_seq (n + 1)\}$, so we can write $y$ as a convex combination of these points.
      obtain ⟨a, b, c, ha, hb, hc, habc⟩ : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ y = a • O_point + b • reflection (A_seq n) + c • A_seq (n + 1) := by
        rw [ convexHull_insert ] at hy_convex;
        · norm_num [ segment_eq_image ] at hy_convex;
          rcases hy_convex with ⟨ i, hi, x, hx, rfl ⟩ ; exact ⟨ 1 - x, x * ( 1 - i ), x * i, by linarith, by nlinarith, by nlinarith, by linarith, by ext ; simpa using by ring ⟩ ;
        · norm_num;
      -- By definition of $reflection$, we know that $reflection y = a • reflection O_point + b • reflection (reflection (A_seq n)) + c • reflection (A_seq (n + 1))$.
      have h_reflection_y : reflection y = a • reflection O_point + b • reflection (reflection (A_seq n)) + c • reflection (A_seq (n + 1)) := by
        unfold reflection; ext i; fin_cases i <;> norm_num [ habc ] ;
        · unfold reflection; norm_num; linarith;
        · unfold reflection; norm_num; ring_nf;
          rw [ show O_point 1 = 0 by rfl ] ; rw [ show A_seq n 1 = A_seq n 1 by rfl ] ; rw [ show A_seq ( 1 + n ) 1 = A_seq ( n + 1 ) 1 by ring_nf ] ; rw [ ← eq_sub_iff_add_eq' ] at habc ; linarith;
      rw [ h_reflection_y, convexHull_eq ];
      refine' ⟨ Fin 3, { 0, 1, 2 }, fun i => if i = 0 then a else if i = 1 then b else c, fun i => if i = 0 then reflection O_point else if i = 1 then reflection ( reflection ( A_seq n ) ) else reflection ( A_seq ( n + 1 ) ), _, _, _, _ ⟩ <;> simp +decide [ *, Finset.centerMass ];
      · linarith;
      · exact ⟨ Or.inl <| O_prime_reflection_O, Or.inr <| Or.inl <| reflection_involution _ ⟩;
      · norm_num [ ← add_assoc, habc.1 ];
    · -- By definition of $Triangle_seq_refl$, we know that $x$ is in the image of the convex hull of $\{O, A'_n, A_{n+1}\}$ under the reflection map.
      obtain ⟨y, hy⟩ : ∃ y ∈ convexHull ℝ {O_point, reflection (A_seq n), A_seq (n + 1)}, reflection y = x := by
        simp_all +decide [ convexHull_insert ];
        rcases hx with ⟨ y, hy, hx ⟩;
        refine' ⟨ reflection x, _, _ ⟩ <;> simp_all +decide [ segment_eq_image ];
        · rcases hy with ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; rcases hx with ⟨ b, ⟨ hb₁, hb₂ ⟩, rfl ⟩ ; use a, ⟨ ha₁, ha₂ ⟩, b, ⟨ hb₁, hb₂ ⟩ ; ext i ; norm_num [ reflection ] ; ring_nf;
          fin_cases i <;> norm_num [ O_point, O_prime ] <;> ring_nf;
          · rfl;
          · rfl;
        · exact reflection_involution x;
      exact Set.mem_image_of_mem _ hy.1 |> fun h => hy.2 ▸ h

/-
The triangle O O' A'_n splits into Triangle_OA_prime_P n and O O' A_{n+1}.
-/
lemma Triangle_split_1 (n : ℕ) : convexHull ℝ {O_point, O_prime, reflection (A_seq n)} = Triangle_OA_prime_P n ∪ convexHull ℝ {O_point, O_prime, A_seq (n + 1)} := by
  have h_convex_hull_split : convexHull ℝ {O_point, O_prime, reflection (A_seq n)} = convexHull ℝ {O_point, A_seq (n + 1), reflection (A_seq n)} ∪ convexHull ℝ {O_point, O_prime, A_seq (n + 1)} := by
    apply Set.Subset.antisymm _;
    · refine' Set.union_subset _ _;
      · refine' convexHull_min _ _;
        · norm_num [ Set.insert_subset_iff, convexHull_insert ];
          refine' ⟨ ⟨ O_prime, _, _ ⟩, ⟨ A_seq ( n + 1 ), _, _ ⟩, ⟨ reflection ( A_seq n ), _, _ ⟩ ⟩ <;> norm_num [ segment_eq_image ];
          exact ⟨ 0, by norm_num ⟩;
          · exact ⟨ 0, by norm_num ⟩;
          · have := A_seq_mem_closed_segment n;
            rw [ segment_eq_image ] at this ; aesop;
          · exact ⟨ 1, by norm_num ⟩;
          · exact ⟨ 1, by norm_num ⟩;
          · exact ⟨ 1, by norm_num ⟩;
        · exact convex_convexHull ℝ _;
      · refine' convexHull_min _ _;
        · simp +decide [ Set.insert_subset_iff ];
          refine' ⟨ subset_convexHull ℝ _ ( Set.mem_insert _ _ ), subset_convexHull ℝ _ ( Set.mem_insert_of_mem _ ( Set.mem_insert _ _ ) ), _ ⟩;
          -- By definition of $A_{n+1}$, we know that it lies on the segment $O' A'_n$.
          have h_A_seq_next_on_segment : A_seq (n + 1) ∈ segment ℝ O_prime (reflection (A_seq n)) := by
            exact A_seq_mem_closed_segment n;
          rw [ convexHull_eq ];
          rcases h_A_seq_next_on_segment with ⟨ a, b, ha, hb, hab, h ⟩;
          refine' ⟨ Fin 2, { 0, 1 }, fun i => if i = 0 then a else b, fun i => if i = 0 then O_prime else reflection ( A_seq n ), _, _, _, _ ⟩ <;> simp +decide [ *, Finset.centerMass ];
        · exact convex_convexHull ℝ _;
    · have h_convex_hull_split : A_seq (n + 1) ∈ segment ℝ O_prime (reflection (A_seq n)) := by
        exact A_seq_mem_closed_segment n;
      apply convex_hull_split_triangle O_point O_prime ( reflection ( A_seq n ) ) ( A_seq ( n + 1 ) ) h_convex_hull_split |> Set.Subset.trans <| Set.union_subset_union ( Set.Subset.refl _ ) ( Set.Subset.refl _ ) |> Set.Subset.trans <| by aesop_cat;
  -- By definition of Triangle_OA_prime_P, we have Triangle_OA_prime_P n = convexHull ℝ {O_point, reflection (A_seq n), A_seq (n + 1)}.
  rw [show Triangle_OA_prime_P n = convexHull ℝ {O_point, reflection (A_seq n), A_seq (n + 1)} from rfl];
  simpa only [ Set.pair_comm, Set.insert_comm ] using h_convex_hull_split

/-
The triangle O A_n O' splits into Triangle_seq_refl n and O A'_{n+1} O'.
-/
lemma Triangle_split_2 (n : ℕ) : convexHull ℝ {O_point, A_seq n, O_prime} = Triangle_seq_refl n ∪ convexHull ℝ {O_point, reflection (A_seq (n + 1)), O_prime} := by
  -- Applying the convexHull_split_triangle lemma with A = O', B = A_n, C = O, and E = reflection (A_seq (n + 1)).
  have h_split : convexHull ℝ {O_prime, A_seq n, O_point} = convexHull ℝ {O_prime, reflection (A_seq (n + 1)), O_point} ∪ convexHull ℝ {O_prime, A_seq n, reflection (A_seq (n + 1))} := by
    apply Set.Subset.antisymm;
    · have h_split : convexHull ℝ {O_prime, A_seq n, O_point} ⊆ convexHull ℝ {O_prime, reflection (A_seq (n + 1)), O_point} ∪ convexHull ℝ {O_prime, A_seq n, reflection (A_seq (n + 1))} := by
        have h_E : reflection (A_seq (n + 1)) ∈ segment ℝ O_point (A_seq n) := by
          exact reflection_A_seq_next_mem_segment_O_A_seq n
        convert convex_hull_split_triangle O_prime O_point ( A_seq n ) ( reflection ( A_seq ( n + 1 ) ) ) h_E using 1;
        · simp +decide only [pair_comm];
        · simp +decide [ Set.union_comm, convexHull_insert ];
          simp +decide [ segment_symm, Set.union_comm ];
      assumption;
    · norm_num [ Set.insert_subset_iff, convexHull_union ];
      constructor <;> refine' convexHull_min _ _;
      · norm_num [ Set.insert_subset_iff, convexHull_pair ];
        refine' ⟨ subset_convexHull ℝ _ ( Set.mem_insert _ _ ), _, subset_convexHull ℝ _ ( Set.mem_insert_of_mem _ ( Set.mem_insert_of_mem _ ( Set.mem_singleton _ ) ) ) ⟩;
        rw [ convexHull_insert ] <;> norm_num;
        refine' ⟨ reflection ( A_seq ( n + 1 ) ), _, _ ⟩;
        · convert reflection_A_seq_next_mem_segment_O_A_seq n using 1;
          exact segment_symm ℝ (A_seq n) O_point;
        · exact right_mem_segment _ _ _;
      · exact convex_convexHull ℝ _;
      · norm_num [ Set.insert_subset_iff, convexHull_insert ];
        refine' ⟨ ⟨ O_point, _, _ ⟩, ⟨ A_seq n, _, _ ⟩, ⟨ reflection ( A_seq ( n + 1 ) ), _, _ ⟩ ⟩ <;> norm_num [ segment_symm ];
        exact left_mem_segment ℝ O_point (A_seq n);
        · exact right_mem_segment _ _ _;
        · exact right_mem_segment _ _ _;
        · exact right_mem_segment _ _ _;
        · exact reflection_A_seq_next_mem_segment_O_A_seq n;
        · exact right_mem_segment _ _ _;
      · exact convex_convexHull ℝ _;
  convert h_split using 1;
  · exact congr_arg _ ( by ext; simp +decide [ Set.mem_insert_iff, Set.mem_singleton_iff, or_comm, or_left_comm ] );
  · rw [ Triangle_seq_refl_eq_convexHull ];
    simp +decide [ Set.union_comm ];
    congr! 2;
    aesop

/-
The union of the two triangles formed by the diagonal O O' in the (n+1)-th parallelogram is contained in the (n+1)-th parallelogram.
-/
lemma Parallelogram_next_contains_triangles (n : ℕ) :
  convexHull ℝ {O_point, reflection (A_seq (n + 1)), O_prime} ∪ convexHull ℝ {O_point, O_prime, A_seq (n + 1)} ⊆ Parallelogram_seq (n + 1) := by
    exact Set.union_subset ( convexHull_mono <| by aesop_cat ) ( convexHull_mono <| by aesop_cat )

/-
If A + A' = O', then the parallelogram defined by O, A, O', A' is the union of the two triangles O A O' and O O' A'.
-/
lemma Parallelogram_decomposition_algebraic (A : Point) (h_sum : A + reflection A = O_prime) :
  Parallelogram A = convexHull ℝ {O_point, A, O_prime} ∪ convexHull ℝ {O_point, O_prime, reflection A} := by
    refine' Set.Subset.antisymm _ _;
    · intro x hx;
      -- By definition of $Parallelogram$, we know that $x$ can be written as $\alpha O + \beta A + \gamma O' + \delta A'$ for some $\alpha, \beta, \gamma, \delta \geq 0$ with $\alpha + \beta + \gamma + \delta = 1$.
      obtain ⟨α, β, γ, δ, hαβγδ⟩ : ∃ α β γ δ : ℝ, α ≥ 0 ∧ β ≥ 0 ∧ γ ≥ 0 ∧ δ ≥ 0 ∧ α + β + γ + δ = 1 ∧ x = α • O_point + β • A + γ • O_prime + δ • reflection A := by
        have h_convex : x ∈ convexHull ℝ {O_point, A, O_prime, reflection A} := by
          exact hx;
        rw [ convexHull_insert ] at h_convex;
        · norm_num [ segment_eq_image ] at h_convex;
          rcases h_convex with ⟨ i, hi, x_1, hx_1, rfl ⟩;
          rw [ convexHull_insert ] at hi;
          · norm_num [ segment_eq_image ] at hi;
            rcases hi with ⟨ y, hy, z, hz, rfl ⟩;
            exact ⟨ 1 - x_1, x_1 * ( 1 - z ), x_1 * z * ( 1 - y ), x_1 * z * y, by nlinarith, by nlinarith, by nlinarith [ mul_nonneg hx_1.1 hz.1 ], by nlinarith [ mul_nonneg hx_1.1 hz.1 ], by nlinarith, by ext i; norm_num; ring ⟩;
          · norm_num;
        · norm_num;
      by_cases hβδ : β ≥ δ;
      · -- Let $y = \gamma + \delta$ and $x = \beta - \delta$. Then $x, y \geq 0$.
        set x' := β - δ
        set y' := γ + δ
        have hx'_nonneg : 0 ≤ x' := by
          exact sub_nonneg_of_le hβδ
        have hy'_nonneg : 0 ≤ y' := by
          exact add_nonneg hαβγδ.2.2.1 hαβγδ.2.2.2.1;
        -- Then $x = x' A + y' O'$.
        have hx'_eq : x = x' • A + y' • O_prime := by
          ext i; simp [hαβγδ, x', y'];
          rw [ ← h_sum ] ; ring_nf;
          rw [ show O_point = 0 from by ext i; fin_cases i <;> rfl ] ; norm_num ; ring;
        -- Since $x' + y' \leq 1$, we have $x \in \text{conv}(O, A, O')$.
        have hx'_conv : x ∈ convexHull ℝ {O_point, A, O_prime} := by
          rw [ convexHull_eq ];
          refine' ⟨ Fin 3, { 0, 1, 2 }, fun i => if i = 0 then 1 - x' - y' else if i = 1 then x' else y', fun i => if i = 0 then O_point else if i = 1 then A else O_prime, _, _, _, _ ⟩ <;> simp +decide [ Finset.centerMass ];
          · exact ⟨ by linarith, hx'_nonneg, hy'_nonneg ⟩;
          · rw [ hx'_eq ] ; ext i ; norm_num ; ring_nf;
            exact Or.inr ( by fin_cases i <;> rfl );
        exact Or.inl hx'_conv;
      · -- Since $\delta > \beta$, we can write $x$ as a convex combination of $O$, $O'$, and $A'$.
        have hx_comb : x = (α + β) • O_point + (γ + β) • O_prime + (δ - β) • reflection A := by
          ext i; have := congr_fun h_sum i; norm_num at *; rw [ hαβγδ.2.2.2.2.2 ] ; ring_nf;
          rw [ show O_prime i = A i + reflection A i by rw [ ← this ] ] ; norm_num ; ring_nf;
          rw [ show O_prime i = A i + reflection A i by rw [ ← this ] ] ; ring_nf;
          fin_cases i <;> norm_num [ O_point ];
        refine' Or.inr _;
        rw [ hx_comb, convexHull_eq ];
        refine' ⟨ Fin 3, { 0, 1, 2 }, fun i => if i = 0 then α + β else if i = 1 then γ + β else δ - β, fun i => if i = 0 then O_point else if i = 1 then O_prime else reflection A, _, _, _, _ ⟩ <;> simp +decide [ *, Finset.centerMass ];
        · exact ⟨ by linarith, by linarith, by linarith ⟩;
        · linarith;
        · norm_num [ show α + β + ( γ + δ ) = 1 by linarith ];
          rw [ add_assoc ];
    · exact Set.union_subset ( convexHull_mono <| by aesop_cat ) ( convexHull_mono <| by aesop_cat )

/-
The parallelogram is the union of the two triangles formed by the diagonal O O'.
-/
lemma Parallelogram_eq_union_triangles (n : ℕ) : Parallelogram_seq n = convexHull ℝ {O_point, A_seq n, O_prime} ∪ convexHull ℝ {O_point, O_prime, reflection (A_seq n)} := by
  apply Parallelogram_decomposition_algebraic;
  ext i ; fin_cases i <;> norm_num [ reflection ];
  · exact show A_seq n 0 + ( 1 - A_seq n 0 ) = 1 by ring;
  · unfold O_prime; norm_num;
    ring!

/-
The n-th parallelogram is covered by the n-th triangle, the reflected triangle, and the (n+1)-th parallelogram.
-/
lemma Parallelogram_covered (n : ℕ) : Parallelogram_seq n ⊆ Triangle_OA_prime_P n ∪ Triangle_seq_refl n ∪ Parallelogram_seq (n + 1) := by
  -- By definition of $Parallelogram_seq$, we know that $Parallelogram_seq n = convexHull ℝ {O_point, A_seq n, O_prime} ∪ convexHull ℝ {O_point, O_prime, reflection (A_seq n)}$.
  rw [Parallelogram_eq_union_triangles];
  -- By definition of $Triangle_OA_prime_P$ and $Triangle_seq_refl$, we can rewrite the right-hand side of the inclusion.
  have h_rewrite : (convexHull ℝ {O_point, A_seq n, O_prime}) ∪ (convexHull ℝ {O_point, O_prime, reflection (A_seq n)}) = Triangle_seq_refl n ∪ convexHull ℝ {O_point, reflection (A_seq (n + 1)), O_prime} ∪ Triangle_OA_prime_P n ∪ convexHull ℝ {O_point, O_prime, A_seq (n + 1)} := by
    have h_rewrite : convexHull ℝ {O_point, A_seq n, O_prime} = Triangle_seq_refl n ∪ convexHull ℝ {O_point, reflection (A_seq (n + 1)), O_prime} ∧ convexHull ℝ {O_point, O_prime, reflection (A_seq n)} = Triangle_OA_prime_P n ∪ convexHull ℝ {O_point, O_prime, A_seq (n + 1)} := by
      apply And.intro;
      · exact Triangle_split_2 n;
      · exact Triangle_split_1 n;
    grind;
  rw [h_rewrite];
  simp +zetaDelta at *;
  exact ⟨ ⟨ ⟨ fun x hx => by aesop, fun x hx => by exact Or.inr <| by exact Parallelogram_next_contains_triangles n |> fun h => h <| by aesop ⟩, fun x hx => by aesop ⟩, fun x hx => by exact Or.inr <| by exact Parallelogram_next_contains_triangles n |> fun h => h <| by aesop ⟩

/-
If a connected set is in the union of two closed sets and disjoint from their intersection, it is in one of them.
-/
lemma connected_subset_union_disjoint_inter {α : Type*} [TopologicalSpace α] (A B L : Set α) (hA : IsClosed A) (hB : IsClosed B) (hL_conn : IsConnected L) (hL_sub : L ⊆ A ∪ B) (hL_disj : Disjoint L (A ∩ B)) : L ⊆ A ∨ L ⊆ B := by
  have h_connected : IsPreconnected L := by
    exact hL_conn.isPreconnected;
  contrapose! h_connected;
  simp_all +decide [ IsPreconnected, Set.subset_def, Set.disjoint_left ];
  refine' ⟨ ( B ) ᶜ, isOpen_compl_iff.mpr hB, ( A ) ᶜ, isOpen_compl_iff.mpr hA, _, _, _, _ ⟩ <;> simp_all +decide [ Set.Nonempty ];
  · grind +ring;
  · exact fun x hx hx' => Or.resolve_right ( hL_sub x hx ) hx'

/-
Define a linear functional that vanishes on O and A_{n+1}, and show it separates O' and A'_n.
-/
noncomputable def separating_functional (n : ℕ) : Point →L[ℝ] ℝ :=
  let x := (A_seq (n + 1)) 0
  let y := (A_seq (n + 1)) 1
  LinearMap.toContinuousLinearMap
  { toFun := fun p => -y * p 0 + x * p 1
    map_add' := by intros; simp; ring
    map_smul' := by intros; simp; ring }

lemma separating_functional_properties (n : ℕ) :
  let f := separating_functional n
  f O_point = 0 ∧ f (A_seq (n + 1)) = 0 ∧
  (f O_prime * f (reflection (A_seq n)) ≤ 0) := by
    unfold separating_functional;
    -- By definition of $A_{n+1}$, we know that $A_{n+1} = (1-t) O' + t A'_n$ for some $t \in [0, 1]$.
    obtain ⟨t, ht⟩ : ∃ t ∈ Set.Icc (0 : ℝ) 1, A_seq (n + 1) = (1 - t) • O_prime + t • reflection (A_seq n) := by
      have := A_seq_mem_closed_segment n;
      rw [ segment_eq_image ] at this; aesop;
    simp_all +decide [ O_prime, reflection ];
    unfold O_point; norm_num; ring_nf; norm_num;
    -- Since $t \in [0, 1]$, we have $t(t - 1) \leq 0$.
    have h_t_neg : t * (t - 1) ≤ 0 := by
      nlinarith;
    nlinarith [ sq_nonneg ( A_seq n 0 - A_seq n 1 * 2 ) ]

/-
The separating functional separates the triangle T_n from the parallelogram P_{n+1}.
-/
lemma separating_functional_separates (n : ℕ) :
  let f := separating_functional n
  (∀ p ∈ Triangle_OA_prime_P n, f p * f (reflection (A_seq n)) ≥ 0) ∧
  (∀ p ∈ Parallelogram_seq (n + 1), f p * f (reflection (A_seq n)) ≤ 0) := by
    field_simp;
    constructor;
    · intro p hp
      obtain ⟨α, β, γ, hα, hβ, hγ, hp_eq⟩ : ∃ α β γ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α + β + γ = 1 ∧ p = α • O_point + β • A_seq (n + 1) + γ • reflection (A_seq n) := by
        unfold Triangle_OA_prime_P at hp;
        rw [ convexHull_insert ] at hp;
        · norm_num [ segment_eq_image ] at hp;
          rcases hp with ⟨ i, hi, x, hx, rfl ⟩ ; exact ⟨ 1 - x, x * i, x * ( 1 - i ), by nlinarith, by nlinarith, by nlinarith, by nlinarith, by ext ; simpa using by ring ⟩ ;
        · norm_num;
      have h_f_p : (separating_functional n) p = γ * (separating_functional n) (reflection (A_seq n)) := by
        have := separating_functional_properties n; aesop;
      rw [ h_f_p ] ; nlinarith [ mul_nonneg hγ ( sq_nonneg ( ( separating_functional n ) ( reflection ( A_seq n ) ) ) ) ] ;
    · -- For $P_{n+1} = \text{conv}(O, A_{n+1}, O', A'_{n+1})$.
      intro p hp
      have hP : p ∈ convexHull ℝ {O_point, A_seq (n + 1), O_prime, reflection (A_seq (n + 1))} := by
        exact hp;
      -- Since $p \in \text{conv}(O, A_{n+1}, O', A'_{n+1})$, we can write $p$ as a convex combination of these points.
      obtain ⟨α, β, γ, δ, hαβγδ, hp⟩ : ∃ α β γ δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧ α + β + γ + δ = 1 ∧ p = α • O_point + β • A_seq (n + 1) + γ • O_prime + δ • reflection (A_seq (n + 1)) := by
        rw [ convexHull_insert ] at hP;
        · norm_num [ segment_eq_image ] at hP;
          rcases hP with ⟨ i, hi, x, hx, rfl ⟩;
          rw [ convexHull_insert ] at hi;
          · norm_num [ segment_eq_image ] at hi;
            rcases hi with ⟨ y, hy, z, hz, rfl ⟩;
            exact ⟨ 1 - x, x * ( 1 - z ), x * z * ( 1 - y ), x * z * y, by nlinarith, by nlinarith [ mul_nonneg hx.1 hz.1 ], by nlinarith [ mul_nonneg hx.1 hz.1 ], by nlinarith [ mul_nonneg hx.1 hz.1 ], by nlinarith, by ext i; norm_num; ring ⟩;
          · norm_num;
        · norm_num;
      -- Substitute the values of the separating functional at the vertices.
      have h_values : (separating_functional n) O_point = 0 ∧ (separating_functional n) (A_seq (n + 1)) = 0 ∧ (separating_functional n) O_prime * (separating_functional n) (reflection (A_seq n)) ≤ 0 ∧ (separating_functional n) (reflection (A_seq (n + 1))) * (separating_functional n) (reflection (A_seq n)) ≤ 0 := by
        have := separating_functional_properties n;
        -- Since $A_{n+1}$ is in the segment $[O', A'_n]$, we have $A_{n+1} + reflection (A_{n+1}) = O'$.
        have h_sum : A_seq (n + 1) + reflection (A_seq (n + 1)) = O_prime := by
          ext i; fin_cases i <;> norm_num [ reflection ] ; ring_nf;
          · exact show 1 + ( A_seq ( 1 + n ) 0 - A_seq ( 1 + n ) 0 ) = 1 by ring;
          · exact show A_seq ( n + 1 ) 1 + ( 1 / 2 - A_seq ( n + 1 ) 1 ) = 1 / 2 by ring;
        have h_values : (separating_functional n) (A_seq (n + 1)) + (separating_functional n) (reflection (A_seq (n + 1))) = (separating_functional n) O_prime := by
          rw [ ← map_add, h_sum ];
        aesop;
      rw [ hp.2.2.2.2 ] ; simp_all +decide [ mul_comm ] ;
      nlinarith [ mul_nonneg hp.2.1 hp.2.2.1 ]

/-
The distance of A_n from the diagonal is strictly decreasing.
-/
lemma dist_from_diagonal_strict_decreasing (n : ℕ) : dist_from_diagonal (A_seq (n + 1)) < dist_from_diagonal (A_seq n) := by
  -- By definition of $A_seq$, we know that $A_seq (n + 1)$ is strictly between $O'$ and $A'_n$.
  have h_between : dist_from_diagonal (A_seq (n + 1)) ≤ ((2 - Real.sqrt 3) / 2) * dist_from_diagonal (A_seq n) := by
    exact dist_from_diagonal_recurrence n;
  -- Since $A_seq n$ is in the closed region $[0,1] \times [0,1/2]$, its distance from the diagonal $x - 2y = 0$ is positive.
  have h_pos : 0 < dist_from_diagonal (A_seq n) := by
    -- Since $A_n$ is in the closed region $[0,1] \times [0,1/2]$ and $A_n \neq O'$, its distance from the diagonal $x - 2y = 0$ is positive.
    have h_pos : ∀ n, dist_from_diagonal (A_seq n) > 0 := by
      intro n
      have h_pos : (A_seq n) 0 - 2 * (A_seq n) 1 ≠ 0 := by
        induction' n with n ih;
        · exact show ( 1 : ℝ ) - 2 * 0 ≠ 0 by norm_num;
        · have h_pos : A_seq (n + 1) ∈ openSegment ℝ O_prime (reflection (A_seq n)) := by
            exact A_seq_between n;
          obtain ⟨ t, ht₀, ht₁, ht₂ ⟩ := h_pos;
          simp_all +decide [ ← ht₂.2.2, reflection ];
          unfold O_prime; norm_num; cases lt_or_gt_of_ne ih <;> nlinarith;
      exact abs_pos.mpr h_pos;
    exact h_pos n;
  exact h_between.trans_lt ( mul_lt_of_lt_one_left h_pos ( by nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ) ] ) )

/-
The vertices A_n are all distinct.
-/
lemma A_seq_distinct (n m : ℕ) (h : n ≠ m) : A_seq n ≠ A_seq m := by
  have h_distinct : ∀ n m, n < m → dist_from_diagonal (A_seq m) < dist_from_diagonal (A_seq n) := by
    exact strictAnti_nat_of_succ_lt ( fun n => dist_from_diagonal_strict_decreasing n );
  cases lt_or_gt_of_ne h <;> [ exact ne_of_apply_ne _ ( ne_of_gt ( h_distinct _ _ ‹_› ) ) ; exact ne_of_apply_ne _ ( ne_of_lt ( h_distinct _ _ ‹_› ) ) ]

/-
The segments S_seq n and S_seq m are disjoint for distinct n and m.
-/
lemma S_seq_disjoint (n m : ℕ) (h : n ≠ m) : Disjoint (S_seq n) (S_seq m) := by
  -- By definition of $A_seq$, we know that $A_{n+1}$ and $A_{m+1}$ are distinct points on the unit circle centered at $O$, so the segments $S_seq n$ and $S_seq m$ are disjoint.
  have h_distinct : A_seq (n + 1) ≠ A_seq (m + 1) := by
    exact fun hnm => h ( by have := A_seq_distinct ( n + 1 ) ( m + 1 ) ; aesop );
  -- Assume there exists a point p in both S_seq n and S_seq m.
  by_contra h_inter;
  obtain ⟨a, b, c, d, habcd⟩ : ∃ a b c d : ℝ, 0 < a ∧ a < 1 ∧ 0 < b ∧ b < 1 ∧ a • A_seq (n + 1) = b • A_seq (m + 1) ∧ 0 < c ∧ c < 1 ∧ d = c ∧ 0 < d ∧ d < 1 := by
    obtain ⟨ p, hp₁, hp₂ ⟩ := Set.not_disjoint_iff.mp h_inter;
    obtain ⟨ a, ha₁, ha₂ ⟩ := hp₁;
    obtain ⟨ b, hb₁, hb₂ ⟩ := hp₂;
    use ha₁, hb₁, b, b;
    simp_all +decide [ ← eq_sub_iff_add_eq' ];
    exact ⟨ by linarith, by linarith, by rw [ ← ha₂.2.2.1, ← hb₂.2.2.1 ] ; rw [ ha₂.2.2.2, hb₂.2.2.2 ] ; ext i ; fin_cases i <;> norm_num [ O_point ], by linarith ⟩;
  -- Since $a • A_seq (n + 1) = b • A_seq (m + 1)$, we have $a = b$ because $A_seq (n + 1)$ and $A_seq (m + 1)$ are distinct points on the unit circle.
  have h_eq : a = b := by
    have := congr_arg ( fun x : Point => ‖x‖ ) habcd.2.2.2.2.1 ; norm_num [ EuclideanSpace.norm_eq ] at this;
    -- Since $A_seq (n + 1)$ and $A_seq (m + 1)$ are distinct points on the unit circle, their norms are both 1.
    have h_norm : ‖A_seq (n + 1)‖ = 1 ∧ ‖A_seq (m + 1)‖ = 1 := by
      have := A_seq_properties ( n + 1 ) ; have := A_seq_properties ( m + 1 ) ; simp_all +decide [ dist_eq_norm ] ;
      simp_all +decide [ EuclideanSpace.norm_eq, O_point ];
    simp_all +decide [ EuclideanSpace.norm_eq ];
    rw [ Real.sqrt_inj ( by positivity ) ( by positivity ) ] at this ; simp_all +decide [ mul_pow, abs_of_pos ];
    nlinarith [ mul_pos habcd.1 habcd.2.2.1 ];
  simp_all +decide
  exact h_distinct ( smul_right_injective _ habcd.1.ne' habcd.2.2.2.2.1 )

/-
The segments S_seq_refl n and S_seq_refl m are disjoint for distinct n and m.
-/
lemma S_seq_refl_disjoint (n m : ℕ) (h : n ≠ m) : Disjoint (S_seq_refl n) (S_seq_refl m) := by
  convert Set.disjoint_image_of_injective ( show Function.Injective reflection from fun p q h => ?_ ) ( S_seq_disjoint n m h ) using 1;
  · unfold S_seq_refl S_seq;
    ext; simp [reflection];
    constructor;
    · rintro ⟨ a, b, ha, hb, hab, rfl ⟩;
      refine' ⟨ a • O_point + b • A_seq ( n + 1 ), _, _ ⟩ <;> norm_num [ openSegment_eq_image, hab ];
      · exact ⟨ b, ⟨ hb, by linarith ⟩, by rw [ ← eq_sub_iff_add_eq' ] at hab; aesop ⟩;
      · ext i ; fin_cases i <;> norm_num [ O_point, O_prime ] <;> ring_nf;
        · linarith;
        · rw [ ← eq_sub_iff_add_eq' ] at hab ; subst_vars ; ring;
    · rintro ⟨ x, ⟨ a, b, ha, hb, hab, rfl ⟩, rfl ⟩;
      refine' ⟨ a, b, ha, hb, hab, _ ⟩ ; ext i ; fin_cases i <;> norm_num [ O_point, A_seq ] ; ring_nf;
      · rw [ show O_prime ⟨ 0, by norm_num ⟩ = 1 by norm_num [ O_prime ] ] ; linarith;
      · rw [ show O_prime = ![1, 1 / 2] by rfl ] ; norm_num ; rw [ ← eq_sub_iff_add_eq' ] at hab ; subst_vars ; ring;
  · unfold S_seq_refl S_seq;
    ext; simp [reflection];
    constructor;
    · rintro ⟨ a, b, ha, hb, hab, rfl ⟩;
      refine' ⟨ a • O_point + b • A_seq ( m + 1 ), _, _ ⟩ <;> norm_num [ openSegment_eq_image ];
      · exact ⟨ b, ⟨ hb, by linarith ⟩, by rw [ ← eq_sub_iff_add_eq' ] at hab; aesop ⟩;
      · ext i ; fin_cases i <;> norm_num [ O_point, O_prime ] <;> ring_nf;
        · linarith;
        · rw [ ← eq_sub_iff_add_eq' ] at hab ; subst_vars ; ring;
    · rintro ⟨ x, hx, rfl ⟩;
      obtain ⟨ a, b, ha, hb, hab, rfl ⟩ := hx;
      refine' ⟨ a, b, ha, hb, hab, _ ⟩ ; ext i ; fin_cases i <;> norm_num [ O_point, A_0, reflection ] ; ring_nf;
      · rw [ show O_prime ⟨ 0, by norm_num ⟩ = 1 by exact rfl ] ; nlinarith;
      · rw [ show O_prime = ![1, 1 / 2] by rfl ] ; norm_num ; rw [ ← eq_sub_iff_add_eq' ] at hab ; subst_vars ; ring;
  · exact reflection_involution p ▸ reflection_involution q ▸ h ▸ rfl

/-
The signed distance of A_n from the diagonal alternates sign: positive for even n, negative for odd n.
-/
def signed_dist_from_diagonal (p : Point) : ℝ := p 0 - 2 * p 1

lemma signed_dist_A_seq_sign (n : ℕ) :
  (Even n → signed_dist_from_diagonal (A_seq n) > 0) ∧
  (Odd n → signed_dist_from_diagonal (A_seq n) < 0) := by
    induction' n with n ih <;> simp_all +decide [ parity_simps ];
    · unfold signed_dist_from_diagonal; norm_num [ A_0 ];
      exact show 2 * 0 < 1 by norm_num;
    · -- By definition of $A_{n+1}$, it lies on the segment between $O'$ and $A'_n$.
      have h_A_seq_succ : A_seq (n + 1) ∈ openSegment ℝ O_prime (reflection (A_seq n)) := by
        exact A_seq_between n;
      obtain ⟨t, ht⟩ : ∃ t ∈ Set.Ioo (0 : ℝ) 1, A_seq (n + 1) = (1 - t) • O_prime + t • reflection (A_seq n) := by
        rw [ openSegment_eq_image ] at h_A_seq_succ ; aesop;
      -- By definition of $signed_dist_from_diagonal$, we have $signed_dist_from_diagonal (A_seq (n + 1)) = (1 - t) * signed_dist_from_diagonal O_prime + t * signed_dist_from_diagonal (reflection (A_seq n))$.
      have h_signed_dist_succ : signed_dist_from_diagonal (A_seq (n + 1)) = (1 - t) * signed_dist_from_diagonal O_prime + t * signed_dist_from_diagonal (reflection (A_seq n)) := by
        simp [ht, signed_dist_from_diagonal];
        ring;
      -- By definition of $signed_dist_from_diagonal$, we have $signed_dist_from_diagonal O_prime = 0$ and $signed_dist_from_diagonal (reflection (A_seq n)) = -signed_dist_from_diagonal (A_seq n)$.
      have h_signed_dist_O_prime : signed_dist_from_diagonal O_prime = 0 := by
        unfold signed_dist_from_diagonal; norm_num [ O_prime ] ;
      have h_signed_dist_reflection : signed_dist_from_diagonal (reflection (A_seq n)) = -signed_dist_from_diagonal (A_seq n) := by
        unfold signed_dist_from_diagonal; unfold reflection; norm_num; ring;
      cases' Nat.even_or_odd n with h h <;> simp_all +decide [ parity_simps ];
      nlinarith

/-
The limit segment S_inf is contained in the diagonal.
-/
lemma S_inf_subset_diagonal : S_inf ⊆ {p | signed_dist_from_diagonal p = 0} := by
  unfold S_inf;
  unfold signed_dist_from_diagonal; intro x hx; rw [ openSegment_eq_image ] at hx; obtain ⟨ t, ht, rfl ⟩ := hx; norm_num [ ht.1, ht.2 ] ;
  unfold O_point A_inf; norm_num; ring;

/-
The segments S_seq n are disjoint from the diagonal.
-/
lemma S_seq_disjoint_diagonal (n : ℕ) : Disjoint (S_seq n) {p | signed_dist_from_diagonal p = 0} := by
  -- By definition of $A_seq$, we know that $A_{n+1}$ has a non-zero signed distance from the diagonal.
  have h_A_seq_n1_sign : signed_dist_from_diagonal (A_seq (n + 1)) ≠ 0 := by
    have := signed_dist_A_seq_sign ( n + 1 ) ; aesop;
  rw [ Set.disjoint_left ];
  rintro p ⟨ u, v, hu, hv, huv, rfl ⟩ ; simp_all +decide [ signed_dist_from_diagonal ];
  unfold O_point; norm_num; cases lt_or_gt_of_ne h_A_seq_n1_sign <;> nlinarith;

/-
The reflected segments S_seq_refl n are disjoint from the diagonal.
-/
lemma S_seq_refl_disjoint_diagonal (n : ℕ) : Disjoint (S_seq_refl n) {p | signed_dist_from_diagonal p = 0} := by
  -- By definition of $S_seq_refl$, we know that $S_seq_refl n = reflection '' S_seq n$.
  have h_reflection : S_seq_refl n = reflection '' S_seq n := by
    ext; simp
    constructor <;> intro h;
    · obtain ⟨ a, ha, b, hb, hab, rfl ⟩ := h;
      refine' ⟨ _, ⟨ a, ha, b, hb, hab, rfl ⟩, _ ⟩;
      unfold reflection; ext i; fin_cases i <;> norm_num [ O_point, O_prime, A_0 ] ; ring_nf;
      · linarith;
      · rw [ ← eq_sub_iff_add_eq' ] at hab ; subst_vars ; ring;
    · rcases h with ⟨ x, ⟨ a, ha, b, hb, hab, rfl ⟩, rfl ⟩ ; use a, ha, b, hb, hab; ext i; fin_cases i <;> norm_num [ reflection ] ;
      · unfold O_prime O_point; norm_num; rw [ ← eq_sub_iff_add_eq' ] at hab; subst hab; ring;
      · unfold O_prime O_point; norm_num; rw [ ← eq_sub_iff_add_eq' ] at hab; subst hab; ring;
  -- Since $S_seq n$ is disjoint from the diagonal, its reflection $S_seq_refl n$ is also disjoint from the diagonal.
  have h_disjoint_refl : Disjoint (S_seq n) {p | signed_dist_from_diagonal p = 0} := by
    exact S_seq_disjoint_diagonal n;
  simp_all +decide [ Set.disjoint_left ];
  exact fun x hx => fun hx' => h_disjoint_refl hx <| by unfold reflection at hx'; unfold signed_dist_from_diagonal at *; norm_num at *; linarith;

/-
The segments S_seq n are disjoint from S_inf.
-/
lemma S_seq_S_inf_disjoint (n : ℕ) : Disjoint (S_seq n) S_inf := by
  exact Set.disjoint_left.mpr fun x hx₁ hx₂ => by have := S_inf_subset_diagonal hx₂; exact ( S_seq_disjoint_diagonal n ) |> fun h => h.le_bot ⟨ hx₁, this ⟩ ;

/-
The segments S_seq_refl n are disjoint from S_inf.
-/
lemma S_seq_refl_S_inf_disjoint (n : ℕ) : Disjoint (S_seq_refl n) S_inf := by
  -- Since S_inf is contained in the diagonal and S_seq_refl n is disjoint from the diagonal, they must be disjoint from each other.
  have h_disjoint : Disjoint (S_seq_refl n) {p : Point | signed_dist_from_diagonal p = 0} := by
    -- Apply the lemma that states S_seq_refl n is disjoint from the diagonal.
    apply S_seq_refl_disjoint_diagonal;
  exact h_disjoint.mono_right ( by exact fun x hx => by have := S_inf_subset_diagonal hx; aesop )

/-
The signed distance of points in S_seq n has a constant sign depending on the parity of n.
-/
lemma S_seq_sign (n : ℕ) :
  (Even n → ∀ p ∈ S_seq n, signed_dist_from_diagonal p < 0) ∧
  (Odd n → ∀ p ∈ S_seq n, signed_dist_from_diagonal p > 0) := by
    constructor <;> intro hn p hp;
    · -- By definition of $S_seq$, we know that $p$ is a convex combination of $O_point$ and $A_seq (n + 1)$.
      obtain ⟨t, ht⟩ : ∃ t ∈ Set.Ioo (0 : ℝ) 1, p = (1 - t) • O_point + t • A_seq (n + 1) := by
        -- By definition of openSegment, there exists a t in (0,1) such that p = (1-t) • O_point + t • A_seq (n + 1).
        have h_convex : p ∈ openSegment ℝ O_point (A_seq (n + 1)) := by
          exact hp;
        rcases h_convex with ⟨ u, v, hu, hv, huv, rfl ⟩ ; exact ⟨ v, ⟨ by linarith, by linarith ⟩, by simp +decide [ huv.symm ] ⟩ ;
      have := signed_dist_A_seq_sign ( n + 1 );
      simp_all +decide [ parity_simps ];
      unfold signed_dist_from_diagonal at *;
      rw [ Pi.add_apply, Pi.add_apply ] ; norm_num [ O_point ] ; nlinarith;
    · -- By definition of $S_seq$, we know that $p$ is a convex combination of $O$ and $A_{n+1}$.
      obtain ⟨t, ht⟩ : ∃ t ∈ Set.Ioo (0 : ℝ) 1, p = t • O_point + (1 - t) • A_seq (n + 1) := by
        unfold S_seq at hp;
        rw [ openSegment_eq_image ] at hp;
        rcases hp with ⟨ t, ht, rfl ⟩ ; exact ⟨ 1 - t, ⟨ by linarith [ ht.1, ht.2 ], by linarith [ ht.1, ht.2 ] ⟩, by simp +decide [ add_comm ] ⟩ ;
      -- Substitute the coordinates of p into the signed distance formula.
      simp [ht, signed_dist_from_diagonal];
      -- Since $n$ is odd, we have $signed_dist_from_diagonal (A_seq (n + 1)) > 0$.
      have h_odd : signed_dist_from_diagonal (A_seq (n + 1)) > 0 := by
        convert signed_dist_A_seq_sign ( n + 1 ) |>.1 ( by simpa [ parity_simps ] using hn ) using 1;
      unfold signed_dist_from_diagonal at h_odd; norm_num [ O_point ] at *; nlinarith [ ht.1.1, ht.1.2 ] ;

/-
The signed distance of points in S_seq_refl n has a constant sign opposite to that of S_seq n.
-/
lemma S_seq_refl_sign (n : ℕ) :
  (Even n → ∀ p ∈ S_seq_refl n, signed_dist_from_diagonal p > 0) ∧
  (Odd n → ∀ p ∈ S_seq_refl n, signed_dist_from_diagonal p < 0) := by
    -- By definition of $S_seq_refl$, we know that $p = reflection q$ for some $q \in S_seq n$.
    have h_reflection : ∀ p ∈ S_seq_refl n, ∃ q ∈ S_seq n, p = reflection q := by
      unfold S_seq;
      rintro p ⟨ a, b, ha, hb, hab, rfl ⟩;
      refine' ⟨ a • O_point + b • A_seq ( n + 1 ), _, _ ⟩ <;> norm_num [ openSegment_eq_image ];
      · exact ⟨ b, ⟨ hb, by linarith ⟩, by rw [ ← eq_sub_iff_add_eq' ] at hab; subst hab; ext i; fin_cases i <;> norm_num ⟩;
      · unfold reflection; ext i; fin_cases i <;> norm_num <;> ring_nf;
        · unfold O_prime O_point; norm_num; rw [ ← eq_sub_iff_add_eq' ] at hab; subst hab; ring;
        · unfold O_prime O_point; norm_num; rw [ ← eq_sub_iff_add_eq' ] at hab; subst hab; ring;
    constructor <;> intro hn p hp <;> obtain ⟨ q, hq, rfl ⟩ := h_reflection p hp <;> unfold signed_dist_from_diagonal <;> unfold reflection <;> norm_num;
    · have := S_seq_sign n;
      linarith [ this.1 hn q hq, show signed_dist_from_diagonal q = q 0 - 2 * q 1 from rfl ];
    · have := S_seq_sign n;
      linarith [ this.2 hn q hq, show signed_dist_from_diagonal q = q 0 - 2 * q 1 from rfl ]

/-
If n and m have the same parity, the segments S_seq n and S_seq_refl m are disjoint because they lie on opposite sides of the diagonal.
-/
lemma S_seq_S_seq_refl_disjoint_same_parity (n m : ℕ) (h : n % 2 = m % 2) : Disjoint (S_seq n) (S_seq_refl m) := by
  by_cases hn : Even n <;> by_cases hm : Even m <;> simp_all +decide [ Nat.even_iff ];
  · -- Since $n$ and $m$ are both even, $S_seq n$ lies on the negative side of the diagonal and $S_seq_refl m$ lies on the positive side of the diagonal.
    have h_neg_pos : ∀ p ∈ S_seq n, signed_dist_from_diagonal p < 0 ∧ ∀ q ∈ S_seq_refl m, signed_dist_from_diagonal q > 0 := by
      exact fun p hp => ⟨ S_seq_sign n |>.1 ( Nat.even_iff.mpr h ) p hp, fun q hq => S_seq_refl_sign m |>.1 ( Nat.even_iff.mpr hn ) q hq ⟩;
    exact Set.disjoint_left.mpr fun p hp hp' => by linarith [ h_neg_pos p hp |>.1, h_neg_pos p hp |>.2 p hp' ] ;
  · -- By S_seq_sign and S_seq_refl_sign, if n and m are both odd, then S_seq n has positive signed distance and S_seq_refl m has negative signed distance.
    have h_sign : ∀ p ∈ S_seq n, signed_dist_from_diagonal p > 0 := by
      exact S_seq_sign n |>.2 ( Nat.odd_iff.mpr h )
    have h_sign_refl : ∀ p ∈ S_seq_refl m, signed_dist_from_diagonal p < 0 := by
      exact S_seq_refl_sign m |>.2 ( Nat.odd_iff.mpr hn );
    exact Set.disjoint_left.mpr fun x hx hx' => by linarith [ h_sign x hx, h_sign_refl x hx' ] ;

/-
The separating functional f_n takes the same non-zero value at O' and A'_{n+1}.
-/
lemma separating_functional_values (n : ℕ) :
  let f := separating_functional n
  f O_prime = f (reflection (A_seq (n + 1))) ∧ f O_prime ≠ 0 := by
    unfold separating_functional
    simp [O_prime, reflection]
    -- By definition of $A_seq$, we know that $A_seq (n + 1) 0 - 2 * (A_seq (n + 1)) 1 ≠ 0$.
    have h_sign : (A_seq (n + 1)) 0 - 2 * (A_seq (n + 1)) 1 ≠ 0 := by
      by_contra h_contra;
      have := signed_dist_A_seq_sign ( n + 1 ) ; simp_all +decide [ sub_eq_iff_eq_add ] ;have := signed_dist_A_seq_sign (n + 1); simp_all +decide
      cases Nat.even_or_odd ( n + 1 ) <;> simp_all +decide [ signed_dist_from_diagonal ];
    exact ⟨ by ring, by contrapose! h_sign; ring_nf at *; linarith ⟩

/-
The separating functional f_n is non-zero on S_seq_refl m for m >= n.
-/
lemma separating_functional_nonzero_on_S_seq_refl (n m : ℕ) (h : n ≤ m) :
  ∀ p ∈ S_seq_refl m, separating_functional n p ≠ 0 := by
    intro p hp;
    -- By definition of $S_seq_refl$, there exist $t \in (0, 1)$ such that $p = (1 - t) • O_prime + t • reflection (A_seq (m + 1))$.
    obtain ⟨t, ht₀, ht₁⟩ : ∃ t ∈ Set.Ioo (0 : ℝ) 1, p = (1 - t) • O_prime + t • reflection (A_seq (m + 1)) := by
      unfold S_seq_refl at hp;
      rw [ openSegment_eq_image ] at hp; aesop;
    -- By definition of $f_n$, we know that $f_n(O') = k$ and $f_n(A'_{n+1}) = k$ for some $k \neq 0$.
    obtain ⟨k, hk⟩ : ∃ k : ℝ, (separating_functional n) O_prime = k ∧ (separating_functional n) (reflection (A_seq (n + 1))) = k ∧ k ≠ 0 := by
      have := separating_functional_values n; aesop;
    -- Since $m \geq n$, we have $A'_{m+1} \in P_{n+1}$.
    have h_A_prime_mem_P_n_plus_1 : reflection (A_seq (m + 1)) ∈ Parallelogram_seq (n + 1) := by
      have h_A_prime_mem_P_n_plus_1 : ∀ k ≥ n + 1, reflection (A_seq (k + 1)) ∈ Parallelogram_seq (n + 1) := by
        intro k hk_n_plus_1
        have h_A_prime_mem_P_k_plus_1 : reflection (A_seq (k + 1)) ∈ Parallelogram_seq (k + 1) := by
          exact subset_convexHull ℝ _ <| by aesop;
        have h_P_k_plus_1_subset_P_n_plus_1 : ∀ k ≥ n + 1, Parallelogram_seq (k + 1) ⊆ Parallelogram_seq (n + 1) := by
          intros k hk_n_plus_1
          induction' hk_n_plus_1 with k hk ih;
          · exact Parallelogram_seq_subset (n + 1);
          · exact Set.Subset.trans ( Parallelogram_seq_subset _ ) ih;
        exact h_P_k_plus_1_subset_P_n_plus_1 k hk_n_plus_1 h_A_prime_mem_P_k_plus_1;
      by_cases h_cases : m = n;
      · simp_all +decide [ Parallelogram_seq ];
        exact subset_convexHull ℝ _ ( by norm_num );
      · exact h_A_prime_mem_P_n_plus_1 m ( Nat.succ_le_of_lt ( lt_of_le_of_ne h ( Ne.symm h_cases ) ) );
    -- Since $A'_{m+1} \in P_{n+1}$, we have $f_n(A'_{m+1}) = (c + d)k$ for some $c, d \geq 0$ with $c + d \leq 1$.
    obtain ⟨c, d, hc, hd, hcd⟩ : ∃ c d : ℝ, 0 ≤ c ∧ 0 ≤ d ∧ c + d ≤ 1 ∧ (separating_functional n) (reflection (A_seq (m + 1))) = (c + d) * k := by
      -- By definition of $P_{n+1}$, we know that $A'_{m+1}$ can be written as a convex combination of $O$, $A_{n+1}$, $O'$, and $A'_{n+1}$.
      obtain ⟨a, b, c, d, ha, hb, hc, hd, habcd⟩ : ∃ a b c d : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ a + b + c + d = 1 ∧ reflection (A_seq (m + 1)) = a • O_point + b • A_seq (n + 1) + c • O_prime + d • reflection (A_seq (n + 1)) := by
        have h_convex_comb : ∀ p ∈ convexHull ℝ {O_point, A_seq (n + 1), O_prime, reflection (A_seq (n + 1))}, ∃ a b c d : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ a + b + c + d = 1 ∧ p = a • O_point + b • A_seq (n + 1) + c • O_prime + d • reflection (A_seq (n + 1)) := by
          intro p hp
          rw [convexHull_insert] at hp;
          · norm_num [ segment_eq_image ] at hp;
            rcases hp with ⟨ q, hq, x, hx, rfl ⟩ ; rw [ convexHull_insert ] at hq; norm_num at hq;
            · rcases hq with ⟨ y, hy, hq ⟩ ; rw [ segment_eq_image ] at hy hq; norm_num at hy hq;
              rcases hy with ⟨ y, ⟨ hy₀, hy₁ ⟩, rfl ⟩ ; rcases hq with ⟨ z, ⟨ hz₀, hz₁ ⟩, rfl ⟩ ; exact ⟨ 1 - x, x * ( 1 - z ), x * z * ( 1 - y ), x * z * y, by linarith, by nlinarith, by nlinarith [ mul_nonneg hx.1 hz₀ ], by nlinarith [ mul_nonneg hx.1 hz₀ ], by ring, by ext i; simpa using by ring ⟩ ;
            · norm_num;
          · norm_num;
        exact h_convex_comb _ h_A_prime_mem_P_n_plus_1;
      use c, d;
      rw [ habcd.2 ] ; norm_num [ hk, add_mul, mul_add, mul_assoc, mul_left_comm, Finset.sum_add_distrib ] ; ring_nf;
      exact ⟨ hc, hd, by linarith, by rw [ show separating_functional n O_point = 0 from by simpa using separating_functional_properties n |>.1, show separating_functional n ( A_seq ( 1 + n ) ) = 0 from by simpa [ add_comm ] using separating_functional_properties n |>.2.1 ] ; ring ⟩;
    -- Substitute the values of $f_n(O')$ and $f_n(A'_{m+1})$ into the expression for $f_n(p)$.
    have h_f_p : (separating_functional n) p = k * ((1 - t) + t * (c + d)) := by
      simp_all +decide [ mul_add, mul_comm, mul_left_comm ];
    exact h_f_p.symm ▸ mul_ne_zero hk.2.2 ( by nlinarith [ ht₀.1, ht₀.2 ] )

/-
If n < m, the segments S_seq n and S_seq_refl m are disjoint.
-/
lemma S_seq_disjoint_S_seq_refl_of_lt (n m : ℕ) (h : n < m) : Disjoint (S_seq n) (S_seq_refl m) := by
  -- By `separating_functional_nonzero_on_S_seq_refl`, f_n is non-zero on S_seq_refl m (since n < m implies n <= m).
  have h_nonzero : ∀ p ∈ S_seq_refl m, separating_functional n p ≠ 0 := by
    apply_rules [ separating_functional_nonzero_on_S_seq_refl ];
    linarith;
  -- By `separating_functional_values`, f_n vanishes on the line passing through O and A_{n+1}, which contains S_seq n.
  have h_zero : ∀ p ∈ S_seq n, separating_functional n p = 0 := by
    -- Since $p \in S_seq n$, we can write $p$ as $(1 - t) * O_point + t * A_seq (n + 1)$ for some $t \in (0, 1)$.
    intro p hp
    obtain ⟨t, ht⟩ : ∃ t ∈ Set.Ioo (0 : ℝ) 1, p = (1 - t) • O_point + t • A_seq (n + 1) := by
      unfold S_seq at hp; rw [ openSegment_eq_image ] at hp; aesop;
    simp_all +decide [ separating_functional ];
    unfold O_point; norm_num; ring;
  exact Set.disjoint_left.mpr fun x hx₁ hx₂ => h_nonzero x hx₂ <| h_zero x hx₁

/-
If n < m, the segments S_seq_refl n and S_seq m are disjoint.
-/
lemma S_seq_refl_disjoint_S_seq_of_lt (n m : ℕ) (h : n < m) : Disjoint (S_seq_refl n) (S_seq m) := by
  have h_disjoint_refl : Disjoint (S_seq n) (S_seq_refl m) := by
    exact S_seq_disjoint_S_seq_refl_of_lt n m h;
  -- Since reflection is a bijection, the disjointness of the original segments implies the disjointness of their reflections.
  have h_reflection_bij : ∀ (S T : Set Point), Disjoint S T → Disjoint (reflection '' S) (reflection '' T) := by
    intros S T h_disjoint
    simp [Set.disjoint_iff_forall_ne] at h_disjoint ⊢;
    exact fun a ha b hb hab => h_disjoint ha hb <| by simpa [ reflection ] using congr_fun hab 0 |> fun h => by simpa [ reflection ] using congr_fun hab 1 |> fun h' => by ext i; fin_cases i <;> norm_num [ reflection ] at * <;> linarith!;
  convert h_reflection_bij _ _ h_disjoint_refl using 1;
  · ext; simp [S_seq_refl, S_seq];
    constructor <;> intro h;
    · rcases h with ⟨ a, b, ha, hb, hab, rfl ⟩;
      refine' ⟨ a • O_point + b • A_seq ( n + 1 ), _, _ ⟩ <;> simp_all +decide [ openSegment_eq_image, reflection ];
      · exact ⟨ b, ⟨ hb, by linarith ⟩, by rw [ ← eq_sub_iff_add_eq' ] at hab; aesop ⟩;
      · ext i; fin_cases i <;> norm_num [ O_prime, O_point ] <;> ring_nf;
        · linarith;
        · nlinarith;
    · rcases h with ⟨ x, hx, rfl ⟩;
      obtain ⟨ a, b, ha, hb, hab, rfl ⟩ := hx;
      use a, b;
      simp +decide [ reflection ];
      exact ⟨ ha, hb, hab, by ext i; fin_cases i <;> norm_num [ O_prime, O_point ] <;> linarith ⟩;
  · ext; simp [S_seq, S_seq_refl];
    constructor;
    · rintro ⟨ a, b, ha, hb, hab, rfl ⟩;
      refine' ⟨ a • O_prime + b • reflection ( A_seq ( m + 1 ) ), _, _ ⟩ <;> simp_all +decide [ openSegment_eq_image ];
      · exact ⟨ b, ⟨ hb, by linarith ⟩, by rw [ ← eq_sub_iff_add_eq' ] at hab; subst hab; ext i; fin_cases i <;> norm_num ⟩;
      · unfold reflection; norm_num [ ← eq_sub_iff_add_eq' ] at *; ring_nf;
        ext i ; fin_cases i <;> norm_num [ O_point, O_prime ] <;> ring_nf;
        · linarith!;
        · linarith!;
    · rintro ⟨ x, hx, rfl ⟩;
      obtain ⟨ a, b, ha, hb, hab, rfl ⟩ := hx;
      refine' ⟨ a, b, ha, hb, hab, _ ⟩ ; ext i ; fin_cases i <;> norm_num [ reflection ] ; ring_nf!;
      · unfold O_point O_prime; norm_num; ring_nf;
        linarith;
      · unfold O_point O_prime; norm_num; ring_nf;
        rw [ show a = 1 - b by linarith ] ; ring!

/-
The segments in S_collection are pairwise disjoint.
-/
theorem S_collection_pairwise_disjoint :
  ∀ s t, s ∈ S_collection → t ∈ S_collection → s ≠ t → Disjoint s t := by
    intro s t hs ht hst;
    by_cases h_cases : s = S_inf ∨ t = S_inf;
    · rcases h_cases with ( rfl | rfl );
      · cases' ht with n hn;
        · cases' n with n hn;
          · rcases n with ⟨ n, rfl ⟩ ; exact S_seq_S_inf_disjoint n |> Disjoint.symm;
          · rcases hn with ⟨ n, rfl ⟩ ; exact S_seq_refl_S_inf_disjoint n |> fun h => h.symm;
        · aesop;
      · cases' hs with n hn;
        · rcases n with ( ⟨ n, rfl ⟩ | ⟨ n, rfl ⟩ ) <;> [ exact S_seq_S_inf_disjoint n; exact S_seq_refl_S_inf_disjoint n ];
        · aesop;
    · rcases hs with ( ⟨ n, rfl ⟩ | ⟨ n, rfl ⟩ ) <;> rcases ht with ( ⟨ m, rfl ⟩ | ⟨ m, rfl ⟩ ) <;> simp_all +decide [ Set.disjoint_left ];
      · exact fun x hx hx' => Set.disjoint_left.mp ( S_seq_disjoint n m ( by aesop ) ) hx hx';
      · obtain ⟨ m, rfl ⟩ := ‹∃ n, t = S_seq_refl n›;
        by_cases hnm : n < m;
        · exact fun p hp hp' => Set.disjoint_left.mp ( S_seq_disjoint_S_seq_refl_of_lt n m hnm ) hp hp';
        · cases lt_or_eq_of_le ( le_of_not_gt hnm ) <;> simp_all +decide
          · exact fun x hx₁ hx₂ => hst <| by have := S_seq_refl_disjoint_S_seq_of_lt _ _ ‹_›; exact False.elim <| this.le_bot ⟨ hx₂, hx₁ ⟩ ;
          · intro p hp hp'; have := S_seq_sign n; have := S_seq_refl_sign n; simp_all +decide
            grind;
      · intro p hp hp'; rcases ‹∃ n, s = S_seq_refl n› with ⟨ n, rfl ⟩ ; exact (by
        by_cases hmn : m < n;
        · exact hst ( by have := S_seq_disjoint_S_seq_refl_of_lt m n hmn; exact False.elim <| this.le_bot ⟨ hp', hp ⟩ );
        · cases lt_or_eq_of_le ( le_of_not_gt hmn ) <;> simp_all +decide
          · exact Set.disjoint_left.mp ( S_seq_refl_disjoint_S_seq_of_lt _ _ ‹_› ) hp hp';
          · -- Since $p$ is in both $S_seq m$ and $S_seq_refl m$, and these segments are disjoint, this leads to a contradiction.
            have h_contradiction : Disjoint (S_seq m) (S_seq_refl m) := by
              apply S_seq_S_seq_refl_disjoint_same_parity;
              rfl;
            exact h_contradiction.le_bot ⟨ hp', hp ⟩);
      · -- Since $s$ and $t$ are both in the collection and not equal to $S_{\infty}$, they must be of the form $S_{\text{seq\_refl}} n$ and $S_{\text{seq\_refl}} m$ for some $n$ and $m$.
        obtain ⟨n, rfl⟩ := ‹∃ n, s = S_seq_refl n›
        obtain ⟨m, rfl⟩ := ‹∃ m, t = S_seq_refl m›;
        have := S_seq_refl_disjoint n m; simp_all +decide [ Set.disjoint_left ] ;
        cases eq_or_ne n m <;> aesop

/-
The region R is contained in the first parallelogram P_0.
-/
lemma Region_subset_P0 : Region_R ⊆ Parallelogram_seq 0 := by
  -- To prove the subset relation, take any point $p$ in $Region_R$. By the definition of $Region_R$, we have $0 < p 0 < 1$ and $0 < p 1 < 1/2$.
  intro p hp
  have h_coords : 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1/2 := by
    exact ⟨ hp.1.le, hp.2.1.le, hp.2.2.1.le, hp.2.2.2.le ⟩;
  -- Since $p$ is in the closed rectangle $[0,1] \times [0,1/2]$, it is in the convex hull of the four points.
  have h_p_convex : p ∈ convexHull ℝ {![0, 0], ![1, 0], ![1, 1/2], ![0, 1/2]} := by
    rw [ convexHull_eq ];
    use Fin 4;
    refine' ⟨ { 0, 1, 2, 3 }, fun i => if i = 0 then ( 1 - p 0 ) * ( 1 - p 1 * 2 ) else if i = 1 then p 0 * ( 1 - p 1 * 2 ) else if i = 2 then p 0 * p 1 * 2 else ( 1 - p 0 ) * p 1 * 2, fun i => if i = 0 then ![0, 0] else if i = 1 then ![1, 0] else if i = 2 then ![1, 1 / 2] else ![0, 1 / 2], _, _, _, _ ⟩ <;> simp +decide [ Finset.centerMass ];
    · exact ⟨ mul_nonneg ( by linarith ) ( by linarith ), mul_nonneg ( by linarith ) ( by linarith ), mul_nonneg ( by linarith ) ( by linarith ), mul_nonneg ( by linarith ) ( by linarith ) ⟩;
    · ring;
    · ext i ; fin_cases i <;> norm_num <;> ring_nf;
      · rfl;
      · rfl;
  convert h_p_convex using 1;
  unfold Parallelogram_seq Parallelogram; norm_num;
  congr ; ext i ; fin_cases i <;> norm_num [ O_point, A_seq, O_prime, reflection ];
  · exact sub_eq_zero_of_eq <| by norm_num [ A_0 ] ;
  · exact rfl

/-
The n-th parallelogram is the union of the n-th triangle, the (n+1)-th parallelogram, and the reflected n-th triangle.
-/
lemma Parallelogram_decomposition_eq (n : ℕ) : Parallelogram_seq n = Triangle_OA_prime_P n ∪ Parallelogram_seq (n + 1) ∪ Triangle_seq_refl n := by
  -- Apply the lemma that states the parallelogram is covered by the union of the triangle, the next parallelogram, and the reflected triangle.
  apply le_antisymm;
  · convert Parallelogram_covered n using 1;
    ac_rfl;
  · -- By definition of $Parallelogram_seq$, we know that $Triangle_OA_prime_P n \cup Parallelogram_seq (n + 1) \cup Triangle_seq_refl n \subseteq Parallelogram_seq n$.
    apply Parallelogram_decomposition_subset

/-
The triangle T_n lies in the non-positive half-plane for even n, and in the non-negative half-plane for odd n.
-/
lemma Tn_subset_halfplane (n : ℕ) :
  (Even n → ∀ p ∈ Triangle_OA_prime_P n, signed_dist_from_diagonal p ≤ 0) ∧
  (Odd n → ∀ p ∈ Triangle_OA_prime_P n, signed_dist_from_diagonal p ≥ 0) := by
    constructor <;> intro hn p hp;
    · -- Since $p$ is in the triangle $T_n$, we can write it as a convex combination of $O$, $A'_n$, and $A_{n+1}$.
      obtain ⟨a, b, c, ha, hb, hc, habc, hp⟩ : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • O_point + b • reflection (A_seq n) + c • A_seq (n + 1) := by
        unfold Triangle_OA_prime_P at hp;
        norm_num [ convexHull_insert ] at hp;
        rcases hp with ⟨ q, ⟨ a, b, ha, hb, hab, rfl ⟩, ⟨ c, d, hc, hd, hcd, rfl ⟩ ⟩ ; exact ⟨ c, d * a, d * b, by positivity, by positivity, by positivity, by nlinarith, by ext i; simpa using by ring ⟩ ;
      unfold signed_dist_from_diagonal at *;
      unfold reflection at *; norm_num [ hp ] ;
      -- By definition of $A_seq$, we know that $A_seq n 0 - 2 * A_seq n 1 > 0$ and $A_seq (n + 1) 0 - 2 * A_seq (n + 1) 1 < 0$ for even $n$.
      have h_signs : A_seq n 0 - 2 * A_seq n 1 > 0 ∧ A_seq (n + 1) 0 - 2 * A_seq (n + 1) 1 < 0 := by
        have := signed_dist_A_seq_sign n; have := signed_dist_A_seq_sign ( n + 1 ) ; simp_all +decide [ parity_simps ] ;
        unfold signed_dist_from_diagonal at *; constructor <;> linarith;
      unfold O_point at *; norm_num at *; nlinarith;
    · -- By definition of $Triangle_OA_prime_P$, we know that $p$ is a convex combination of $O$, $reflection (A_seq n)$, and $A_seq (n + 1)$.
      obtain ⟨a, b, c, ha, hb, hc, habc⟩ : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • O_point + b • reflection (A_seq n) + c • A_seq (n + 1) := by
        unfold Triangle_OA_prime_P at hp;
        norm_num [ convexHull_insert ] at hp;
        rcases hp with ⟨ q, ⟨ a, b, ha, hb, hab, rfl ⟩, ⟨ c, d, hc, hd, hcd, rfl ⟩ ⟩ ; exact ⟨ c, d * a, d * b, by positivity, by positivity, by positivity, by nlinarith, by ext ; simpa using by ring ⟩ ;
      -- Since $n$ is odd, by `signed_dist_A_seq_sign`, we have $signed_dist_from_diagonal (A_seq n) < 0$ and $signed_dist_from_diagonal (A_seq (n + 1)) > 0$.
      have h_signed_dist_A_seq_neg : signed_dist_from_diagonal (A_seq n) < 0 := by
        exact signed_dist_A_seq_sign n |>.2 hn
      have h_signed_dist_A_seq_pos : signed_dist_from_diagonal (A_seq (n + 1)) > 0 := by
        have := signed_dist_A_seq_sign ( n + 1 ) ; simp_all +decide [ parity_simps ] ;
      unfold signed_dist_from_diagonal at *; norm_num [ habc ] at *;
      unfold reflection at *; norm_num [ O_point ] at *; nlinarith;

/-
The closure of S_seq n is the closed segment connecting O and A_{n+1}.
-/
lemma closure_S_seq (n : ℕ) : closure (S_seq n) = segment ℝ O_point (A_seq (n + 1)) := by
  unfold S_seq;
  exact closure_openSegment O_point (A_seq (n + 1))

/-
The intersection of the n-th triangle and the (n+1)-th parallelogram is contained in the closure of S_seq n.
-/
lemma Tn_inter_Pn_subset_closure_S_seq (n : ℕ) : Triangle_OA_prime_P n ∩ Parallelogram_seq (n + 1) ⊆ closure (S_seq n) := by
  have h_sep_zero : ∀ p ∈ Triangle_OA_prime_P n ∩ Parallelogram_seq (n + 1), separating_functional n p = 0 := by
    intro p hp
    have h_sep : (separating_functional n) p * (separating_functional n) (reflection (A_seq n)) ≥ 0 ∧ (separating_functional n) p * (separating_functional n) (reflection (A_seq n)) ≤ 0 := by
      exact ⟨ by simpa using separating_functional_separates n |>.1 p hp.1, by simpa using separating_functional_separates n |>.2 p hp.2 ⟩;
    have h_sep_nonzero : (separating_functional n) (reflection (A_seq n)) ≠ 0 := by
      have := separating_functional_values n; simp_all +decide
      -- By definition of $A_seq$, we know that $A_seq (n + 1) = t • O_prime + (1 - t) • reflection (A_seq n)$ for some $t \in (0, 1)$.
      obtain ⟨t, ht⟩ : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ A_seq (n + 1) = t • O_prime + (1 - t) • reflection (A_seq n) := by
        have := A_seq_between n; simp_all +decide [ openSegment_eq_image ] ;
        obtain ⟨ t, ht₁, ht₂ ⟩ := this; exact ⟨ 1 - t, by linarith, by linarith, by simpa [ add_comm ] using ht₂.symm ⟩ ;
      simp_all +decide [ separating_functional ];
      grind;
    exact mul_left_cancel₀ h_sep_nonzero <| by linarith;
  -- The set of points in $P_{n+1}$ where $f=0$ is the segment $[O, A_{n+1}]$.
  have h_segment : {p ∈ Parallelogram_seq (n + 1) | separating_functional n p = 0} = segment ℝ O_point (A_seq (n + 1)) := by
    ext p_of_subset_of_subset;
    constructor <;> intro hp;
    · -- By definition of $P_{n+1}$, we know that $p_of_subset_of_subset$ is a convex combination of $O$, $A_{n+1}$, $O'$, and $A'_{n+1}$.
      obtain ⟨a, b, c, d, ha, hb, hc, hd, habcd⟩ : ∃ a b c d : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ a + b + c + d = 1 ∧ p_of_subset_of_subset = a • O_point + b • A_seq (n + 1) + c • O_prime + d • reflection (A_seq (n + 1)) := by
        have h_convex_comb : p_of_subset_of_subset ∈ convexHull ℝ {O_point, A_seq (n + 1), O_prime, reflection (A_seq (n + 1))} := by
          exact hp.1;
        rw [ convexHull_insert ] at h_convex_comb;
        · norm_num [ segment_eq_image ] at h_convex_comb;
          rcases h_convex_comb with ⟨ i, hi, x, hx, rfl ⟩ ; rw [ convexHull_insert ] at hi; norm_num at hi;
          · rcases hi with ⟨ j, hj, hi ⟩ ; rw [ segment_eq_image ] at hj hi; norm_num at hj hi;
            rcases hj with ⟨ y, ⟨ hy₀, hy₁ ⟩, rfl ⟩ ; rcases hi with ⟨ z, ⟨ hz₀, hz₁ ⟩, rfl ⟩ ; exact ⟨ 1 - x, x * ( 1 - z ), x * z * ( 1 - y ), x * z * y, by linarith, by nlinarith, by nlinarith [ mul_nonneg hx.1 hz₀ ], by nlinarith [ mul_nonneg hx.1 hz₀ ], by nlinarith, by ext ; simpa using by ring ⟩ ;
          · norm_num;
        · norm_num;
      -- Since $f$ is linear, we have $f(p_of_subset_of_subset) = a * f(O) + b * f(A_{n+1}) + c * f(O') + d * f(A'_{n+1})$.
      have h_f_linear : (separating_functional n) p_of_subset_of_subset = a * (separating_functional n) O_point + b * (separating_functional n) (A_seq (n + 1)) + c * (separating_functional n) O_prime + d * (separating_functional n) (reflection (A_seq (n + 1))) := by
        rw [ habcd.2, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul ];
        rfl;
      -- Since $f(O) = 0$ and $f(A_{n+1}) = 0$, we have $f(p_of_subset_of_subset) = c * f(O') + d * f(A'_{n+1})$.
      have h_f_simplified : (separating_functional n) p_of_subset_of_subset = c * (separating_functional n) O_prime + d * (separating_functional n) (reflection (A_seq (n + 1))) := by
        have h_f_simplified : (separating_functional n) O_point = 0 ∧ (separating_functional n) (A_seq (n + 1)) = 0 := by
          exact ⟨ by simpa using separating_functional_properties n |>.1, by simpa using separating_functional_properties n |>.2.1 ⟩;
        rw [ h_f_linear, h_f_simplified.1, h_f_simplified.2, MulZeroClass.mul_zero, MulZeroClass.mul_zero, zero_add, zero_add ];
      -- Since $f(O') = f(A'_{n+1})$ and $f(O') \neq 0$, we have $c + d = 0$.
      have h_cd_zero : c + d = 0 := by
        have h_cd_zero : (separating_functional n) O_prime = (separating_functional n) (reflection (A_seq (n + 1))) ∧ (separating_functional n) O_prime ≠ 0 := by
          exact separating_functional_values n;
        grind;
      norm_num [ show c = 0 by linarith, show d = 0 by linarith ] at *;
      exact ⟨ a, b, ha, hb, habcd.1, by simp [ habcd.2 ] ⟩;
    · refine' ⟨ _, _ ⟩;
      · -- Since $p$ is in the segment connecting $O$ and $A_{n+1}$, it is also in the parallelogram defined by $O$, $A_{n+1}$, $O'$, and $A_{n+1}'$.
        have h_segment_in_parallelogram : segment ℝ O_point (A_seq (n + 1)) ⊆ Parallelogram (A_seq (n + 1)) := by
          exact segment_subset_convexHull ( by norm_num ) ( by norm_num );
        exact h_segment_in_parallelogram hp;
      · obtain ⟨ t, ht ⟩ := hp;
        rcases ht with ⟨ u, ht, hu, htu, rfl ⟩ ; simp +decide [ *, separating_functional ];
        unfold O_point; norm_num; ring;
  -- The closure of $S_{seq} n$ is the segment $[O, A_{n+1}]$.
  have h_closure : closure (S_seq n) = segment ℝ O_point (A_seq (n + 1)) := by
    exact closure_S_seq n;
  exact fun p hp => h_closure.symm ▸ h_segment.subset ⟨ hp.2, h_sep_zero p hp ⟩

/-
A_{n+1} is in S_seq_refl (n-1).
-/
lemma A_succ_mem_S_seq_refl_pred (n : ℕ) (h : n > 0) : A_seq (n + 1) ∈ S_seq_refl (n - 1) := by
  convert A_seq_between n using 1 ; cases n <;> tauto;

/-
The reflection of A_{n+1} is in S_seq (n-1).
-/
lemma A_succ_refl_mem_S_seq_pred (n : ℕ) (h : n > 0) : reflection (A_seq (n + 1)) ∈ S_seq (n - 1) := by
  -- Apply the reflectionInvolution lemma to rewrite reflection (reflection (A_seq (n+1))) as A_seq (n+1) and then use the fact that A_seq (n+1) is in S_seq_refl (n-1).
  have h_reflect : A_seq (n + 1) ∈ S_seq_refl (n - 1) := by
    exact A_succ_mem_S_seq_refl_pred n h;
  obtain ⟨ t, ht₁, ht₂ ⟩ := h_reflect;
  use t, ht₁;
  simp_all +decide [ ← ht₂.2.2.2, reflection ];
  ext i ; fin_cases i <;> norm_num [ O_point, O_prime ] <;> ring_nf;
  · linarith!;
  · rw [ show t = 1 - ht₁ by linarith ] ; ring!

/-
L is disjoint from O and O'.
-/
lemma L_disjoint_O_O_prime (L : Set Point) (hL_region : L ⊆ Region_R) : O_point ∉ L ∧ O_prime ∉ L := by
  refine ⟨ fun h => ?_, fun h => ?_ ⟩ <;> have := hL_region h <;> norm_num [ Region_R ] at this;
  · exact this.1.ne' ( by unfold O_point; norm_num );
  · exact this.2.2.2.not_ge ( by norm_num [ show O_prime 1 = 1 / 2 by rfl ] )

/-
The vertices A_{n+1} and its reflection are not in L.
-/
lemma L_disjoint_vertices (n : ℕ) (L : Set Point) (hL_disj : ∀ s ∈ S_collection, Disjoint L s) (hL_region : L ⊆ Region_R) :
  A_seq (n + 1) ∉ L ∧ reflection (A_seq (n + 1)) ∉ L := by
    constructor <;> intro h0;
    · rcases n with ( _ | n ) <;> simp_all +decide [ Set.disjoint_left ];
      · -- By definition of $A_seq$, we know that $A_seq 1$ lies on the segment $O' (reflection A_0)$.
        have hA1_segment : A_seq 1 ∈ segment ℝ O_prime (reflection A_0) := by
          convert A_seq_mem_closed_segment 0 using 1;
        -- Since $A_seq 1$ lies on the segment $O' (reflection A_0)$, its y-coordinate is $1/2$.
        have hA1_y : (A_seq 1) 1 = 1 / 2 := by
          obtain ⟨ a, b, ha, hb, hab, h ⟩ := hA1_segment;
          have := congr_fun h 1; norm_num [ O_prime, reflection, A_0 ] at *; nlinarith;
        exact absurd ( hL_region h0 ) ( by rintro ⟨ h1, h2, h3, h4 ⟩ ; linarith );
      · exact hL_disj _ ( Set.mem_union_left _ <| Set.mem_union_right _ ⟨ n, rfl ⟩ ) h0 ( by simpa using A_succ_mem_S_seq_refl_pred ( n + 1 ) ( Nat.succ_pos _ ) );
    · rcases n <;> simp_all +decide [ Set.disjoint_left ];
      · -- By definition of $A_seq$, we know that $A_seq 1$ is the point on $[O', A_0']$ such that $|O - A_seq 1| = 1$.
        obtain ⟨t, ht⟩ : ∃ t : ℝ, t ∈ Set.Ioo 0 1 ∧ A_seq 1 = O_prime + t • (reflection A_0 - O_prime) := by
          have hA1 : A_seq 1 ∈ openSegment ℝ O_prime (reflection A_0) := by
            convert A_seq_in_open_segment 0 using 1;
          rw [ openSegment_eq_image ] at hA1;
          obtain ⟨ t, ht, h ⟩ := hA1; exact ⟨ t, ht, by ext i; have := congr_fun h i; norm_num at *; linarith ⟩ ;
        have := hL_region h0; unfold Region_R at this; norm_num [ ht, A_0, O_prime, reflection ] at this;
      · exact hL_disj _ ( Or.inl <| Or.inl <| ⟨ _, rfl ⟩ ) h0 ( A_succ_refl_mem_S_seq_pred _ <| Nat.succ_pos _ )

/-
If L is disjoint from the open segment and the endpoints, it is disjoint from the closed segment.
-/
lemma disjoint_segment_of_disjoint_open_endpoints (L : Set Point) (a b : Point) :
  Disjoint L (openSegment ℝ a b) → a ∉ L → b ∉ L → Disjoint L (segment ℝ a b) := by
    intros h_disjoint h_a h_b
    simp [segment_eq_image_lineMap] at *;
    norm_num [ Set.disjoint_left, Set.mem_image ] at *;
    intro x hx y hy₁ hy₂ hy₃; specialize @h_disjoint x hx; simp_all +decide [ openSegment_eq_image ] ;
    cases lt_or_eq_of_le hy₁ <;> cases lt_or_eq_of_le hy₂ <;> simp_all +decide [ AffineMap.lineMap_apply ];
    · exact h_disjoint y ‹_› ‹_› ( by ext i; have := congr_fun hy₃ i; norm_num at *; linarith );
    · subst_vars; exact h_a ( by simpa [ add_comm ] using hx ) ;

/-
L is disjoint from the closures of S_seq n and S_seq_refl n.
-/
lemma L_disjoint_boundaries (n : ℕ) (L : Set Point)
  (hL_disj : ∀ s ∈ S_collection, Disjoint L s)
  (hL_region : L ⊆ Region_R) :
  Disjoint L (closure (S_seq n)) ∧ Disjoint L (closure (S_seq_refl n)) := by
    apply And.intro;
    · have hS_seq_disjoint : Disjoint L (openSegment ℝ O_point (A_seq (n + 1))) ∧ O_point ∉ L ∧ A_seq (n + 1) ∉ L := by
        exact ⟨ hL_disj _ <| Set.mem_union_left _ <| Set.mem_union_left _ ⟨ n, rfl ⟩, fun h => L_disjoint_O_O_prime L hL_region |>.1 h, fun h => L_disjoint_vertices n L hL_disj hL_region |>.1 h ⟩;
      convert disjoint_segment_of_disjoint_open_endpoints L O_point ( A_seq ( n + 1 ) ) hS_seq_disjoint.1 hS_seq_disjoint.2.1 hS_seq_disjoint.2.2 using 1;
      exact closure_S_seq n;
    · have hL_disjoint_vertices_refl : O_prime ∉ L ∧ reflection (A_seq (n + 1)) ∉ L := by
        exact ⟨ fun h => L_disjoint_O_O_prime L hL_region |>.2 h, fun h => L_disjoint_vertices n L hL_disj hL_region |>.2 h ⟩;
      have hL_disjoint_open_refl : Disjoint L (openSegment ℝ O_prime (reflection (A_seq (n + 1)))) := by
        exact hL_disj _ ( Set.mem_union_left _ <| Set.mem_union_right _ <| ⟨ n, rfl ⟩ );
      have hL_disjoint_closure_refl : Disjoint L (segment ℝ O_prime (reflection (A_seq (n + 1)))) := by
        apply disjoint_segment_of_disjoint_open_endpoints L O_prime (reflection (A_seq (n + 1))) hL_disjoint_open_refl hL_disjoint_vertices_refl.left hL_disjoint_vertices_refl.right;
      convert hL_disjoint_closure_refl using 1;
      unfold S_seq_refl; ext; simp [segment]

/-
The triangle OA'P is a closed set.
-/
lemma Triangle_OA_prime_P_is_closed (n : ℕ) : IsClosed (Triangle_OA_prime_P n) := by
  convert Triangle_OA_prime_P_isClosed n using 1

/-
The parallelogram sequence consists of closed sets.
-/
lemma Parallelogram_seq_is_closed (n : ℕ) : IsClosed (Parallelogram_seq n) := by
  -- The convex hull of a finite set of points in a finite-dimensional vector space is compact.
  have h_convex_hull_compact : IsCompact (convexHull ℝ ({O_point, A_seq n, O_prime, reflection (A_seq n)} : Set Point)) := by
    have h_finite : Set.Finite ({O_point, A_seq n, O_prime, reflection (A_seq n)} : Set Point) := by
      exact Set.toFinite _;
    exact h_finite.isCompact_convexHull;
  exact h_convex_hull_compact.isClosed

/-
The reflected triangle is a closed set.
-/
lemma Triangle_seq_refl_is_closed (n : ℕ) : IsClosed (Triangle_seq_refl n) := by
  -- The reflection of the triangle OA'P is the convex hull of O', A_n, and the reflection of A_{n+1}, which are three points.
  have h_triangle_refl : Triangle_seq_refl n = convexHull ℝ {O_prime, A_seq n, reflection (A_seq (n + 1))} := by
    exact Triangle_seq_refl_eq_convexHull n;
  rw [ h_triangle_refl ];
  -- The convex hull of a finite set of points in Euclidean space is closed.
  have h_convex_hull_closed : ∀ (s : Finset Point), IsClosed (convexHull ℝ (s : Set Point)) := by
    -- The convex hull of a finite set of points in Euclidean space is compact.
    have h_convex_hull_compact : ∀ (s : Finset Point), IsCompact (convexHull ℝ (s : Set Point)) := by
      exact fun s => s.finite_toSet.isCompact_convexHull;
    exact fun s => IsCompact.isClosed ( h_convex_hull_compact s );
  convert h_convex_hull_closed { O_prime, A_seq n, reflection ( A_seq ( n + 1 ) ) } using 1;
  norm_num [ Set.insert_subset_iff ]

/-
The intersection of the reflected triangle and the next parallelogram is contained in the closure of the reflected segment.
-/
lemma seam_2_subset (n : ℕ) : Triangle_seq_refl n ∩ Parallelogram_seq (n + 1) ⊆ closure (S_seq_refl n) := by
  -- Let $x \in Triangle\_seq\_refl n \cap Parallelogram\_seq (n + 1)$.
  intro x hx
  obtain ⟨hx_triangle, hx_parallelogram⟩ := hx
  obtain ⟨y, hy_triangle, rfl⟩ := hx_triangle;
  -- Since $y \in Triangle_OA_prime_P n \cap Parallelogram_seq (n + 1)$, by `Tn_inter_Pn_subset_closure_S_seq`, we have $y \in closure (S_seq n)$.
  have hy_closure_S_seq : y ∈ closure (S_seq n) := by
    -- Since $y \in Triangle_OA_prime_P n$ and $reflection y \in Parallelogram_seq (n + 1)$, we have $y \in Parallelogram_seq (n + 1)$ by the symmetry of the parallelogram.
    have hy_parallelogram : y ∈ Parallelogram_seq (n + 1) := by
      convert Parallelogram_symmetric _ _ hx_parallelogram using 1;
      exact Eq.symm ( reflection_involution y );
    exact Tn_inter_Pn_subset_closure_S_seq n ⟨ hy_triangle, hy_parallelogram ⟩;
  -- Since reflection is a continuous function, applying it to the closure of S_seq n should give me the closure of the reflection of S_seq n.
  have h_reflection_closure : reflection '' closure (S_seq n) ⊆ closure (reflection '' S_seq n) := by
    intro z hz
    obtain ⟨w, hw_closure, rfl⟩ := hz
    have hw_closure_S_seq : w ∈ closure (S_seq n) := hw_closure
    have h_reflection_closure_S_seq : reflection w ∈ closure (reflection '' S_seq n) := by
      have h_reflection_closure_S_seq : Continuous reflection := by
        exact continuous_pi_iff.mpr fun i => by fin_cases i <;> [ exact continuous_const.sub ( continuous_apply 0 ) ; exact continuous_const.sub ( continuous_apply 1 ) ] ;
      exact mem_closure_image h_reflection_closure_S_seq.continuousAt hw_closure_S_seq
    exact h_reflection_closure_S_seq;
  convert h_reflection_closure ( Set.mem_image_of_mem _ hy_closure_S_seq ) using 1;
  congr! 1;
  ext; simp [S_seq_refl, S_seq];
  constructor <;> intro h <;> simp_all +decide [ openSegment_eq_image ];
  · obtain ⟨ a, ha, rfl ⟩ := h; use a; simp +decide [ *, reflection ] ;
    ext i; fin_cases i <;> norm_num [ O_point, O_prime ] <;> ring;
  · obtain ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ := h; use a; simp +decide [ *, reflection ] ; ring_nf;
    ext i; fin_cases i <;> norm_num [ O_prime, O_point ] <;> ring;

/-
L is disjoint from the intersection of the triangle and the next parallelogram.
-/
lemma L_disjoint_seam_1 (n : ℕ) (L : Set Point)
  (hL_disj : ∀ s ∈ S_collection, Disjoint L s)
  (hL_region : L ⊆ Region_R) :
  Disjoint L (Triangle_OA_prime_P n ∩ Parallelogram_seq (n + 1)) := by
    exact Set.disjoint_left.mpr fun x hx₁ hx₂ => Set.disjoint_left.mp ( L_disjoint_boundaries n L hL_disj hL_region |>.1 ) hx₁ ( Tn_inter_Pn_subset_closure_S_seq n hx₂ )

/-
L is disjoint from the intersection of the reflected triangle and the next parallelogram.
-/
lemma L_disjoint_seam_2 (n : ℕ) (L : Set Point)
  (hL_disj : ∀ s ∈ S_collection, Disjoint L s)
  (hL_region : L ⊆ Region_R) :
  Disjoint L (Triangle_seq_refl n ∩ Parallelogram_seq (n + 1)) := by
    have hL_disjoint_seam_2 : Disjoint L (closure (S_seq_refl n)) := by
      exact L_disjoint_boundaries n L hL_disj hL_region |>.2;
    exact hL_disjoint_seam_2.mono_right ( seam_2_subset n )

/-
The intersection of the triangle and its reflection is contained in the next parallelogram.
-/
lemma Triangle_inter_Triangle_refl_subset_Parallelogram_succ (n : ℕ) : Triangle_OA_prime_P n ∩ Triangle_seq_refl n ⊆ Parallelogram_seq (n + 1) := by
  -- Since the intersection of the triangle and its reflection is a subset of the segment connecting O and O', and this segment is contained in the next parallelogram, we can conclude the proof.
  have h_inter_subset_segment : Triangle_OA_prime_P n ∩ Triangle_seq_refl n ⊆ segment ℝ O_point O_prime := by
    -- Since the intersection of the triangle and its reflection is a subset of the segment connecting O and O', we can conclude the proof by showing that any point in this intersection satisfies the condition for being in the segment.
    intros p hp
    obtain ⟨hp_triangle, hp_reflection⟩ := hp;
    -- Since p is in the intersection of T_n and T'_n, it must satisfy both conditions: signed_dist_from_diagonal p ≤ 0 and signed_dist_from_diagonal p ≥ 0. Therefore, signed_dist_from_diagonal p = 0.
    have h_signed_dist_zero : signed_dist_from_diagonal p = 0 := by
      -- By definition of $Triangle_seq_refl$, there exists $q \in Triangle_OA_prime_P n$ such that $p = reflection q$.
      obtain ⟨q, hq_triangle, rfl⟩ : ∃ q ∈ Triangle_OA_prime_P n, p = reflection q := by
        unfold Triangle_seq_refl at hp_reflection; aesop;
      have h_sign_opposite : signed_dist_from_diagonal (reflection q) = -signed_dist_from_diagonal q := by
        unfold reflection; unfold signed_dist_from_diagonal; norm_num; ring;
      by_cases hn : Even n <;> simp_all +decide
      · linarith [ Tn_subset_halfplane n |>.1 hn q hq_triangle, Tn_subset_halfplane n |>.1 hn ( reflection q ) hp_triangle ];
      · have := Tn_subset_halfplane n |>.2 hn q hq_triangle; ( have := Tn_subset_halfplane n |>.2 hn ( reflection q ) hp_triangle; ( norm_num [ signed_dist_from_diagonal ] at *; linarith; ) );
    apply dist_from_diagonal_eq_zero_implies_on_segment;
    · -- Since $p \in T_n$ and $T_n \subset P_n$, we have $p \in P_n$.
      have hp_in_Pn : p ∈ Parallelogram_seq n := by
        exact ( Parallelogram_decomposition_subset n ) ( Set.mem_union_left _ <| Set.mem_union_left _ hp_triangle );
      exact Set.mem_of_subset_of_mem ( show Parallelogram_seq n ⊆ Parallelogram_seq 0 from by exact Nat.recOn n ( by tauto ) fun n ihn => by exact Set.Subset.trans ( Parallelogram_seq_subset n ) ihn ) hp_in_Pn;
    · exact abs_eq_zero.mpr h_signed_dist_zero;
  exact Set.Subset.trans h_inter_subset_segment ( Set.Subset.trans ( segment_O_O_prime_subset_inter_Parallelogram_seq ) ( Set.iInter_subset _ _ ) )

/-
If L is in the n-th parallelogram and disjoint from S, it is in the (n+1)-th parallelogram.
-/
lemma L_subset_Parallelogram_succ (n : ℕ) (L : Set Point) (hL_unit : IsUnitSegment L)
  (hL_subset : L ⊆ Parallelogram_seq n)
  (hL_disj : ∀ s ∈ S_collection, Disjoint L s)
  (hL_region : L ⊆ Region_R) :
  L ⊆ Parallelogram_seq (n + 1) := by
    -- By `connected_subset_union_disjoint_inter`, `L ⊆ T_n` or `L ⊆ P_{n+1} ∪ T'_n`.
    have hL_subset_T_or_P : L ⊆ Triangle_OA_prime_P n ∨ L ⊆ Parallelogram_seq (n + 1) ∪ Triangle_seq_refl n := by
      have hL_disjoint_inter : Disjoint L ((Triangle_OA_prime_P n) ∩ (Parallelogram_seq (n + 1) ∪ Triangle_seq_refl n)) := by
        have hL_disjoint_inter : Disjoint L ((Triangle_OA_prime_P n) ∩ (Parallelogram_seq (n + 1))) := by
          apply L_disjoint_seam_1 n L hL_disj hL_region;
        have hL_disjoint_inter : Disjoint L ((Triangle_OA_prime_P n) ∩ (Triangle_seq_refl n)) := by
          have hL_disjoint_inter : (Triangle_OA_prime_P n) ∩ (Triangle_seq_refl n) ⊆ Parallelogram_seq (n + 1) := by
            exact Triangle_inter_Triangle_refl_subset_Parallelogram_succ n;
          exact Set.disjoint_left.mpr fun x hx₁ hx₂ => by have := hL_disjoint_inter hx₂; exact Set.disjoint_left.mp ‹Disjoint L ( Triangle_OA_prime_P n ∩ Parallelogram_seq ( n + 1 ) ) › hx₁ ⟨ hx₂.1, this ⟩ ;
        simp_all +decide [ Set.inter_union_distrib_left, Set.disjoint_left ];
      apply connected_subset_union_disjoint_inter;
      · exact Triangle_OA_prime_P_is_closed n;
      · exact IsClosed.union ( Parallelogram_seq_is_closed _ ) ( Triangle_seq_refl_is_closed _ );
      · obtain ⟨ x, y, hxy, h ⟩ := hL_unit;
        rw [ h ];
        rw [ openSegment_eq_image ];
        exact ⟨ Set.Nonempty.image _ ⟨ 1 / 2, by norm_num ⟩, isPreconnected_Ioo.image _ <| Continuous.continuousOn <| by continuity ⟩;
      · intro x hx; specialize hL_subset hx; rw [ Parallelogram_decomposition_eq ] at hL_subset; aesop;
      · assumption;
    cases' hL_subset_T_or_P with h h;
    · -- By `Triangle_OA_prime_P_unit_segment_eq_S_seq`, `L = S_seq n`.
      have hL_eq_S_seq : L = S_seq n := by
        exact Triangle_OA_prime_P_unit_segment_eq_S_seq_v2 n L hL_unit h;
      have := hL_disj ( S_seq n ) ; simp_all +decide [ Set.disjoint_left ] ;
      cases n <;> simp_all +decide [ S_collection ];
    · -- By `connected_subset_union_disjoint_inter`, `L \subseteq P_{n+1}` or `L \subseteq T'_n`.
      have hL_subset_P_or_T : L ⊆ Parallelogram_seq (n + 1) ∨ L ⊆ Triangle_seq_refl n := by
        have hL_subset_P_or_T : L ⊆ Parallelogram_seq (n + 1) ∨ L ⊆ Triangle_seq_refl n := by
          have h_closed : IsClosed (Parallelogram_seq (n + 1)) ∧ IsClosed (Triangle_seq_refl n) := by
            exact ⟨ Parallelogram_seq_is_closed _, Triangle_seq_refl_is_closed _ ⟩
          have hL_subset_P_or_T : L ⊆ Parallelogram_seq (n + 1) ∨ L ⊆ Triangle_seq_refl n := by
            have h_connected : IsConnected L := by
              obtain ⟨ v, hv_unit, hv ⟩ := hL_unit;
              rw [ hv.2 ];
              convert isConnected_Ioo ( show ( 0 : ℝ ) < 1 by norm_num ) |> ( fun h => h.image _ _ ) using 1;
              rotate_left;
              use fun t => ( 1 - t ) • v + t • hv_unit;
              · fun_prop (disch := norm_num);
              · exact openSegment_eq_image ℝ v hv_unit
            have h_disjoint : Disjoint L (Parallelogram_seq (n + 1) ∩ Triangle_seq_refl n) := by
              have h_disjoint : Disjoint L (Triangle_seq_refl n ∩ Parallelogram_seq (n + 1)) := by
                exact L_disjoint_seam_2 n L hL_disj hL_region;
              simpa only [ Set.inter_comm ] using h_disjoint;
            have := connected_subset_union_disjoint_inter ( Parallelogram_seq ( n + 1 ) ) ( Triangle_seq_refl n ) L h_closed.1 h_closed.2 h_connected h h_disjoint; aesop;
          exact hL_subset_P_or_T;
        exact hL_subset_P_or_T
      cases' hL_subset_P_or_T with h h;
      · assumption;
      · -- By `Triangle_seq_refl_unit_segment_eq_S_seq_refl`, `L = S_seq_refl n`.
        have hL_eq_S_seq_refl : L = S_seq_refl n := by
          apply Triangle_seq_refl_unit_segment_eq_S_seq_refl n L hL_unit h;
        specialize hL_disj ( S_seq_refl n ) ; simp_all +decide ;
        unfold S_collection at hL_disj; aesop;

/-
S_collection is blocking in Region_R.
-/
lemma S_collection_is_blocking : IsBlocking S_collection Region_R := by
  -- Let `L` be a unit segment in `Region_R`.
  intro L hL_unit hL_subset
  by_contra h_disjoint;
  -- By induction using `L_subset_Parallelogram_succ`, `L ⊆ Parallelogram_seq n` for all `n`.
  have hL_parallelogram : ∀ n, L ⊆ Parallelogram_seq n := by
    intro n
    induction' n with n ih;
    · exact hL_subset.trans ( Region_subset_P0 );
    · apply L_subset_Parallelogram_succ n L hL_unit ih (by
      exact fun s hs => by push_neg at h_disjoint; exact h_disjoint s hs |> Disjoint.symm;) hL_subset;
  -- Thus `L ⊆ ⋂ n, Parallelogram_seq n`.
  have hL_inter : L ⊆ ⋂ n, Parallelogram_seq n := by
    exact Set.subset_iInter hL_parallelogram;
  -- By `Inter_Parallelogram_seq_eq_segment_O_O_prime`, `L ⊆ segment O O'`.
  have hL_segment : L ⊆ segment ℝ O_point O_prime := by
    exact hL_inter.trans ( by rw [ Inter_Parallelogram_seq_eq_segment_O_O_prime ] );
  -- By `S_inf_blocks_on_segment_O_O_prime`, `L` intersects `S_inf`.
  have hL_inter_S_inf : ¬Disjoint L S_inf := by
    apply S_inf_blocks_on_segment_O_O_prime L hL_unit hL_segment;
  exact h_disjoint ⟨ S_inf, by unfold S_collection; aesop, by simpa only [ disjoint_comm ] using hL_inter_S_inf ⟩

/-
Definitions for Corollary 2: The open unit square, the shifted collection, and the combined collection S_cor2.
-/
def Region_Square : Set Point := {p | 0 < p 0 ∧ p 0 < 1 ∧ 0 < p 1 ∧ p 1 < 1}

def S_shifted : Set (Set Point) := {s | ∃ t ∈ S_collection, s = (fun p => p + (![0, 1/2] : Point)) '' t}

def S_cor2 : Set (Set Point) := S_collection ∪ S_shifted ∪ {H_mid}

/-
The upper region (0,1) x (1/2, 1).
-/
def Region_Upper : Set Point := {p | 0 < p 0 ∧ p 0 < 1 ∧ 1/2 < p 1 ∧ p 1 < 1}

/-
The shifted collection is a disjoint collection.
-/
lemma S_shifted_is_disjoint_collection : IsDisjointCollection S_shifted := by
  constructor;
  · intro s hs_shifted
    obtain ⟨t, ht_S_collection, rfl⟩ := hs_shifted
    have ht_unit : IsUnitSegment t := by
      exact S_collection_is_unit_segment t ht_S_collection
    exact (by
    obtain ⟨a, b, hab, ht⟩ := ht_unit;
    refine' ⟨ _, _, _ ⟩ <;> norm_num [ ht, openSegment_eq_image ];
    exact fun i => if i = 0 then a 0 else a 1 + 1 / 2
    exact fun i => if i = 0 then b 0 else b 1 + 1 / 2;
    norm_num [ dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two ] at *;
    simp_all +decide [ Set.ext_iff, openSegment_eq_image ];
    simp +decide [ funext_iff, Fin.forall_fin_two, Matrix.vecHead, Matrix.vecTail ];
    exact fun x => ⟨ fun ⟨ y, hy, hx₀, hx₁ ⟩ => ⟨ y, hy, hx₀, by linear_combination hx₁ ⟩, fun ⟨ y, hy, hx₀, hx₁ ⟩ => ⟨ y, hy, hx₀, by linear_combination hx₁ ⟩ ⟩);
  · -- By definition of $S_shifted$, if $s \in S_shifted$ and $t \in S_shifted$, then there exist $t1, t2 \in S_collection$ such that $s = t1 + (0, 1/2)$ and $t = t2 + (0, 1/2)$.
    intro s t hs ht hne
    obtain ⟨t1, ht1, rfl⟩ := hs
    obtain ⟨t2, ht2, rfl⟩ := ht;
    -- Since $t1$ and $t2$ are disjoint, their images under the translation by $(0, 1/2)$ are also disjoint.
    have h_disjoint : Disjoint t1 t2 := by
      exact S_collection_pairwise_disjoint t1 t2 ht1 ht2 ( by aesop );
    simp_all +decide [ Set.disjoint_left ];
    intro a ha x hx h₁ h₂; specialize h_disjoint ha; simp_all +decide [ Matrix.vecHead, Matrix.vecTail ] ;
    exact h_disjoint ( by convert hx using 1; ext i; fin_cases i <;> aesop )

/-
The shifted collection is blocking in the upper region.
-/
lemma S_shifted_is_blocking : IsBlocking S_shifted Region_Upper := by
  intro L hL_unit hL_subset;
  -- Let $v = (0, 1/2)$.
  set v : Point := ![0, 1 / 2];
  -- Let $L' = L - v$.
  set L' : Set Point := {p | p + v ∈ L};
  -- Since $L'$ is a unit segment in $Region_R$, by the blocking property of $S_collection$, there exists $s \in S_collection$ such that $L'$ intersects $s$.
  obtain ⟨s, hs⟩ : ∃ s ∈ S_collection, ¬Disjoint s L' := by
    apply S_collection_is_blocking L';
    · obtain ⟨ x, y, hxy, hL' ⟩ := hL_unit;
      use x - v, y - v;
      simp_all +decide [ dist_eq_norm, openSegment_eq_image ];
      ext; simp [L', hL'];
      constructor <;> rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, ha₃ ⟩ <;> use a <;> simp_all +decide;
      · convert congr_arg ( fun z => z - v ) ha₃ using 1 <;> ext i <;> fin_cases i <;> norm_num <;> ring;
      · exact ha₃ ▸ by ext i; fin_cases i <;> norm_num <;> ring;
    · intro p hp
      have hL'_subset : p + v ∈ Region_Upper := by
        exact hL_subset hp;
      exact ⟨ by have := hL'_subset.1; norm_num [ v ] at this; linarith, by have := hL'_subset.2.1; norm_num [ v ] at this; linarith, by have := hL'_subset.2.2.1; norm_num [ v ] at this; linarith, by have := hL'_subset.2.2.2; norm_num [ v ] at this; linarith ⟩;
  refine' ⟨ _, ⟨ s, hs.1, rfl ⟩, _ ⟩;
  simp_all +decide [ Set.disjoint_left ];
  norm_num +zetaDelta at *;
  convert hs.2 using 4 ; ext i ; fin_cases i <;> norm_num [ Matrix.vecHead, Matrix.vecTail ]

/-
If a connected set in the unit square is disjoint from the horizontal middle segment, it must be entirely in the lower half or entirely in the upper half.
-/
lemma connected_subset_split (L : Set Point) (hL_conn : IsConnected L) (hL_sub : L ⊆ Region_Square) (hL_disj : Disjoint L H_mid) : L ⊆ Region_R ∨ L ⊆ Region_Upper := by
  -- Region_Square minus H_mid is the union of Region_R and Region_Upper.
  have h_union : Region_Square \ H_mid = Region_R ∪ Region_Upper := by
    ext p
    simp [Region_Square, H_mid, Region_R, Region_Upper];
    constructor <;> intro h <;> simp_all +decide [ openSegment_eq_image ];
    · contrapose! h;
      exact fun hp => ⟨ p 0, hp.1, hp.2.1, by ext i; fin_cases i <;> norm_num <;> linarith! ⟩;
    · rcases h with ( ⟨ h₀, h₁, h₂, h₃ ⟩ | ⟨ h₀, h₁, h₂, h₃ ⟩ ) <;> refine' ⟨ ⟨ h₀, h₁, by linarith, by linarith ⟩, _ ⟩ <;> intro x hx₁ hx₂ hx₃ <;> have := congr_fun hx₃ 0 <;> have := congr_fun hx₃ 1 <;> norm_num at * <;> linarith;
  -- Since L is connected and a subset of the union of two disjoint open sets, it must be entirely in one of them.
  have h_connected_subset : IsConnected L → L ⊆ Region_R ∪ Region_Upper → L ⊆ Region_R ∨ L ⊆ Region_Upper := by
    intro hL_conn hL_sub
    have h_connected_subset : IsConnected L → L ⊆ Region_R ∪ Region_Upper → L ⊆ Region_R ∨ L ⊆ Region_Upper := by
      intro hL_conn hL_sub
      have h_disjoint : Disjoint Region_R Region_Upper := by
        exact Set.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ hx₁.2.2.2, hx₂.2.2.1 ] ;
      have h_open : IsOpen Region_R ∧ IsOpen Region_Upper := by
        exact ⟨ isOpen_Ioi.preimage ( continuous_apply 0 ) |> IsOpen.inter <| isOpen_Iio.preimage ( continuous_apply 0 ) |> IsOpen.inter <| isOpen_Ioi.preimage ( continuous_apply 1 ) |> IsOpen.inter <| isOpen_Iio.preimage ( continuous_apply 1 ), isOpen_Ioi.preimage ( continuous_apply 0 ) |> IsOpen.inter <| isOpen_Iio.preimage ( continuous_apply 0 ) |> IsOpen.inter <| isOpen_Ioi.preimage ( continuous_apply 1 ) |> IsOpen.inter <| isOpen_Iio.preimage ( continuous_apply 1 ) ⟩
      have h_connected_subset : ∀ {U V : Set Point}, IsOpen U → IsOpen V → Disjoint U V → IsConnected L → L ⊆ U ∪ V → L ⊆ U ∨ L ⊆ V := by
        intros U V hU hV h_disjoint hL_conn hL_sub
        have h_connected_subset : IsConnected L → L ⊆ U ∪ V → L ⊆ U ∨ L ⊆ V := by
          intros hL_conn hL_sub
          have h_connected_subset : IsPreconnected L → L ⊆ U ∪ V → L ⊆ U ∨ L ⊆ V := by
            (expose_names;
              exact fun a a_1 ↦ IsPreconnected.subset_or_subset hU hV h_disjoint hL_sub_4 a);
          exact h_connected_subset hL_conn.isPreconnected hL_sub;
        exact h_connected_subset hL_conn hL_sub;
      exact h_connected_subset h_open.1 h_open.2 h_disjoint hL_conn hL_sub;
    exact h_connected_subset hL_conn hL_sub;
  exact h_connected_subset hL_conn ( h_union ▸ fun x hx => ⟨ hL_sub hx, fun hx' => hL_disj.le_bot ⟨ hx, hx' ⟩ ⟩ )

/-
The horizontal middle segment is a unit segment.
-/
lemma H_mid_is_unit_segment : IsUnitSegment H_mid := by
  refine' ⟨ _, _, _, rfl ⟩;
  norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ]

/-
The lower region (y < 1/2) and the upper region (y > 1/2) are disjoint.
-/
lemma regions_disjoint_R_Upper : Disjoint Region_R Region_Upper := by
  exact Set.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ hx₁.2.2.2, hx₂.2.2.1 ] ;

/-
The horizontal middle segment is disjoint from the lower region.
-/
lemma H_mid_disjoint_Region_R : Disjoint H_mid Region_R := by
  -- Since $H_{\text{mid}}$ consists of points with $y = 1/2$ and $Region_R$ consists of points with $y < 1/2$, they are disjoint.
  simp [H_mid, Region_R];
  norm_num [ Set.disjoint_left, openSegment_eq_image ];
  rintro a x hx₁ hx₂ rfl hx₃ hx₄ hx₅; norm_num [ Algebra.smul_def ] at * ; linarith;

/-
The horizontal middle segment is disjoint from the upper region.
-/
lemma H_mid_disjoint_Region_Upper : Disjoint H_mid Region_Upper := by
  -- To prove disjointness, we show that no point in H_mid can be in Region_Upper.
  simp [H_mid, Region_Upper];
  unfold openSegment; norm_num [ Set.disjoint_left ] ;
  intros; subst_vars; norm_num [ ← List.ofFn_inj ] at *; linarith;

/-
Any segment in the original collection is disjoint from any segment in the shifted collection.
-/
lemma S_collection_disjoint_S_shifted : ∀ s ∈ S_collection, ∀ t ∈ S_shifted, Disjoint s t := by
  -- By definition of $S_{\text{collection}}$ and $S_{\text{shifted}}$, we know that $S_{\text{collection}} \subseteq \text{Region}_R$ and $S_{\text{shifted}} \subseteq \text{Region}_{\text{Upper}}$.
  have h_S_collection_subset_Region_R : S_collection ⊆ {s | s ⊆ Region_R} := by
    -- Apply the lemma S_collection_in_region to each element in S_collection.
    intros s hs
    apply S_collection_in_region s hs
  have h_S_shifted_subset_Region_Upper : S_shifted ⊆ {s | s ⊆ Region_Upper} := by
    intro s hs
    obtain ⟨t, htS, ht⟩ := hs
    have ht_subset : t ⊆ Region_R := h_S_collection_subset_Region_R htS
    have hs_subset : s ⊆ Region_Upper := by
      intro p hp
      rw [ht] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      have hq_upper : q ∈ Region_R := ht_subset hq
      exact (by
      exact ⟨ by have := hq_upper.1; have := hq_upper.2.1; have := hq_upper.2.2.1; have := hq_upper.2.2.2; norm_num [ ← List.ofFn_inj ] at *; linarith, by have := hq_upper.1; have := hq_upper.2.1; have := hq_upper.2.2.1; have := hq_upper.2.2.2; norm_num [ ← List.ofFn_inj ] at *; linarith, by have := hq_upper.1; have := hq_upper.2.1; have := hq_upper.2.2.1; have := hq_upper.2.2.2; norm_num [ ← List.ofFn_inj ] at *; linarith, by have := hq_upper.1; have := hq_upper.2.1; have := hq_upper.2.2.1; have := hq_upper.2.2.2; norm_num [ ← List.ofFn_inj ] at *; linarith ⟩)
    exact hs_subset;
  exact fun s hs t ht => Set.disjoint_left.mpr fun x hx hx' => by have := Set.disjoint_left.mp ( regions_disjoint_R_Upper ) ( h_S_collection_subset_Region_R hs hx ) ( h_S_shifted_subset_Region_Upper ht hx' ) ; contradiction;

/-
Any segment in the original collection is disjoint from the horizontal middle segment.
-/
lemma S_collection_disjoint_H_mid : ∀ s ∈ S_collection, Disjoint s H_mid := by
  intro s hs
  have h_s_subset_R : s ⊆ Region_R := by
    exact S_collection_in_region s hs
  have h_H_mid_disjoint_R : Disjoint H_mid Region_R := by
    -- Apply the lemma that states H_mid is disjoint from Region_R.
    apply H_mid_disjoint_Region_R
  exact Set.disjoint_left.mpr fun x hx hx' => h_H_mid_disjoint_R.le_bot ⟨hx', h_s_subset_R hx⟩

/-
Any segment in the shifted collection is disjoint from the horizontal middle segment.
-/
lemma S_shifted_disjoint_H_mid : ∀ s ∈ S_shifted, Disjoint s H_mid := by
  intro s hs
  obtain ⟨t, htS, ht⟩ := hs
  have ht_shifted : t ⊆ Region_R := by
    exact S_collection_in_region t htS;
  have ht_shifted_upper : s ⊆ Region_Upper := by
    intro p hp
    rw [ht] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have hq_upper : q ∈ Region_R := ht_shifted hq
    exact (by
    exact ⟨ by simpa using hq_upper.1, by simpa using hq_upper.2.1, by simpa using by linarith [ hq_upper.2.2.1, hq_upper.2.2.2 ], by simpa using by linarith [ hq_upper.2.2.1, hq_upper.2.2.2 ] ⟩)
  have h_disjoint_upper : Disjoint s H_mid := by
    exact Set.disjoint_left.mpr fun x hx_s hx_H_mid => by have := ht_shifted_upper hx_s; exact ( show False from by exact absurd ( H_mid_disjoint_Region_Upper ) ( by exact Set.not_disjoint_iff_nonempty_inter.mpr ⟨ x, hx_H_mid, this ⟩ ) ) ;
  exact h_disjoint_upper

/-
The combined collection S_cor2 is a disjoint collection of unit segments.
-/
lemma S_cor2_is_disjoint_collection : IsDisjointCollection S_cor2 := by
  -- We need to show that every pair of distinct segments in S_cor2 is disjoint.
  -- We can split into cases based on which segments are being considered.
  have h_disjoint : ∀ s t, s ∈ S_cor2 → t ∈ S_cor2 → s ≠ t → Disjoint s t := by
    intros s t hs ht hst;
    rcases hs with ( hs | hs | hs ) <;> rcases ht with ( ht | ht | ht ) <;> simp_all +decide
    · rcases hs with ( hs | hs ) <;> rcases ht with ( ht | ht );
      · exact S_collection_pairwise_disjoint s t hs ht hst;
      · exact S_collection_disjoint_S_shifted s hs t ht;
      · exact Disjoint.symm (S_collection_disjoint_S_shifted t ht s hs);
      · exact S_shifted_is_disjoint_collection.2 s t hs ht ( by aesop );
    · rcases hs with ( hs | hs ) <;> [ exact S_collection_disjoint_H_mid s hs; exact S_shifted_disjoint_H_mid s hs ];
    · rcases ht with ( ht | ht ) <;> [ exact Disjoint.symm (S_collection_disjoint_H_mid t ht) ; exact Disjoint.symm (S_shifted_disjoint_H_mid t ht) ];
  constructor;
  · unfold S_cor2;
    simp +zetaDelta at *;
    exact ⟨ H_mid_is_unit_segment, fun s hs => hs.elim ( fun hs => S_collection_is_unit_segment s hs ) fun hs => S_shifted_is_disjoint_collection.1 s hs ⟩;
  · assumption

/-
The combined collection S_cor2 is contained in the unit square.
-/
lemma S_cor2_in_region : IsInRegion S_cor2 Region_Square := by
  -- By definition of $S_{\text{cor2}}$, we need to show that $S_{\text{collection}} \cup S_{\text{shifted}} \cup \{H_{\text{mid}}\}$ is in the region.
  simp [IsInRegion];
  unfold S_cor2;
  simp +zetaDelta at *;
  constructor;
  · unfold H_mid Region_Square; norm_num [ Set.Ioo_subset_Ioo_iff ] ;
    intro p hp
    obtain ⟨a, b, ha, hb, hab, hp_eq⟩ := hp
    simp at *;
    norm_num [ ← hp_eq, ha, hb, hab ];
    exact ⟨ by linarith, by linarith, by linarith ⟩;
  · rintro s ( hs | hs );
    · exact S_collection_in_region s hs |> fun h => h.trans ( by
        exact fun p hp => ⟨ hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.trans_le <| by norm_num ⟩ );
    · obtain ⟨ t, ht, rfl ⟩ := hs;
      have h_shifted_subset : t ⊆ Region_R := by
        exact S_collection_in_region _ ht;
      intro p hp
      obtain ⟨ q, hq, rfl ⟩ := hp
      have hq_bounds : 0 < (q 0) ∧ (q 0) < 1 ∧ 0 < (q 1) ∧ (q 1) < 1 / 2 := by
        exact h_shifted_subset hq;
      exact ⟨ by simpa using hq_bounds.1, by simpa using hq_bounds.2.1, by simpa using by linarith, by simpa using by linarith ⟩

/-
The combined collection S_cor2 is blocking in the unit square.
-/
lemma S_cor2_is_blocking : IsBlocking S_cor2 Region_Square := by
  intro L hL_unit hL_sub
  by_cases hL_mid : ¬Disjoint L H_mid;
  · exact ⟨ H_mid, by tauto, by tauto ⟩;
  · -- Since L is disjoint from H_mid, it must be contained in either Region_R or Region_Upper (by connected_subset_split).
    have hL_region : L ⊆ Region_R ∨ L ⊆ Region_Upper := by
      have hL_region : L ⊆ Region_R ∨ L ⊆ Region_Upper := by
        have h_connected : IsConnected L := by
          obtain ⟨ x, y, hxy, rfl ⟩ := hL_unit;
          have h_connected : IsConnected (Set.Ioo (0 : ℝ) 1) := by
            exact isConnected_Ioo ( by norm_num );
          convert h_connected.image _ _ using 1;
          rotate_left;
          use fun t => ( 1 - t ) • x + t • y;
          · fun_prop;
          · ext; simp [openSegment];
            exact ⟨ fun ⟨ a, ha, b, hb, hab, h ⟩ => ⟨ b, ⟨ hb, by linarith ⟩, by simpa [ ← hab ] using h ⟩, fun ⟨ a, ⟨ ha, hb ⟩, h ⟩ => ⟨ 1 - a, by linarith, a, by linarith, by linarith, by simpa [ ← add_comm ] using h ⟩ ⟩
        have h_subset : L ⊆ Region_Square := by
          assumption
        have h_disjoint : Disjoint L H_mid := by
          exact Classical.not_not.mp hL_mid
        exact connected_subset_split L h_connected hL_sub h_disjoint;
      exact hL_region;
    cases' hL_region with hL_region hL_region;
    · -- Since L is contained in Region_R, it must intersect S_collection (by S_collection_is_blocking).
      obtain ⟨s, hs⟩ : ∃ s ∈ S_collection, ¬Disjoint s L := by
        exact Classical.not_forall_not.1 fun h => by have := S_collection_is_blocking L hL_unit hL_region; aesop;
      exact ⟨ s, Or.inl <| Or.inl hs.1, hs.2 ⟩;
    · -- Since L is contained in Region_Upper, it must intersect some segment in S_shifted (by S_shifted_is_blocking).
      obtain ⟨s, hs⟩ : ∃ s ∈ S_shifted, ¬Disjoint s L := by
        have := S_shifted_is_blocking L hL_unit hL_region; aesop;
      exact ⟨ s, Or.inl <| Or.inr hs.1, hs.2 ⟩

/-
The shifted collection is countable.
-/
lemma S_shifted_countable : Set.Countable S_shifted := by
  have h_countable : S_collection.Countable := by
    convert Set.countable_range ( fun n : ℕ => S_seq n ) |> Set.Countable.union <| Set.countable_range ( fun n : ℕ => S_seq_refl n ) |> Set.Countable.union <| Set.countable_singleton S_inf using 1;
    exact Set.ext fun x => by unfold S_collection; aesop;
  exact Set.Countable.mono ( fun s hs => by cases' hs with t ht; aesop ) ( h_countable.image _ )

/-
Define the set of sides of the unit square and the collection S_cor3.
-/
def S_sides : Set (Set Point) := {V_L, V_R, H_bot, H_top}

def S_cor3 : Set (Set Point) := S_cor2 ∪ S_sides

/-
The collection of the four sides of the unit square is a disjoint collection.
-/
lemma S_sides_is_disjoint_collection : IsDisjointCollection S_sides := by
  -- Show that the four sides of the unit square are pairwise disjoint.
  simp [S_sides, IsDisjointCollection];
  unfold V_L V_R H_bot H_top;
  have h_unit_segments : IsUnitSegment (openSegment ℝ ![0, 0] ![0, 1]) ∧ IsUnitSegment (openSegment ℝ ![1, 0] ![1, 1]) ∧ IsUnitSegment (openSegment ℝ ![0, 0] ![1, 0]) ∧ IsUnitSegment (openSegment ℝ ![0, 1] ![1, 1]) := by
    unfold IsUnitSegment;
    norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
    exact ⟨ ⟨ _, _, by norm_num, rfl ⟩, ⟨ _, _, by norm_num, rfl ⟩, ⟨ _, _, by norm_num, rfl ⟩, ⟨ _, _, by norm_num, rfl ⟩ ⟩;
  refine' ⟨ h_unit_segments, _ ⟩;
  rintro s t ( rfl | rfl | rfl | rfl ) ( rfl | rfl | rfl | rfl ) <;> norm_num [ openSegment_eq_image ];
  all_goals rw [ Set.disjoint_left ] ; norm_num [ Set.mem_image ];
  all_goals intro h a x hx₁ hx₂ hx₃ y hy₁ hy₂ hy₃; rw [ ← List.ofFn_inj ] at *; norm_num at * ;
  all_goals linarith!;

/-
The sides of the unit square are disjoint from the open unit square.
-/
lemma S_sides_disjoint_Region_Square : ∀ s ∈ S_sides, Disjoint s Region_Square := by
  unfold S_sides Region_Square;
  simp +decide [ Set.disjoint_left, V_L, V_R, H_bot, H_top ];
  norm_num [ openSegment_eq_image ] ; aesop

/-
Any segment in S_cor2 is disjoint from any segment in S_sides.
-/
lemma S_cor2_disjoint_S_sides : ∀ s ∈ S_cor2, ∀ t ∈ S_sides, Disjoint s t := by
  -- By definition of $S_{\text{cor}2}$, we know that $s \in S_{\text{cor}2}$ implies $s \subseteq \text{Region}_{\text{Square}}$.
  intro s hs t ht
  have hs_region : s ⊆ Region_Square := by
    have := @S_cor2_in_region; aesop;
  exact Set.disjoint_left.mpr fun x hx hx' => by have := S_sides_disjoint_Region_Square t ht; have := this.le_bot ⟨ hx', hs_region hx ⟩ ; contradiction;

/-
The combined collection S_cor3 is a disjoint collection of unit segments.
-/
lemma S_cor3_is_disjoint_collection : IsDisjointCollection S_cor3 := by
  -- First, let's show that S_sides is a disjoint collection.
  have h_sides_disjoint : IsDisjointCollection S_sides := by
    exact S_sides_is_disjoint_collection;
  have h_combined_disjoint : IsDisjointCollection (S_cor2 ∪ S_sides) := by
    have h_combined_disjoint : ∀ s ∈ S_cor2, ∀ t ∈ S_sides, Disjoint s t := by
      exact fun s a t a_1 ↦ S_cor2_disjoint_S_sides s a t a_1
    constructor;
    · rintro s ( hs | hs ) <;> [ exact ( S_cor2_is_disjoint_collection.1 s hs ) ; exact ( h_sides_disjoint.1 s hs ) ];
    · rintro s t ( hs | hs ) ( ht | ht ) hst <;> simp_all +decide [ IsDisjointCollection ];
      · exact S_cor2_is_disjoint_collection.2 s t hs ht hst;
      · exact Disjoint.symm ( h_combined_disjoint t ht s hs );
  exact h_combined_disjoint

/-
The open unit square is a subset of the closed unit square.
-/
lemma Region_Square_subset_UnitSquare : Region_Square ⊆ UnitSquare := by
  -- By definition of Region_Square, any point p in Region_Square satisfies 0 < p 0 ∧ p 0 < 1 ∧ 0 < p 1 ∧ p 1 < 1.
  intro p hp
  obtain ⟨hx, hy⟩ := hp;
  -- Since $0 < p 0 < 1$ and $0 < p 1 < 1$, we have $0 \leq p 0 \leq 1$ and $0 \leq p 1 \leq 1$.
  have h_bounds : 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1 := by
    exact ⟨ le_of_lt hx, le_of_lt hy.1, le_of_lt hy.2.1, le_of_lt hy.2.2 ⟩;
  -- By definition of UnitSquare, we need to show that for all i, p i is between 0 and 1.
  simp [UnitSquare, h_bounds]

/-
The collection S_cor2 is contained in the closed unit square.
-/
lemma S_cor2_subset_UnitSquare : IsInRegion S_cor2 UnitSquare := by
  -- Since S_cor2 is in Region_Square and Region_Square is a subset of UnitSquare, S_cor2 must be in UnitSquare.
  have h_S_cor2_in_UnitSquare : IsInRegion S_cor2 Region_Square → IsInRegion S_cor2 UnitSquare := by
    exact fun h => fun s hs => h s hs |> fun hs' => hs'.trans Region_Square_subset_UnitSquare;
  exact h_S_cor2_in_UnitSquare <| by exact S_cor2_in_region;

/-
The sides of the unit square are contained in the closed unit square.
-/
lemma S_sides_in_UnitSquare : IsInRegion S_sides UnitSquare := by
  intro s hs; obtain rfl | rfl | rfl | rfl := hs <;> norm_num [ UnitSquare, H_bot, H_top, V_L, V_R ] ;
  · intro p hp; obtain ⟨ a, b, ha, hb, hab, rfl ⟩ := hp; norm_num [ ha, hb, hab ] ;
    constructor <;> linarith;
  · intro p hp; obtain ⟨ a, b, ha, hb, hab, rfl ⟩ := hp; norm_num at *; constructor <;> constructor <;> nlinarith;
  · norm_num [ Set.subset_def, openSegment_eq_image ];
    rintro x y hy₁ hy₂ rfl; norm_num [ hy₁.le, hy₂.le ] ;
  · intro p hp; obtain ⟨ a, b, ha, hb, hab, rfl ⟩ := hp; norm_num at *; constructor <;> constructor <;> nlinarith;

/-
The combined collection S_cor3 is contained in the closed unit square.
-/
lemma S_cor3_in_region : IsInRegion S_cor3 UnitSquare := by
  exact Set.union_subset S_cor2_subset_UnitSquare ( S_sides_in_UnitSquare )

/-
If an open segment in the non-negative half-plane touches the boundary, it lies entirely in the boundary.
-/
lemma segment_in_halfplane_boundary (A B : Point) (hA : 0 ≤ A 0) (hB : 0 ≤ B 0) (P : Point) (hP : P ∈ openSegment ℝ A B) (hP_bound : P 0 = 0) : A 0 = 0 ∧ B 0 = 0 := by
  rcases hP with ⟨ u, v, hu, hv, huv, rfl ⟩;
  constructor <;> nlinarith! [ show ( u • A + v • B ) 0 = u * A 0 + v * B 0 by exact rfl ]

/-
If an open segment in the half-plane x <= 1 touches the boundary x = 1, it lies entirely in the boundary.
-/
lemma segment_in_halfplane_boundary_x1 (A B : Point) (hA : A 0 ≤ 1) (hB : B 0 ≤ 1) (P : Point) (hP : P ∈ openSegment ℝ A B) (hP_bound : P 0 = 1) : A 0 = 1 ∧ B 0 = 1 := by
  rcases hP with ⟨ a, b, ha, hb, hab, rfl ⟩;
  exact ⟨ by norm_num at hP_bound; nlinarith, by norm_num at hP_bound; nlinarith ⟩

/-
If an open segment in the half-plane y >= 0 touches the boundary y = 0, it lies entirely in the boundary.
-/
lemma segment_in_halfplane_boundary_y0 (A B : Point) (hA : 0 ≤ A 1) (hB : 0 ≤ B 1) (P : Point) (hP : P ∈ openSegment ℝ A B) (hP_bound : P 1 = 0) : A 1 = 0 ∧ B 1 = 0 := by
  obtain ⟨ s, t, hs, ht, hst ⟩ := hP;
  have h_eq : s * A 1 + t * B 1 = 0 := by
    convert congr_arg ( fun x : Point => x 1 ) hst.2 using 1 ; aesop;
  constructor <;> nlinarith

/-
The unit square is a closed set.
-/
lemma UnitSquare_isClosed : IsClosed UnitSquare := by
  -- The unit square is the intersection of four closed half-spaces, which are defined by the inequalities 0 ≤ p 0 ≤ 1 and 0 ≤ p 1 ≤ 1.
  have h_unit_square_closed : IsClosed {p : Point | 0 ≤ p 0 ∧ p 0 ≤ 1} ∧ IsClosed {p : Point | 0 ≤ p 1 ∧ p 1 ≤ 1} := by
    exact ⟨ isClosed_Icc.preimage ( continuous_apply 0 ), isClosed_Icc.preimage ( continuous_apply 1 ) ⟩;
  convert h_unit_square_closed.1.inter h_unit_square_closed.2 using 1;
  exact Set.ext fun x => by unfold UnitSquare; aesop;

/-
If a unit segment in the unit square intersects the line x=0, it is contained in the line x=0.
-/
lemma unit_segment_subset_boundary_x0 (L : Set Point) (hL_unit : IsUnitSegment L) (hL_sub : L ⊆ UnitSquare) (h_inter : (L ∩ {p | p 0 = 0}).Nonempty) : L ⊆ {p | p 0 = 0} := by
  cases' hL_unit with a b hab L_eq;
  -- Since L is a unit segment, it is the open segment connecting a and b.
  obtain ⟨b, hb_dist, hb_L⟩ := b;
  have hb_zero : a 0 = 0 ∧ b 0 = 0 := by
    -- Since P is in the open segment between a and b, and P 0 = 0, we can apply the lemma segment_in_halfplane_boundary.
    have hP_bounds : a 0 ≥ 0 ∧ b 0 ≥ 0 := by
      have h_bounds : ∀ p ∈ openSegment ℝ a b, 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1 := by
        exact fun p hp => by have := hL_sub ( hb_L ▸ hp ) ; unfold UnitSquare at this; aesop;
      have h_bounds : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ (1 - t) * a 0 + t * b 0 ∧ (1 - t) * a 0 + t * b 0 ≤ 1 := by
        intro t ht; specialize h_bounds ( ( 1 - t ) • a + t • b ) ; simp_all +decide [ openSegment_eq_image ] ;
        exact ⟨ h_bounds t ht.1 ht.2 rfl |>.1, h_bounds t ht.1 ht.2 rfl |>.2.1 ⟩;
      have h_bounds : Filter.Tendsto (fun t : ℝ => (1 - t) * a 0 + t * b 0) (nhdsWithin 0 (Set.Ioi 0)) (nhds (a 0)) ∧ Filter.Tendsto (fun t : ℝ => (1 - t) * a 0 + t * b 0) (nhdsWithin 1 (Set.Iio 1)) (nhds (b 0)) := by
        exact ⟨ tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num ), tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num ) ⟩;
      exact ⟨ le_of_tendsto_of_tendsto tendsto_const_nhds h_bounds.1 ( Filter.eventually_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ by norm_num, by norm_num ⟩ ) fun t ht => ‹∀ t ∈ Ioo 0 1, 0 ≤ ( 1 - t ) * a 0 + t * b 0 ∧ ( 1 - t ) * a 0 + t * b 0 ≤ 1› t ht |>.1 ), le_of_tendsto_of_tendsto tendsto_const_nhds h_bounds.2 ( Filter.eventually_of_mem ( Ioo_mem_nhdsLT_of_mem ⟨ by norm_num, by norm_num ⟩ ) fun t ht => ‹∀ t ∈ Ioo 0 1, 0 ≤ ( 1 - t ) * a 0 + t * b 0 ∧ ( 1 - t ) * a 0 + t * b 0 ≤ 1› t ht |>.1 ) ⟩;
    obtain ⟨ P, hP_L, hP_zero ⟩ := h_inter;
    have := segment_in_halfplane_boundary a b hP_bounds.1 hP_bounds.2 P; aesop;
  intro p hp; rw [ hb_L, openSegment_eq_image ] at hp; obtain ⟨ t, ht, rfl ⟩ := hp; simp +decide [ *, mul_comm ] ;

/-
If a unit segment in the unit square intersects the line x=1, it is contained in the line x=1.
-/
lemma unit_segment_subset_boundary_x1 (L : Set Point) (hL_unit : IsUnitSegment L) (hL_sub : L ⊆ UnitSquare) (h_inter : (L ∩ {p | p 0 = 1}).Nonempty) : L ⊆ {p | p 0 = 1} := by
  -- Since L is a unit segment, it is an open segment between two points A and B.
  obtain ⟨A, B, hAB⟩ : ∃ A B : Point, L = openSegment ℝ A B ∧ dist A B = 1 := by
    obtain ⟨A, B, hL_def, hL_dist⟩ := hL_unit;
    use A, B;
  -- Since L is a unit segment, it is an open segment between two points A and B. If L intersects the line x=1, then either A or B must lie on this line.
  obtain ⟨P, hP⟩ : ∃ P ∈ L, P 0 = 1 := by
    exact h_inter;
  have hP_in_halfplane : 0 ≤ A 0 ∧ A 0 ≤ 1 ∧ 0 ≤ B 0 ∧ B 0 ≤ 1 := by
    have hP_in_halfplane : ∀ p ∈ L, 0 ≤ p 0 ∧ p 0 ≤ 1 := by
      exact fun p a => hL_sub a 0;
    simp_all +decide [ openSegment_eq_image ];
    -- By taking the limit as $x$ approaches $0$ and $1$, we can show that $A 0$ and $B 0$ must be in $[0, 1]$.
    have hA0 : 0 ≤ A 0 ∧ A 0 ≤ 1 := by
      have hA0 : Filter.Tendsto (fun x : ℝ => ((1 - x) • A + x • B) 0) (nhdsWithin 0 (Set.Ioi 0)) (nhds (A 0)) := by
        exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num )
      generalize_proofs at *; (
      exact ⟨ le_of_tendsto_of_tendsto tendsto_const_nhds hA0 <| Filter.eventually_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, zero_lt_one ⟩ ) fun x hx => hP_in_halfplane _ _ hx.1 hx.2 rfl |>.1, le_of_tendsto_of_tendsto hA0 tendsto_const_nhds <| Filter.eventually_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, zero_lt_one ⟩ ) fun x hx => hP_in_halfplane _ _ hx.1 hx.2 rfl |>.2 ⟩)
    have hB0 : 0 ≤ B 0 ∧ B 0 ≤ 1 := by
      have hB0 : Filter.Tendsto (fun x : ℝ => ((1 - x) • A + x • B) 0) (nhdsWithin 1 (Set.Iio 1)) (nhds (B 0)) := by
        exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num );
      exact ⟨ le_of_tendsto_of_tendsto tendsto_const_nhds hB0 <| Filter.eventually_of_mem ( Ioo_mem_nhdsLT zero_lt_one ) fun x hx => hP_in_halfplane _ _ hx.1 hx.2 rfl |>.1, le_of_tendsto_of_tendsto hB0 tendsto_const_nhds <| Filter.eventually_of_mem ( Ioo_mem_nhdsLT zero_lt_one ) fun x hx => hP_in_halfplane _ _ hx.1 hx.2 rfl |>.2 ⟩
    exact ⟨hA0.left, hA0.right, hB0.left, hB0.right⟩;
  have hP_in_halfplane : A 0 = 1 ∧ B 0 = 1 := by
    have := segment_in_halfplane_boundary_x1 A B hP_in_halfplane.2.1 hP_in_halfplane.2.2.2 P ( hAB.1.subset hP.1 ) hP.2; aesop;
  simp_all +decide [ openSegment_eq_image ]

/-
If a unit segment in the unit square intersects the line y=0, it is contained in the line y=0.
-/
lemma unit_segment_subset_boundary_y0 (L : Set Point) (hL_unit : IsUnitSegment L) (hL_sub : L ⊆ UnitSquare) (h_inter : (L ∩ {p | p 1 = 0}).Nonempty) : L ⊆ {p | p 1 = 0} := by
  -- By definition of $IsUnitSegment$, there exist points $A$ and $B$ such that $L = openSegment ℝ A B$ and $dist A B = 1$.
  obtain ⟨A, B, hL, hAB⟩ : ∃ A B : Point, L = openSegment ℝ A B ∧ dist A B = 1 := by
    rcases hL_unit with ⟨ A, B, hL ⟩ ; use A, B ; aesop;
  -- By definition of $IsUnitSegment$, there exist points $A$ and $B$ such that $L = openSegment ℝ A B$ and $dist A B = 1$. Since $L$ intersects the line $y=0$, we have $A_1 \geq 0$ and $B_1 \geq 0$.
  have h_nonneg : 0 ≤ A 1 ∧ 0 ≤ B 1 := by
    have h_nonneg : ∀ p ∈ openSegment ℝ A B, 0 ≤ p 1 := by
      intro p hp; specialize hL_sub ( hL ▸ hp ) ; unfold UnitSquare at hL_sub; aesop;
    have h_nonneg : ∀ t : ℝ, 0 < t ∧ t < 1 → 0 ≤ (1 - t) * A 1 + t * B 1 := by
      intro t ht; specialize h_nonneg ( ( 1 - t ) • A + t • B ) ; simp_all +decide [ openSegment_eq_image ] ;
      exact h_nonneg t ht.1 ht.2 rfl;
    have h_nonneg_A : Filter.Tendsto (fun t : ℝ => (1 - t) * A 1 + t * B 1) (nhdsWithin 0 (Set.Ioi 0)) (nhds (A 1)) := by
      exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ ( by norm_num ) );
    have h_nonneg_B : Filter.Tendsto (fun t : ℝ => (1 - t) * A 1 + t * B 1) (nhdsWithin 1 (Set.Iio 1)) (nhds (B 1)) := by
      exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num );
    exact ⟨ le_of_tendsto_of_tendsto tendsto_const_nhds h_nonneg_A <| Filter.eventually_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ by norm_num, by norm_num ⟩ ) fun t ht => h_nonneg t ht, le_of_tendsto_of_tendsto tendsto_const_nhds h_nonneg_B <| Filter.eventually_of_mem ( Ioo_mem_nhdsLT_of_mem ⟨ by norm_num, by norm_num ⟩ ) fun t ht => h_nonneg t ht ⟩;
  -- By definition of $IsUnitSegment$, there exist points $A$ and $B$ such that $L = openSegment ℝ A B$ and $dist A B = 1$. Since $L$ intersects the line $y=0$, we have $A_1 \geq 0$ and $B_1 \geq 0$. Therefore, $L$ is contained in the line $y=0$.
  obtain ⟨P, hP⟩ : ∃ P ∈ L, P 1 = 0 := by
    exact h_inter.imp fun x hx => ⟨ hx.1, hx.2 ⟩;
  have hL_subset_y0 : A 1 = 0 ∧ B 1 = 0 := by
    have := segment_in_halfplane_boundary_y0 A B h_nonneg.1 h_nonneg.2 P (by
    grind) hP.2; aesop;
  intro p hp; rw [ hL ] at hp; rw [ openSegment_eq_image ] at hp; aesop;

/-
If a unit segment in the unit square is contained in the line x=0, it must be the left vertical side V_L.
-/
lemma unit_segment_on_boundary_x0_eq_V_L (L : Set Point) (hL_unit : IsUnitSegment L) (hL_sub : L ⊆ UnitSquare) (h_subset : L ⊆ {p | p 0 = 0}) : L = V_L := by
  -- Since L is a unit segment contained in the line x=0, its endpoints must be (0,0) and (0,1).
  have h_endpoints : ∃ A B : Point, L = openSegment ℝ A B ∧ A 0 = 0 ∧ B 0 = 0 ∧ A 1 = 0 ∧ B 1 = 1 := by
    obtain ⟨A, B, hL, hAB⟩ : ∃ A B : Point, L = openSegment ℝ A B ∧ dist A B = 1 ∧ (∀ p ∈ L, p 0 = 0) := by
      rcases hL_unit with ⟨A, B, hL, hAB⟩; use A, B; aesop;
    have h_endpoints : A 0 = 0 ∧ B 0 = 0 := by
      simp_all +decide [ openSegment_eq_image ];
      have := h_subset ( show 1 / 3 ∈ Set.Ioo 0 1 by norm_num ) ; have := h_subset ( show 2 / 3 ∈ Set.Ioo 0 1 by norm_num ) ; norm_num at * ; constructor <;> linarith;
    have h_endpoints : A 1 = 0 ∧ B 1 = 1 ∨ A 1 = 1 ∧ B 1 = 0 := by
      have h_endpoints : A 1 ∈ Set.Icc 0 1 ∧ B 1 ∈ Set.Icc 0 1 := by
        have h_endpoints : ∀ p ∈ L, p 1 ∈ Set.Icc 0 1 := by
          exact fun p hp => ⟨ by have := hL_sub hp; unfold UnitSquare at this; aesop, by have := hL_sub hp; unfold UnitSquare at this; aesop ⟩;
        simp_all +decide [ openSegment_eq_image ];
        have h_endpoints : Filter.Tendsto (fun x : ℝ => (1 - x) • A + x • B) (nhdsWithin 0 (Set.Ioi 0)) (nhds A) ∧ Filter.Tendsto (fun x : ℝ => (1 - x) • A + x • B) (nhdsWithin 1 (Set.Iio 1)) (nhds B) := by
          field_simp;
          exact ⟨ tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num ), tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num ) ⟩;
        have h_endpoints : Filter.Tendsto (fun x : ℝ => ((1 - x) • A + x • B) 1) (nhdsWithin 0 (Set.Ioi 0)) (nhds (A 1)) ∧ Filter.Tendsto (fun x : ℝ => ((1 - x) • A + x • B) 1) (nhdsWithin 1 (Set.Iio 1)) (nhds (B 1)) := by
          exact ⟨ tendsto_pi_nhds.mp h_endpoints.1 1, tendsto_pi_nhds.mp h_endpoints.2 1 ⟩;
        exact ⟨ ⟨ le_of_tendsto_of_tendsto tendsto_const_nhds h_endpoints.1 <| Filter.eventually_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ by norm_num, by norm_num ⟩ ) fun x hx => ( ‹∀ p : Point, ∀ x : ℝ, 0 < x → x < 1 → ( 1 - x ) • A + x • B = p → 0 ≤ p 1 ∧ p 1 ≤ 1› _ _ hx.1 hx.2 rfl ) |>.1, le_of_tendsto_of_tendsto h_endpoints.1 tendsto_const_nhds <| Filter.eventually_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ by norm_num, by norm_num ⟩ ) fun x hx => ( ‹∀ p : Point, ∀ x : ℝ, 0 < x → x < 1 → ( 1 - x ) • A + x • B = p → 0 ≤ p 1 ∧ p 1 ≤ 1› _ _ hx.1 hx.2 rfl ) |>.2 ⟩, ⟨ le_of_tendsto_of_tendsto tendsto_const_nhds h_endpoints.2 <| Filter.eventually_of_mem ( Ioo_mem_nhdsLT_of_mem ⟨ by norm_num, by norm_num ⟩ ) fun x hx => ( ‹∀ p : Point, ∀ x : ℝ, 0 < x → x < 1 → ( 1 - x ) • A + x • B = p → 0 ≤ p 1 ∧ p 1 ≤ 1› _ _ hx.1 hx.2 rfl ) |>.1, le_of_tendsto_of_tendsto h_endpoints.2 tendsto_const_nhds <| Filter.eventually_of_mem ( Ioo_mem_nhdsLT_of_mem ⟨ by norm_num, by norm_num ⟩ ) fun x hx => ( ‹∀ p : Point, ∀ x : ℝ, 0 < x → x < 1 → ( 1 - x ) • A + x • B = p → 0 ≤ p 1 ∧ p 1 ≤ 1› _ _ hx.1 hx.2 rfl ) |>.2 ⟩ ⟩;
      have h_dist : |A 1 - B 1| = 1 := by
        simp_all +decide [ dist_eq_norm, EuclideanSpace.norm_eq ];
        cases hAB.1 <;> cases abs_cases ( A 1 - B 1 ) <;> linarith;
      cases abs_cases ( A 1 - B 1 ) <;> [ right; left ] <;> constructor <;> linarith [ h_endpoints.1.1, h_endpoints.1.2, h_endpoints.2.1, h_endpoints.2.2 ];
    cases' h_endpoints with h h <;> [ exact ⟨ A, B, hL, by tauto ⟩ ; exact ⟨ B, A, by rw [ hL, openSegment_symm ], by tauto ⟩ ];
  -- Since A and B are (0,0) and (0,1), the open segment between them is exactly the vertical line segment from (0,0) to (0,1), which is V_L.
  obtain ⟨A, B, hL, hA, hB, hA1, hB1⟩ := h_endpoints
  have h_open_segment : openSegment ℝ A B = openSegment ℝ ![0, 0] ![0, 1] := by
    congr <;> ext i <;> fin_cases i <;> aesop;
  convert hL.trans h_open_segment using 1

/-
If a unit segment in the unit square is contained in the line x=1, it must be the right vertical side V_R.
-/
lemma unit_segment_on_boundary_x1_eq_V_R (L : Set Point) (hL_unit : IsUnitSegment L) (hL_sub : L ⊆ UnitSquare) (h_subset : L ⊆ {p | p 0 = 1}) : L = V_R := by
  obtain ⟨ p, q, hp, hq, hpq ⟩ := hL_unit;
  -- Since p 0 = 1 and q 0 = 1, we can express p and q as (1, y1) and (1, y2) respectively.
  obtain ⟨y1, y2, hy1, hy2⟩ : ∃ y1 y2 : ℝ, p = ![1, y1] ∧ q = ![1, y2] := by
    have h_p : p 0 = 1 := by
      have h_p0 : p 0 = 1 := by
        have h_seq : Filter.Tendsto (fun t : ℝ => (1 - t) • p + t • q) (nhdsWithin 0 (Set.Ioi 0)) (nhds p) := by
          exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ ( by norm_num ) )
        exact tendsto_nhds_unique ( tendsto_pi_nhds.mp h_seq 0 ) ( tendsto_const_nhds.congr' <| Filter.eventuallyEq_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, zero_lt_one ⟩ ) fun t ht => by have := h_subset <| show ( 1 - t ) • p + t • q ∈ openSegment ℝ p q from ⟨ 1 - t, t, by linarith [ ht.1, ht.2 ], by linarith [ ht.1, ht.2 ], by simp +decide ⟩ ; aesop );
      exact h_p0
    have h_q : q 0 = 1 := by
      convert h_subset ( show ( 1 / 2 : ℝ ) • p + ( 1 / 2 : ℝ ) • q ∈ openSegment ℝ p q from ?_ ) using 1 ; norm_num [ h_p ];
      · constructor <;> intro <;> linarith;
      · exact ⟨ 1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num ⟩;
    exact ⟨ p 1, q 1, by ext i; fin_cases i <;> aesop, by ext i; fin_cases i <;> aesop ⟩;
  -- Since the distance between p and q is 1 and they are both on the line x=1, we have |y2 - y1| = 1. Without loss of generality, assume y2 > y1, so y2 = y1 + 1.
  have h_y_diff : y2 = y1 + 1 ∨ y1 = y2 + 1 := by
    norm_num [ hy1, hy2, dist_eq_norm, EuclideanSpace.norm_eq ] at hp;
    cases hp <;> first | left; linarith | right; linarith;
  -- Since the open segment is contained in the unit square, the y-coordinates of p and q must be between 0 and 1. Therefore, y1 must be 0 and y2 must be 1, or vice versa.
  have h_y_bounds : y1 ∈ Set.Icc 0 1 ∧ y2 ∈ Set.Icc 0 1 := by
    have h_y_bounds : Filter.Tendsto (fun t : ℝ => (1 - t) • p + t • q) (nhdsWithin 0 (Set.Ioi 0)) (nhds p) ∧ Filter.Tendsto (fun t : ℝ => (1 - t) • p + t • q) (nhdsWithin 1 (Set.Iio 1)) (nhds q) := by
      exact ⟨ tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num ), tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num ) ⟩;
    have h_y_bounds : p ∈ closure UnitSquare ∧ q ∈ closure UnitSquare := by
      exact ⟨ mem_closure_of_tendsto ( by tauto ) ( Filter.eventually_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ by norm_num, by norm_num ⟩ ) fun t ht => hL_sub <| openSegment_eq_image ℝ p q ▸ Set.mem_image_of_mem _ ht ), mem_closure_of_tendsto ( by tauto ) ( Filter.eventually_of_mem ( Ioo_mem_nhdsLT_of_mem ⟨ by norm_num, by norm_num ⟩ ) fun t ht => hL_sub <| openSegment_eq_image ℝ p q ▸ Set.mem_image_of_mem _ ht ) ⟩;
    have h_y_bounds : p ∈ UnitSquare ∧ q ∈ UnitSquare := by
      exact ⟨ by simpa using IsClosed.closure_subset (show IsClosed UnitSquare from by exact UnitSquare_isClosed ) h_y_bounds.1, by simpa using IsClosed.closure_subset ( show IsClosed UnitSquare from by exact UnitSquare_isClosed ) h_y_bounds.2 ⟩;
    unfold UnitSquare at h_y_bounds; aesop;
  cases h_y_diff <;> simp_all +decide [ Set.Subset.antisymm_iff ];
  · norm_num [ show y1 = 0 by linarith ] at *;
    unfold V_R; aesop;
  · norm_num [ show y2 = 0 by linarith, openSegment_eq_image ];
    norm_num [ Set.subset_def, V_R ];
    norm_num [ openSegment_eq_image ];
    exact ⟨ fun x hx₁ hx₂ => ⟨ 1 - x, ⟨ by linarith, by linarith ⟩, by ext i; fin_cases i <;> norm_num ⟩, fun x y hy₁ hy₂ hx => ⟨ 1 - y, ⟨ by linarith, by linarith ⟩, by ext i; fin_cases i <;> norm_num [ hx.symm ] ⟩ ⟩

/-
If a unit segment in the unit square is contained in the line y=0, it must be the bottom horizontal side H_bot.
-/
lemma unit_segment_on_boundary_y0_eq_H_bot (L : Set Point) (hL_unit : IsUnitSegment L) (hL_sub : L ⊆ UnitSquare) (h_subset : L ⊆ {p | p 1 = 0}) : L = H_bot := by
  have hL_eq_H_bot : L = {p : Point | p 0 ∈ Set.Ioo 0 1 ∧ p 1 = 0} := by
    have hL_unit_def : ∃ A B : Point, dist A B = 1 ∧ openSegment ℝ A B = L := by
      rcases hL_unit with ⟨ A, B, hAB, rfl ⟩ ; exact ⟨ A, B, hAB, rfl ⟩
    obtain ⟨ A, B, hAB, rfl ⟩ := hL_unit_def;
    -- Since $A$ and $B$ are in the unit square and their $y$-coordinates are $0$, they must be on the bottom edge.
    have hA_B_on_bottom : A 1 = 0 ∧ B 1 = 0 := by
      have hA_B_on_bottom : ∀ t ∈ Set.Ioo (0 : ℝ) 1, (t • A + (1 - t) • B) 1 = 0 := by
        exact fun t ht => h_subset <| ⟨ t, 1 - t, ht.1, by linarith [ ht.2 ], by simp +decide ⟩;
      have := hA_B_on_bottom ( 1 / 3 ) ⟨ by norm_num, by norm_num ⟩ ; ( have := hA_B_on_bottom ( 2 / 3 ) ⟨ by norm_num, by norm_num ⟩ ; ( norm_num at * ; constructor <;> linarith!; ) );
    -- Since $A$ and $B$ are on the bottom edge, their $x$-coordinates must be $0$ and $1$ respectively.
    have hA_B_x : A 0 = 0 ∧ B 0 = 1 ∨ A 0 = 1 ∧ B 0 = 0 := by
      have hA_B_x : |A 0 - B 0| = 1 := by
        simp_all +decide [ dist_eq_norm, EuclideanSpace.norm_eq ];
        cases hAB <;> cases abs_cases ( A 0 - B 0 ) <;> linarith;
      have hA_B_x_bounds : 0 ≤ A 0 ∧ A 0 ≤ 1 ∧ 0 ≤ B 0 ∧ B 0 ≤ 1 := by
        have hA_B_x_bounds : ∀ p ∈ openSegment ℝ A B, 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1 := by
          exact fun p hp => by have := hL_sub hp; unfold UnitSquare at this; aesop;
        have hA_B_x_bounds : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ (1 - t) * A 0 + t * B 0 ∧ (1 - t) * A 0 + t * B 0 ≤ 1 := by
          intro t ht; specialize hA_B_x_bounds ( ( 1 - t ) • A + t • B ) ; simp_all +decide [ openSegment_eq_image ] ;
          exact hA_B_x_bounds t ht.1 ht.2 rfl;
        have hA_B_x_bounds : Filter.Tendsto (fun t : ℝ => (1 - t) * A 0 + t * B 0) (nhdsWithin 0 (Set.Ioi 0)) (nhds (A 0)) ∧ Filter.Tendsto (fun t : ℝ => (1 - t) * A 0 + t * B 0) (nhdsWithin 1 (Set.Iio 1)) (nhds (B 0)) := by
          exact ⟨ tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num ), tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num ) ⟩;
        exact ⟨ le_of_tendsto_of_tendsto tendsto_const_nhds hA_B_x_bounds.1 ( Filter.eventually_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ by norm_num, by norm_num ⟩ ) fun t ht => ‹∀ t ∈ Ioo 0 1, 0 ≤ ( 1 - t ) * A 0 + t * B 0 ∧ ( 1 - t ) * A 0 + t * B 0 ≤ 1› t ht |>.1 ), le_of_tendsto_of_tendsto hA_B_x_bounds.1 tendsto_const_nhds ( Filter.eventually_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ by norm_num, by norm_num ⟩ ) fun t ht => ‹∀ t ∈ Ioo 0 1, 0 ≤ ( 1 - t ) * A 0 + t * B 0 ∧ ( 1 - t ) * A 0 + t * B 0 ≤ 1› t ht |>.2 ), le_of_tendsto_of_tendsto tendsto_const_nhds hA_B_x_bounds.2 ( Filter.eventually_of_mem ( Ioo_mem_nhdsLT_of_mem ⟨ by norm_num, by norm_num ⟩ ) fun t ht => ‹∀ t ∈ Ioo 0 1, 0 ≤ ( 1 - t ) * A 0 + t * B 0 ∧ ( 1 - t ) * A 0 + t * B 0 ≤ 1› t ht |>.1 ), le_of_tendsto_of_tendsto hA_B_x_bounds.2 tendsto_const_nhds ( Filter.eventually_of_mem ( Ioo_mem_nhdsLT_of_mem ⟨ by norm_num, by norm_num ⟩ ) fun t ht => ‹∀ t ∈ Ioo 0 1, 0 ≤ ( 1 - t ) * A 0 + t * B 0 ∧ ( 1 - t ) * A 0 + t * B 0 ≤ 1› t ht |>.2 ) ⟩;
      cases abs_cases ( A 0 - B 0 ) <;> first | left; constructor <;> linarith | right; constructor <;> linarith;
    cases hA_B_x <;> simp_all +decide [ dist_eq_norm, EuclideanSpace.norm_eq ];
    · ext p; simp [openSegment];
      constructor <;> intro h;
      · rcases h with ⟨ a, ha, b, hb, hab, rfl ⟩ ; simp_all +decide
        linarith;
      · use 1 - p 0, by linarith, p 0, by linarith;
        exact ⟨ by ring, by ext i; fin_cases i <;> simp +decide [ * ] ⟩;
    · ext p; simp [openSegment];
      constructor <;> intro h;
      · rcases h with ⟨ a, ha, b, hb, hab, rfl ⟩ ; simp_all +decide
        linarith;
      · exact ⟨ p 0, h.1.1, 1 - p 0, by linarith, by linarith, by ext i; fin_cases i <;> simp +decide [ * ] ⟩;
  convert hL_eq_H_bot using 1;
  ext; simp [H_bot];
  norm_num [ openSegment_eq_image ];
  constructor <;> intro h;
  · rcases h with ⟨ x, ⟨ hx₁, hx₂ ⟩, rfl ⟩ ; norm_num [ hx₁, hx₂ ];
  · exact ⟨ ‹Point› 0, h.1, by ext i; fin_cases i <;> simp ; linarith ⟩

/-
The collection S_cor3 is countable.
-/
lemma S_cor3_countable : Set.Countable S_cor3 := by
  apply Set.Countable.union;
  · apply Set.Countable.union;
    · apply Set.Countable.union;
      · exact S_collection_countable;
      · exact S_shifted_countable;
    · exact Set.countable_singleton _;
  · exact Set.countable_singleton V_L |> Set.Countable.union <| Set.countable_singleton V_R |> Set.Countable.union <| Set.countable_singleton H_bot |> Set.Countable.union <| Set.countable_singleton H_top

/-
If a unit segment in the unit square is disjoint from the four sides, it is contained in the open unit square.
-/
lemma L_disjoint_S_sides_implies_L_subset_Region_Square (L : Set Point) (hL_unit : IsUnitSegment L) (hL_sub : L ⊆ UnitSquare) (h_disj : ∀ s ∈ S_sides, Disjoint L s) : L ⊆ Region_Square := by
  -- By definition of $L$, if $p \in L$, then $0 \leq p_0 \leq 1$ and $0 \leq p_1 \leq 1$.
  have h_bounds : ∀ p ∈ L, 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1 := by
    exact fun p hp => by have := hL_sub hp; unfold UnitSquare at this; aesop;
  -- By definition of $L$, if $p \in L$, then $p_0 \neq 0$ and $p_0 \neq 1$, and $p_1 \neq 0$ and $p_1 \neq 1$.
  have h_bounds_strict : ∀ p ∈ L, p 0 ≠ 0 ∧ p 0 ≠ 1 ∧ p 1 ≠ 0 ∧ p 1 ≠ 1 := by
    intro p hp
    have h_bounds : 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1 := h_bounds p hp
    have h_bounds_strict : p 0 ≠ 0 ∧ p 0 ≠ 1 ∧ p 1 ≠ 0 ∧ p 1 ≠ 1 := by
      have h0 : p 0 ≠ 0 := by
        intro h_zero
        have h_subset : L ⊆ {p | p 0 = 0} := by
          apply unit_segment_subset_boundary_x0 L hL_unit hL_sub ⟨p, hp, h_zero⟩;
        have h_eq_V_L : L = V_L := by
          exact unit_segment_on_boundary_x0_eq_V_L L hL_unit hL_sub h_subset;
        exact Set.not_disjoint_iff_nonempty_inter.mpr ⟨ p, hp, h_eq_V_L.symm ▸ hp ⟩ ( h_disj _ ( by exact Set.mem_insert _ _ ) )
      have h1 : p 0 ≠ 1 := by
        contrapose! h_disj;
        -- Since $p \in L$ and $p 0 = 1$, $L$ must be the right vertical side $V_R$.
        have hL_VR : L ⊆ {p | p 0 = 1} := by
          apply unit_segment_subset_boundary_x1 L hL_unit hL_sub ⟨ p, hp, h_disj ⟩;
        have hL_VR_eq : L = V_R := by
          exact unit_segment_on_boundary_x1_eq_V_R L hL_unit hL_sub hL_VR;
        exact ⟨ V_R, by unfold S_sides; aesop ⟩
      have h2 : p 1 ≠ 0 := by
        contrapose! h_disj;
        have h_subset_y0 : L ⊆ {p | p 1 = 0} := by
          apply unit_segment_subset_boundary_y0 L hL_unit hL_sub ⟨ p, hp, h_disj ⟩;
        have h_eq_H_bot : L = H_bot := by
          exact unit_segment_on_boundary_y0_eq_H_bot L hL_unit hL_sub h_subset_y0;
        exact ⟨ H_bot, by unfold S_sides; simp +decide [ H_bot ], by unfold Disjoint; aesop ⟩
      have h3 : p 1 ≠ 1 := by
        contrapose! h_disj;
        use H_top;
        simp [S_sides, H_top];
        -- Since $p \in L$ and $p \in \text{openSegment} \, \mathbb{R} \, ![0, 1] \, ![1, 1]$, we have $L \cap \text{openSegment} \, \mathbb{R} \, ![0, 1] \, ![1, 1] \neq \emptyset$.
        have h_inter : p ∈ L ∧ p ∈ openSegment ℝ ![0, 1] ![1, 1] := by
          simp_all +decide [ openSegment_eq_image ];
          exact ⟨ p 0, ⟨ lt_of_le_of_ne ( h_bounds p hp |>.1 ) ( Ne.symm h0 ), lt_of_le_of_ne ( h_bounds p hp |>.2.1 ) h1 ⟩, by ext i; fin_cases i <;> aesop ⟩;
        exact Set.not_disjoint_iff_nonempty_inter.mpr ⟨ p, h_inter ⟩
      exact ⟨h0, h1, h2, h3⟩
    exact h_bounds_strict;
  exact fun p hp => ⟨ lt_of_le_of_ne ( h_bounds p hp |>.1 ) ( Ne.symm ( h_bounds_strict p hp |>.1 ) ), lt_of_le_of_ne ( h_bounds p hp |>.2.1 ) ( h_bounds_strict p hp |>.2.1 ), lt_of_le_of_ne ( h_bounds p hp |>.2.2.1 ) ( Ne.symm ( h_bounds_strict p hp |>.2.2.1 ) ), lt_of_le_of_ne ( h_bounds p hp |>.2.2.2 ) ( h_bounds_strict p hp |>.2.2.2 ) ⟩

/-
The collection S_cor3 is blocking in the unit square.
-/
lemma S_cor3_is_blocking : IsBlocking S_cor3 UnitSquare := by
  intro L hL_unit hL_sub
  by_cases h_disj : ∀ s ∈ S_sides, Disjoint L s;
  · -- By L_disjoint_S_sides_implies_L_subset_Region_Square, L is in Region_Square.
    have hL_region : L ⊆ Region_Square := by
      exact L_disjoint_S_sides_implies_L_subset_Region_Square L hL_unit hL_sub h_disj;
    -- Since S_cor2 is blocking in Region_Square (S_cor2_is_blocking), L intersects some s in S_cor2.
    obtain ⟨s, hs⟩ : ∃ s ∈ S_cor2, ¬Disjoint s L := by
      have := S_cor2_is_blocking L hL_unit hL_region;
      exact this;
    exact ⟨ s, Or.inl hs.1, hs.2 ⟩;
  · simp_all +decide [ Set.disjoint_left ];
    obtain ⟨ s, hs₁, x, hx₁, hx₂ ⟩ := h_disj; exact ⟨ s, by exact Set.mem_union_right _ hs₁, x, hx₂, hx₁ ⟩ ;

/-
The collection S_cor2 is countable.
-/
lemma S_cor2_countable : Set.Countable S_cor2 := by
  · apply Set.Countable.union;
    · apply Set.Countable.union;
      · exact S_collection_countable;
      · exact S_shifted_countable;
    · exact Set.countable_singleton _;

lemma openSegment_eq (x y z : Point) : openSegment ℝ x y = openSegment ℝ x z → y = z := by
  intro h
  have hseg :
      segment ℝ x y = segment ℝ x z := by
    simpa [closure_openSegment] using congrArg closure h
  have hy' : y - x ∈ segment ℝ (0 : Point) (z - x) := by
    have : y ∈ segment ℝ x z := by
      simpa [hseg] using (right_mem_segment (𝕜 := ℝ) x y)
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      ( (mem_segment_translate (𝕜 := ℝ) (E := Point) x).1 (by
          -- x + (y - x) = y, x + 0 = x, x + (z - x) = z
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this ) )
  have hz' : z - x ∈ segment ℝ (0 : Point) (y - x) := by
    have : z ∈ segment ℝ x y := by
      simpa [hseg.symm] using (right_mem_segment (𝕜 := ℝ) x z)
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      ( (mem_segment_translate (𝕜 := ℝ) (E := Point) x).1 (by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this ) )
  have hy'' :
      y - x ∈ (fun (θ : ℝ) => (0 : Point) + θ • ((z - x) - (0 : Point))) '' Icc (0 : ℝ) 1 := by
    simpa [segment_eq_image'] using hy'
  rcases hy'' with ⟨t, ht, hyt⟩
  have hyt' : y - x = t • (z - x) := by simp_all only [mem_Icc, sub_zero, zero_add]
  have hz'' :
      z - x ∈ (fun (θ : ℝ) => (0 : Point) + θ • ((y - x) - (0 : Point))) '' Icc (0 : ℝ) 1 := by
    simpa [segment_eq_image'] using hz'
  rcases hz'' with ⟨u, hu, hzu⟩
  have hzu' : z - x = u • (y - x) := by simp_all only [mem_Icc, sub_zero, zero_add]
  have hmul : (y - x) = (t * u) • (y - x) := by
    calc
      y - x = t • (z - x) := hyt'
      _ = t • (u • (y - x)) := by simp [hzu']
      _ = (t * u) • (y - x) := by simp [mul_smul]
  by_cases h0 : y = x
  · have : z = x := by
      have hx : openSegment ℝ x z = {x} := by
        subst h0
        simp_all only [mem_Icc, openSegment_same, segment_same, sub_self, smul_zero, mem_singleton_iff, add_zero]
      have : z ∈ ({x} : Set Point) := by
        subst h0
        simp_all only [mem_Icc, openSegment_same, segment_same, sub_self, smul_zero, mem_singleton_iff, add_zero]
        obtain ⟨left, right⟩ := ht
        obtain ⟨left_1, right_1⟩ := hu
        exact right_mem_segment ℝ y z
      simpa using this
    simp [h0, this]
  · have hne : y - x ≠ (0 : Point) := by
      intro hyx
      apply h0
      simpa using sub_eq_zero.mp hyx
    have : (1 - t * u) = 0 := by
      have : (1 - t * u) • (y - x) = 0 := by
        have : (y - x) - (t * u) • (y - x) = 0 := by
          exact sub_eq_zero.2 hmul
        simpa [sub_smul, one_smul] using this
      rcases smul_eq_zero.mp this with hscalar | hvec
      · exact hscalar
      · cases hne hvec
    have htu : t * u = 1 := by linarith
    have ht1 : t = 1 := by
      have ht_le : t ≤ 1 := ht.2
      have hu_le : u ≤ 1 := hu.2
      by_contra htne
      have htlt : t < 1 := lt_of_le_of_ne ht_le htne
      have : t * u < 1 := by
        have ht0 : 0 ≤ t := ht.1
        have hu0 : 0 ≤ u := hu.1
        exact mul_lt_one_of_nonneg_of_lt_one_left ht0 htlt hu_le
      exact lt_irrefl (1 : ℝ) (by simp [htu] at this)
    have : y - x = z - x := by simpa [ht1] using hyt'
    have h' := congrArg (fun w => w + x) this
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'

theorem S_collection_infinite : Set.Infinite S_collection := by
  unfold S_collection
  rw [Set.infinite_union]
  left
  rw [Set.infinite_union]
  left
  unfold S_seq
  have hinj :
      Function.Injective (fun n : ℕ => openSegment ℝ O_point (A_seq (n + 1))) := by
    intro n m hseg
    have : A_seq (n + 1) = A_seq (m + 1) := by
      simp_all only
      apply openSegment_eq
      simp_all only
      exact hseg
    have : n + 1 = m + 1 := by
      by_contra hnm1
      exact (A_seq_distinct (n + 1) (m + 1) hnm1) this
    simp_all only [Nat.add_right_cancel_iff]
  have : (Set.range (fun n : ℕ => openSegment ℝ O_point (A_seq (n + 1)))).Infinite :=
    Set.infinite_range_of_injective hinj
  refine this.mono ?_
  intro s hs
  rcases hs with ⟨n, rfl⟩
  exact ⟨n, rfl⟩

theorem S_cor2_infinite : Set.Infinite S_cor2 := by
  unfold S_cor2
  rw [Set.infinite_union]
  left
  rw [Set.infinite_union]
  left
  exact S_collection_infinite

theorem S_cor3_infinite : Set.Infinite S_cor3 := by
  unfold S_cor3
  simp [Set.infinite_union]
  left
  exact S_cor2_infinite

/-
There exists a countably infinite maximal disjoint collection of unit segments in Region_R.
-/
theorem Theorem_1 : ∃ S, IsMaximalDisjointCollection S Region_R ∧ Set.Countable S ∧ Set.Infinite S := by
  use S_collection;
  apply And.intro;
  · apply (maximal_iff_blocking S_collection Region_R _ _).mpr;
    · exact S_collection_is_blocking;
    · exact ⟨ S_collection_is_unit_segment, S_collection_pairwise_disjoint ⟩;
    · exact S_collection_in_region;
  apply And.intro
  · exact S_collection_countable
  · exact S_collection_infinite

/-
There exists a countably infinite maximal collection in the open unit square (0,1) x (0,1).
-/
theorem Corollary_2 : ∃ S, IsMaximalDisjointCollection S Region_Square ∧ Set.Countable S ∧ Set.Infinite S := by
  use S_cor2;
  apply And.intro;
  · apply (maximal_iff_blocking S_cor2 Region_Square _ _).mpr;
    · exact S_cor2_is_blocking;
    · exact S_cor2_is_disjoint_collection
    · exact S_cor2_in_region;
  apply And.intro
  · exact S_cor2_countable
  · exact S_cor2_infinite

/-
There exists a countably infinite maximal disjoint collection in the closed unit square.
-/
theorem Corollary_3 : ∃ S, IsMaximalDisjointCollection S UnitSquare ∧ Set.Countable S ∧ Set.Infinite S := by
  use S_cor3;
  apply And.intro;
  · apply (maximal_iff_blocking S_cor3 UnitSquare _ _).mpr;
    · exact S_cor3_is_blocking;
    · exact S_cor3_is_disjoint_collection
    · exact S_cor3_in_region;
  apply And.intro
  · exact S_cor3_countable
  · exact S_cor3_infinite

#print axioms Corollary_3
-- 'Corollary_3' depends on axioms: [propext, Classical.choice, Quot.sound]
