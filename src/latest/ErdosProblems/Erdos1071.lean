/- leanprover/lean4:v4.30.0  mathlib v4.30.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1071.
https://www.erdosproblems.com/forum/thread/1071

Informal authors:
- Everett Howe
- Boris Alexeev

Formal authors:
- Aristotle
- ChatGPT
- Boris Alexeev

URLs:
- https://www.erdosproblems.com/forum/thread/1071#post-4258
- https://bsky.app/profile/ewhowe.com/post/3mbktyzvyak2e
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1071.md
-/
/-
We have proved Corollary 3, establishing the existence of a countable
maximal disjoint collection of unit segments in the closed unit square
[0,1] x [0,1]. This was achieved by defining the collection `S_cor3`
as the union of `S_cor2` (from Corollary 2) and the four sides of the
square, and proving that this collection is disjoint, contained in the
square, and blocking (maximal).
-/

import Mathlib

namespace Erdos1071

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.longLine false
set_option linter.style.cases false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 50000000
-- Several generated unit-segment blocking arguments time out at the default heartbeat limit.

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
      push Not at h_contra;
      -- Since $L$ is a unit segment in $R$ and is disjoint from all segments in $S$, the collection $S \cup \{L\}$ is a disjoint collection in $R$.
      have h_add_L : IsDisjointCollection (insert L S) := by
        refine ⟨ ?_, ?_ ⟩;
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
      refine ⟨ hS, hR, fun S' hS' hR' hSS' => Set.Subset.antisymm hSS' ?_ ⟩;
      intro L hL;
      contrapose! h;
      cases hS'
      rename_i left right
      simp_all only [ne_eq]
      apply Exists.intro
      focus
        apply And.intro
      on_goal 2 => apply And.intro
      on_goal 3 => intro s _
      on_goal 3 => apply right
      on_goal 3 => apply hSS'
      on_goal 3 => simp_all only
      on_goal 3 => exact hL
      on_goal 3 => apply Aesop.BuiltinRules.not_intro
      on_goal 3 => intro a
      on_goal 3 => subst a
      on_goal 3 => simp_all only
      on_goal 2 => apply hR'
      on_goal 2 => simp_all only
      simp_all only

open Set

def V_L : Set Point := openSegment ℝ !₂[0, 0] !₂[0, 1]
def V_R : Set Point := openSegment ℝ !₂[1, 0] !₂[1, 1]
def H_mid : Set Point := openSegment ℝ !₂[0, 0.5] !₂[1, 0.5]

def H_bot : Set Point := openSegment ℝ !₂[0, 0] !₂[1, 0]
def H_top : Set Point := openSegment ℝ !₂[0, 1] !₂[1, 1]

/-
Define the points O(0,0), O'(1,1/2), and A_0(1,0).
-/
def O_point : Point := !₂[0, 0]

noncomputable def O_prime : Point := !₂[1, 1/2]

def A_0 : Point := !₂[1, 0]

/-
Define the reflection of a point through (1/2, 1/4) and state that it is an involution.
-/
noncomputable def reflection (p : Point) : Point := !₂[1 - p 0, 1/2 - p 1]

lemma reflection_involution (p : Point) : reflection (reflection p) = p := by
  unfold reflection;
  ext i <;> fin_cases i <;> norm_num

/-
Reflection preserves distance.
-/
lemma reflection_dist (p q : Point) : dist (reflection p) (reflection q) = dist p q := by
  unfold reflection; (
  norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
  ring_nf);

lemma reflection_openSegment (x y : Point) :
    reflection '' openSegment ℝ x y = openSegment ℝ (reflection x) (reflection y) := by
  ext p
  simp [openSegment_eq_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ht, ?_⟩
    ext i <;> fin_cases i <;> norm_num [reflection] <;> ring
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ht, ?_⟩
    ext i <;> fin_cases i <;> norm_num [reflection] <;> ring

lemma continuous_reflection : Continuous reflection := by
  unfold reflection
  exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 2 => ℝ)).comp (continuous_pi fun i => by
    fin_cases i
    · exact continuous_const.sub (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 0)
    · exact continuous_const.sub (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 1))

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

noncomputable def A_inf : Point := !₂[2 / Real.sqrt 5, 1 / Real.sqrt 5]

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
  simpa [S_collection] using
    Set.Countable.union ( Set.Countable.union h_countable_seq h_countable_refl )
      ( Set.countable_singleton S_inf )

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
  induction n with
  | zero =>
    -- Let's calculate the distance from O to A_0.
    simp [O_point];
    norm_num [ dist_eq_norm, EuclideanSpace.norm_eq, A_seq, reflection ];
    exact ⟨ by norm_num [ A_0 ], by rw [ Real.sqrt_lt' ] <;> norm_num [ A_0 ] ⟩
  | succ n ih =>
    have h_next_vertex : is_next_vertex (A_seq n) (A_seq (n + 1)) := by
      rw [show A_seq (n + 1) = next_vertex (A_seq n) from rfl, next_vertex]
      split
      · rename_i h_exists
        exact Classical.choose_spec h_exists
      · rename_i h_absurd
        exact False.elim (h_absurd (exists_next_vertex (A_seq n) ih.2.le))
    refine ⟨h_next_vertex.2, ?_⟩
    unfold is_next_vertex at h_next_vertex
    rw [segment_eq_image] at h_next_vertex
    rcases h_next_vertex with ⟨⟨θ, hθ, hθeq⟩, hdist⟩
    have hθ_lt_one : θ < 1 := by
      by_contra hnot
      have hθ_eq_one : θ = 1 := le_antisymm hθ.2 (le_of_not_gt hnot)
      have hpoint : A_seq (n + 1) = reflection (A_seq n) := by
        simpa [hθ_eq_one] using hθeq.symm
      have : dist O_point (reflection (A_seq n)) = 1 := by
        simpa [hpoint] using hdist
      exact (ne_of_lt ih.2) this
    have hrefl_eq : reflection (A_seq (n + 1)) = θ • A_seq n := by
      rw [← hθeq]
      ext i <;> fin_cases i <;> norm_num [reflection, O_prime] <;> ring
    have hO_zero : O_point = (0 : Point) := by
      ext i <;> fin_cases i <;> rfl
    have hnorm : ‖A_seq n‖ = 1 := by
      rw [dist_eq_norm] at ih
      simpa [hO_zero, norm_neg] using ih.1
    calc
      dist O_point (reflection (A_seq (n + 1))) = ‖θ • A_seq n‖ := by
        rw [hrefl_eq, dist_eq_norm, hO_zero, zero_sub, norm_neg]
      _ = θ * ‖A_seq n‖ := by
        rw [norm_smul, Real.norm_of_nonneg hθ.1]
      _ < 1 := by
        rw [hnorm, mul_one]
        exact hθ_lt_one

/-
The vertices A_n are in the closed region [0,1] x [0, 1/2].
-/
def ClosedRegion_R : Set Point := {p | 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1/2}

lemma A_seq_in_closed_region (n : ℕ) : A_seq n ∈ ClosedRegion_R := by
  induction n with
  | zero =>
      simp [ClosedRegion_R, A_seq, A_0]
  | succ n ih =>
      have h_next :
          next_vertex (A_seq n) ∈ segment ℝ O_prime (reflection (A_seq n)) := by
        unfold next_vertex
        split_ifs with h
        · exact (Classical.choose_spec h).1
        · exact False.elim (h (exists_next_vertex (A_seq n) (A_seq_properties n).2.le))
      rw [segment_eq_image] at h_next
      rcases h_next with ⟨t, ht, ht_eq⟩
      rw [show A_seq (n + 1) = next_vertex (A_seq n) from rfl, ← ht_eq]
      unfold ClosedRegion_R at ih ⊢
      norm_num [O_prime, reflection] at *
      exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

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
  intro x hx
  rw [S_seq, openSegment_eq_image] at hx
  rcases hx with ⟨t, ht, rfl⟩
  have h_closed := A_seq_in_closed_region (n + 1)
  have h_pos := A_seq_pos n
  unfold ClosedRegion_R at h_closed
  unfold Region_R
  norm_num [O_point]
  have htx_pos : 0 < t * (A_seq (n + 1)) 0 := mul_pos ht.1 h_pos.1
  have htx_lt_one : t * (A_seq (n + 1)) 0 < 1 :=
    (mul_lt_of_lt_one_left h_pos.1 ht.2).trans_le h_closed.2.1
  have hty_pos : 0 < t * (A_seq (n + 1)) 1 := mul_pos ht.1 h_pos.2
  have hty_lt_half : t * (A_seq (n + 1)) 1 < 1 / 2 :=
    (mul_lt_of_lt_one_left h_pos.2 ht.2).trans_le h_closed.2.2.2
  exact ⟨htx_pos, htx_lt_one, hty_pos, hty_lt_half⟩

/-
The segments S_seq_refl n are contained in the region R.
-/
lemma S_seq_refl_in_region (n : ℕ) : S_seq_refl n ⊆ Region_R := by
  intro p hp
  rw [S_seq_refl, openSegment_eq_image] at hp
  rcases hp with ⟨t, ht, rfl⟩
  have h_pos := A_seq_pos n
  have h_closed := A_seq_in_closed_region (n + 1)
  unfold ClosedRegion_R at h_closed
  unfold Region_R
  norm_num [O_prime, reflection]
  have htx_pos : 0 < t * (A_seq (n + 1)) 0 := mul_pos ht.1 h_pos.1
  have htx_lt_one : t * (A_seq (n + 1)) 0 < 1 :=
    (mul_lt_of_lt_one_left h_pos.1 ht.2).trans_le h_closed.2.1
  have hty_pos : 0 < t * (A_seq (n + 1)) 1 := mul_pos ht.1 h_pos.2
  have hty_lt_half : t * (A_seq (n + 1)) 1 < 1 / 2 :=
    (mul_lt_of_lt_one_left h_pos.2 ht.2).trans_le h_closed.2.2.2
  exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

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
  have h_exists : ∃ P, is_next_vertex (A_seq n) P :=
    exists_next_vertex (A_seq n) (A_seq_properties n).2.le
  rw [show A_seq (n + 1) = next_vertex (A_seq n) from rfl]
  rw [next_vertex]
  simp [h_exists]
  have h_choose := Classical.choose_spec h_exists
  obtain ⟨hP_segment, hP_dist⟩ := h_choose
  have hP_ne_O_prime : Classical.choose h_exists ≠ O_prime := by
      intro h'
      have hdist : dist O_point O_prime = 1 := by
        simpa [h'] using hP_dist
      linarith [dist_O_O_prime]
  have hP_ne_reflection : Classical.choose h_exists ≠ reflection (A_seq n) := by
      intro hP_eq_reflection
      have hdist : dist O_point (reflection (A_seq n)) = 1 := by
        simpa [hP_eq_reflection] using hP_dist
      linarith [(A_seq_properties n).2]
  exact
    mem_openSegment_of_ne_left_right (id (Ne.symm hP_ne_O_prime)) (id (Ne.symm hP_ne_reflection))
      hP_segment

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
        refine ⟨ ?_, ?_, ?_ ⟩;
        · -- By the properties of the norm, we can bound the expression.
          have h_norm_bound : ‖t1 • A + t2 • B + t3 • C - A‖ ≤ t2 * ‖B - A‖ + t3 * ‖C - A‖ := by
            convert norm_add_le ( t2 • ( B - A ) ) ( t3 • ( C - A ) ) using 1;
            · exact congr_arg Norm.norm ( by rw [ show t1 = 1 - t2 - t3 by linarith ] ; ext ; norm_num ; ring );
            · rw [ norm_smul, norm_smul, Real.norm_of_nonneg ht2, Real.norm_of_nonneg ht3 ];
          exact h_norm_bound.trans ( by rw [ norm_sub_rev B A ] at *; nlinarith );
        · -- By the properties of the norm, we can bound the distance.
          have h_norm_bound : ‖t1 • (A - B) + t3 • (C - B)‖ ≤ t1 * ‖A - B‖ + t3 * ‖C - B‖ := by
            exact norm_add_le_of_le ( by rw [ norm_smul, Real.norm_of_nonneg ht1 ] ) ( by rw [ norm_smul, Real.norm_of_nonneg ht3 ] );
          have h_vec :
              t1 • A + t2 • B + t3 • C - B = t1 • (A - B) + t3 • (C - B) := by
            rw [show t2 = 1 - t1 - t3 by linarith [hp_convex.1]]
            ext i <;> simp <;> ring
          rw [h_vec]
          exact h_norm_bound.trans (by
            rw [ norm_sub_rev C B ]
            nlinarith [ norm_nonneg ( A - B ), norm_nonneg ( B - C ) ])
        · rw [ show t1 • A + t2 • B + t3 • C - C = t1 • ( A - C ) + t2 • ( B - C ) by ext i; simpa using by rw [ show t3 = 1 - t1 - t2 by linarith ] ; simpa using by ring ];
          refine le_trans ( norm_add_le ( t1 • ( A - C ) ) ( t2 • ( B - C ) ) ) ?_;
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
        refine ⟨ ?_, ?_, ?_, ?_ ⟩ <;> nlinarith only [ ha, hb, hc, ha', hb', hc', hx_comb, hy_comb, h_simplified, h_line_segment, hCA, hBC, hAB, mul_nonneg ha hc', mul_nonneg hb hc', mul_nonneg hc ha', mul_nonneg hc hb' ];
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
        intro p hp
        exact hL_sub (by simpa [hxy.2] using hp)
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
            exact fun s => s.finite_toSet.isCompact_convexHull ℝ;
          exact IsCompact.isClosed ( h_convex_hull_closed s ));
        exact h_convex_hull_closed { O_point, reflection ( A_seq n ), A_seq ( n + 1 ) } |> fun h => by
          simpa [Triangle_OA_prime_P] using h;
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
    convert ( (s.finite_toSet.isCompact_convexHull ℝ).isClosed ) using 1;
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
    refine ⟨ b, ⟨ hb, by linarith ⟩, ?_ ⟩ ;
    ext i <;> fin_cases i <;> norm_num [ reflection, O_point, O_prime ] <;> nlinarith
  -- By definition of $A_seq$, we know that $A_{n+1}$ lies on the segment $O'A'_n$, and $A'_{n+1}$ lies on the segment $OA_n$.
  have h_vertices : {O_point, A_seq (n + 1), O_prime, reflection (A_seq (n + 1))} ⊆ {O_point, A_seq n, O_prime, reflection (A_seq n)} ∪ segment ℝ O_point (A_seq n) ∪ segment ℝ O_prime (reflection (A_seq n)) := by
    simp_all +decide [ Set.insert_subset_iff ];
  -- By definition of $A_seq$, we know that $A_{n+1}$ lies on the segment $O'A'_n$, and $A'_{n+1}$ lies on the segment $OA_n$. Therefore, the convex hull of $\{O, A_{n+1}, O', A'_{n+1}\}$ is contained in the convex hull of $\{O, A_n, O', A'_n\}$.
  have h_convex_hull : convexHull ℝ {O_point, A_seq (n + 1), O_prime, reflection (A_seq (n + 1))} ⊆ convexHull ℝ ({O_point, A_seq n, O_prime, reflection (A_seq n)} ∪ segment ℝ O_point (A_seq n) ∪ segment ℝ O_prime (reflection (A_seq n))) := by
    exact convexHull_mono h_vertices;
  -- Since the convex hull of the union of the segments is contained in the convex hull of the vertices, we have:
  have h_convex_hull_union : convexHull ℝ ({O_point, A_seq n, O_prime, reflection (A_seq n)} ∪ segment ℝ O_point (A_seq n) ∪ segment ℝ O_prime (reflection (A_seq n))) ⊆ convexHull ℝ {O_point, A_seq n, O_prime, reflection (A_seq n)} := by
    refine convexHull_min ?_ ?_;
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
      refine convexHull_min ?_ ?_;
      · rintro x ( rfl | rfl | rfl ) <;> norm_num [ Parallelogram_seq ];
        · exact subset_convexHull ℝ _ ( Set.mem_insert _ _ );
        · exact subset_convexHull ℝ _ ( by norm_num [ Parallelogram ] );
        · -- By definition of $A_{n+1}$, we know that $A_{n+1}$ lies on the segment $O'A'_n$.
          have h_A_seq_in_segment : A_seq (n + 1) ∈ segment ℝ O_prime (reflection (A_seq n)) := by
            exact A_seq_mem_closed_segment n;
          refine segment_subset_convexHull ?_ ?_ h_A_seq_in_segment;
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
      exact Parallelogram_symmetric (A_seq n) y hy_in_Pn |> fun h => by
        simpa [Parallelogram_seq, Parallelogram] using h;
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
        refine ⟨ a • O_point + b • A_seq ( n + 1 ), ?_, ?_ ⟩ <;> norm_num [ openSegment_eq_image ];
        · exact ⟨ b, ⟨ hb, by linarith ⟩, by rw [ ← eq_sub_iff_add_eq' ] at hab; subst hab; ext i; fin_cases i <;> norm_num ⟩;
        · ext i <;> fin_cases i <;> norm_num [ reflection, O_point, O_prime ] <;> nlinarith
      · rintro ⟨ x, hx, rfl ⟩;
        obtain ⟨ a, b, ha, hb, hab, rfl ⟩ := hx;
        refine ⟨ a, b, ha, hb, hab, ?_ ⟩;
        ext i <;> fin_cases i <;> norm_num [ reflection, O_point, O_prime ] <;> nlinarith
    · obtain ⟨ x, y, hxy, rfl ⟩ := hL;
      refine ⟨ reflection x, reflection y, ?_, ?_ ⟩;
      · rw [ reflection_dist, hxy ];
      · exact reflection_openSegment x y
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
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      rw [ pow_succ', mul_assoc ];
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
      exact squeeze_zero ( fun n => abs_nonneg _ ) ( fun n => dist_from_diagonal_bound n ) ( by
        simpa [contraction_factor] using
          tendsto_pow_atTop_nhds_zero_of_lt_one
            ( by exact div_nonneg ( sub_nonneg.mpr <| Real.sqrt_le_iff.mpr <| by norm_num ) zero_le_two )
            ( show ( 2 - Real.sqrt 3 ) / 2 < 1 by
              nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt <| show 0 ≤ 3 by norm_num ] )
            |> Filter.Tendsto.mul_const _ );
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
  have hab_lt : a < b := by linarith
  have hab_ne : a ≠ b := ne_of_lt hab_lt
  have h_closure_subset : closure (Set.Ioo a b) ⊆ Set.Icc 0 d :=
    isClosed_Icc.closure_subset_iff.mpr h_subset
  have h_lower : 0 ≤ a := by
    have ha_closure : a ∈ closure (Set.Ioo a b) := by
      rw [closure_Ioo hab_ne]
      exact ⟨le_rfl, hab_lt.le⟩
    exact (h_closure_subset ha_closure).1
  have h_upper : b ≤ d := by
    have hb_closure : b ∈ closure (Set.Ioo a b) := by
      rw [closure_Ioo hab_ne]
      exact ⟨hab_lt.le, le_rfl⟩
    exact (h_closure_subset hb_closure).2
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
  refine ⟨ h_closure ?_, h_closure ?_ ⟩;
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
        convert image_dist_O_openSegment_v2 x y hx hy _ using 1
        focus
          aesop
        rintro rfl; norm_num at hxy;
      cases le_total ( dist O_point x ) ( dist O_point y ) <;> simp +decide [ *, abs_of_nonneg, abs_of_nonpos ];
      · aesop;
      · aesop;
    -- By `dist_on_segment_O_O_prime`, `|dist O x - dist O y| = dist x y = 1`.
    have h_dist_eq : |dist O_point x - dist O_point y| = dist x y := by
      exact Eq.symm (dist_on_segment_O_O_prime x y hx hy);
    aesop

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
      refine ⟨ t / ( 2 / Real.sqrt 5 ), ?_, ?_, ?_ ⟩ <;> norm_num;
      · positivity;
      · rw [ dist_eq_norm, EuclideanSpace.norm_eq ] at * ; norm_num at *;
        rw [ Real.sqrt_lt' ] at h_lt <;> norm_num [ O_point, O_prime ] at * ; nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
    use 1 - s, s, by linarith, by linarith, by
      ring;
    ext i ; fin_cases i <;> norm_num [ hs₁, O_point, O_prime, A_inf ] ; ring;
  rw [ segment_eq_image ] at *;
  rcases h_segment with ⟨ θ, ⟨ hθ₀, hθ₁ ⟩, rfl ⟩ ; simp_all +decide [ S_inf ] ;
  refine ⟨ 1 - θ, θ, ?_, ?_, ?_ ⟩ <;> norm_num [ EuclideanSpace.norm_eq ] at *;
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
    refine ⟨ θ, ⟨ hθ.1.le, hθ.2.le ⟩, ?_ ⟩ ; rw [ ← h ] ; ext i ; fin_cases i <;> norm_num [ O_prime, O_point ];
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
    · refine Or.inl ⟨ θ'' / θ', ?_, θ, ?_, ?_ ⟩;
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
    refine Set.ext fun x => ⟨ ?_, ?_ ⟩ <;> intro hx;
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
      refine ⟨ Fin 3, { 0, 1, 2 }, fun i => if i = 0 then a else if i = 1 then b else c, fun i => if i = 0 then reflection O_point else if i = 1 then reflection ( reflection ( A_seq n ) ) else reflection ( A_seq ( n + 1 ) ), ?_, ?_, ?_, ?_ ⟩ <;> simp +decide [ *, Finset.centerMass ];
      · linarith;
      · exact ⟨ Or.inl <| O_prime_reflection_O, Or.inr <| Or.inl <| reflection_involution _ ⟩;
      · norm_num [ ← add_assoc, habc.1 ];
    · -- By definition of $Triangle_seq_refl$, we know that $x$ is in the image of the convex hull of $\{O, A'_n, A_{n+1}\}$ under the reflection map.
      obtain ⟨y, hy⟩ : ∃ y ∈ convexHull ℝ {O_point, reflection (A_seq n), A_seq (n + 1)}, reflection y = x := by
        simp_all +decide [ convexHull_insert ];
        rcases hx with ⟨ y, hy, hx ⟩;
        refine ⟨ reflection x, ?_, ?_ ⟩ <;> simp_all +decide [ segment_eq_image ];
        · rcases hy with ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; rcases hx with ⟨ b, ⟨ hb₁, hb₂ ⟩, rfl ⟩ ; use a, ⟨ ha₁, ha₂ ⟩, b, ⟨ hb₁, hb₂ ⟩ ; ext i <;> fin_cases i <;> norm_num [ reflection, O_point, O_prime ] <;> ring_nf
        · exact reflection_involution x;
      exact Set.mem_image_of_mem _ hy.1 |> fun h => hy.2 ▸ h

/-
The triangle O O' A'_n splits into Triangle_OA_prime_P n and O O' A_{n+1}.
-/
lemma Triangle_split_1 (n : ℕ) : convexHull ℝ {O_point, O_prime, reflection (A_seq n)} = Triangle_OA_prime_P n ∪ convexHull ℝ {O_point, O_prime, A_seq (n + 1)} := by
  have h_convex_hull_split : convexHull ℝ {O_point, O_prime, reflection (A_seq n)} = convexHull ℝ {O_point, A_seq (n + 1), reflection (A_seq n)} ∪ convexHull ℝ {O_point, O_prime, A_seq (n + 1)} := by
    apply Set.Subset.antisymm _;
    · refine Set.union_subset ?_ ?_;
      · refine convexHull_min ?_ ?_;
        · norm_num [ Set.insert_subset_iff, convexHull_insert ];
          refine ⟨ ⟨ O_prime, ?_, ?_ ⟩, ⟨ A_seq ( n + 1 ), ?_, ?_ ⟩, ⟨ reflection ( A_seq n ), ?_, ?_ ⟩ ⟩ <;> norm_num [ segment_eq_image ];
          · exact ⟨ 0, by norm_num ⟩;
          · exact ⟨ 0, by norm_num ⟩;
          · have := A_seq_mem_closed_segment n;
            rw [ segment_eq_image ] at this ; aesop;
          · exact ⟨ 1, by norm_num ⟩;
          · exact ⟨ 1, by norm_num ⟩;
          · exact ⟨ 1, by norm_num ⟩;
        · exact convex_convexHull ℝ _;
      · refine convexHull_min ?_ ?_;
        · simp +decide [ Set.insert_subset_iff ];
          refine ⟨ subset_convexHull ℝ {O_point, O_prime, reflection (A_seq n)} (by simp),
            subset_convexHull ℝ {O_point, O_prime, reflection (A_seq n)} (by simp), ?_ ⟩;
          -- By definition of $A_{n+1}$, we know that it lies on the segment $O' A'_n$.
          have h_A_seq_next_on_segment : A_seq (n + 1) ∈ segment ℝ O_prime (reflection (A_seq n)) := by
            exact A_seq_mem_closed_segment n;
          rw [ convexHull_eq ];
          rcases h_A_seq_next_on_segment with ⟨ a, b, ha, hb, hab, h ⟩;
          refine ⟨ Fin 2, { 0, 1 }, fun i => if i = 0 then a else b, fun i => if i = 0 then O_prime else reflection ( A_seq n ), ?_, ?_, ?_, ?_ ⟩ <;> simp +decide [ *, Finset.centerMass ];
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
      constructor <;> refine convexHull_min ?_ ?_;
      · norm_num [ Set.insert_subset_iff, convexHull_pair ];
        refine ⟨ subset_convexHull ℝ {O_prime, A_seq n, O_point} (by simp), ?_,
          subset_convexHull ℝ {O_prime, A_seq n, O_point} (by simp) ⟩;
        rw [ convexHull_insert ] <;> norm_num;
        refine ⟨ reflection ( A_seq ( n + 1 ) ), ?_, ?_ ⟩;
        · convert reflection_A_seq_next_mem_segment_O_A_seq n using 1;
          exact segment_symm ℝ (A_seq n) O_point;
        · exact right_mem_segment _ _ _;
      · exact convex_convexHull ℝ _;
      · norm_num [ Set.insert_subset_iff, convexHull_insert ];
        refine ⟨ ⟨ O_point, ?_, ?_ ⟩, ⟨ A_seq n, ?_, ?_ ⟩, ⟨ reflection ( A_seq ( n + 1 ) ), ?_, ?_ ⟩ ⟩ <;> norm_num [ segment_symm ];
        · exact left_mem_segment ℝ O_point (A_seq n);
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
    refine Set.Subset.antisymm ?_ ?_;
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
          refine ⟨ Fin 3, { 0, 1, 2 }, fun i => if i = 0 then 1 - x' - y' else if i = 1 then x' else y', fun i => if i = 0 then O_point else if i = 1 then A else O_prime, ?_, ?_, ?_, ?_ ⟩ <;> simp +decide [ Finset.centerMass ];
          · exact ⟨ by linarith, hx'_nonneg, hy'_nonneg ⟩;
          · rw [ hx'_eq ] ; ext i ; norm_num ; ring_nf;
            exact Or.inr ( by fin_cases i <;> rfl );
        exact Or.inl hx'_conv;
      · -- Since $\delta > \beta$, we can write $x$ as a convex combination of $O$, $O'$, and $A'$.
        have hx_comb : x = (α + β) • O_point + (γ + β) • O_prime + (δ - β) • reflection A := by
          ext i; have := congr_arg (fun p : Point => p i) h_sum; norm_num at *; rw [ hαβγδ.2.2.2.2.2 ] ; ring_nf;
          rw [ show O_prime i = A i + reflection A i by rw [ ← this ] ] ; norm_num ; ring_nf;
          rw [ show O_prime i = A i + reflection A i by rw [ ← this ] ] ; ring_nf;
          fin_cases i <;> norm_num [ O_point ];
        refine Or.inr ?_;
        rw [ hx_comb, convexHull_eq ];
        refine ⟨ Fin 3, { 0, 1, 2 }, fun i => if i = 0 then α + β else if i = 1 then γ + β else δ - β, fun i => if i = 0 then O_point else if i = 1 then O_prime else reflection A, ?_, ?_, ?_, ?_ ⟩ <;> simp +decide [ *, Finset.centerMass ];
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
  ext i <;> fin_cases i <;> norm_num [ reflection, O_prime ] <;> ring

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
    aesop;
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
  refine ⟨ ( B ) ᶜ, isOpen_compl_iff.mpr hB, ( A ) ᶜ, isOpen_compl_iff.mpr hA, ?_, ?_, ?_, ?_ ⟩ <;> simp_all +decide [ Set.Nonempty ];
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
          ext i <;> fin_cases i <;> norm_num [ reflection, O_prime ] <;> ring
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
    have h_nonzero : ∀ n, (A_seq n) 0 - 2 * (A_seq n) 1 ≠ 0 := by
      intro n
      induction n with
      | zero =>
          norm_num [A_seq, A_0]
      | succ n ih =>
          have hseg : A_seq (n + 1) ∈ openSegment ℝ O_prime (reflection (A_seq n)) :=
            A_seq_between n
          rw [openSegment_eq_image] at hseg
          rcases hseg with ⟨t, ht, ht_eq⟩
          have hsigned :
              (A_seq (n + 1)) 0 - 2 * (A_seq (n + 1)) 1 =
                -t * ((A_seq n) 0 - 2 * (A_seq n) 1) := by
            rw [← ht_eq]
            unfold O_prime reflection
            norm_num
            ring
          intro hzero
          have hmul : t * ((A_seq n) 0 - 2 * (A_seq n) 1) = 0 := by
            nlinarith
          rcases mul_eq_zero.mp hmul with ht_zero | hs_zero
          · exact ht.1.ne' ht_zero
          · exact ih hs_zero
    unfold dist_from_diagonal
    exact abs_pos.mpr (h_nonzero n)
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
  have hinj : Function.Injective reflection := by
    intro p q hpq
    calc
      p = reflection (reflection p) := (reflection_involution p).symm
      _ = reflection (reflection q) := by rw [hpq]
      _ = q := reflection_involution q
  have himage : ∀ k, S_seq_refl k = reflection '' S_seq k := by
    intro k
    calc
      S_seq_refl k = openSegment ℝ (reflection O_point) (reflection (A_seq (k + 1))) := by
        simp [S_seq_refl, O_prime_reflection_O]
      _ = reflection '' S_seq k := by
        rw [S_seq, reflection_openSegment]
  rw [himage n, himage m]
  exact Set.disjoint_image_of_injective hinj (S_seq_disjoint n m h)

/-
The signed distance of A_n from the diagonal alternates sign: positive for even n, negative for odd n.
-/
def signed_dist_from_diagonal (p : Point) : ℝ := p 0 - 2 * p 1

lemma signed_dist_A_seq_sign (n : ℕ) :
  (Even n → signed_dist_from_diagonal (A_seq n) > 0) ∧
  (Odd n → signed_dist_from_diagonal (A_seq n) < 0) := by
    induction n with
    | zero =>
      constructor
      · intro _
        unfold signed_dist_from_diagonal
        norm_num [A_seq, A_0]
      · intro h
        simp at h
    | succ n ih =>
      have h_A_seq_succ : A_seq (n + 1) ∈ openSegment ℝ O_prime (reflection (A_seq n)) := by
        exact A_seq_between n;
      obtain ⟨t, ht⟩ : ∃ t ∈ Set.Ioo (0 : ℝ) 1, A_seq (n + 1) = (1 - t) • O_prime + t • reflection (A_seq n) := by
        rw [ openSegment_eq_image ] at h_A_seq_succ ; aesop;
      have h_signed_dist_succ :
          signed_dist_from_diagonal (A_seq (n + 1)) =
            -t * signed_dist_from_diagonal (A_seq n) := by
        rw [ht.2]
        unfold signed_dist_from_diagonal O_prime reflection
        norm_num
        ring
      constructor
      · intro hn_even_succ
        have hn_odd : Odd n := by
          simpa [Nat.even_add_one] using hn_even_succ
        have hn_neg := ih.2 hn_odd
        rw [h_signed_dist_succ]
        nlinarith [ht.1.1, hn_neg]
      · intro hn_odd_succ
        have hn_even : Even n := by
          simpa [Nat.odd_add_one] using hn_odd_succ
        have hn_pos := ih.1 hn_even
        rw [h_signed_dist_succ]
        nlinarith [ht.1.1, hn_pos]

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
      refine ⟨ a • O_point + ha • A_seq (n + 1), ⟨ a, ha, b, hb, hab, rfl ⟩, ?_ ⟩;
      unfold reflection; ext i; fin_cases i <;> norm_num [ O_point, O_prime, A_0 ]
      focus
        ring_nf
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
      simp [O_point] at *; nlinarith;
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
      refine ⟨ a • O_point + b • A_seq ( n + 1 ), ?_, ?_ ⟩ <;> norm_num [ openSegment_eq_image ];
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
  by_cases hn : Even n
  · have hm : Even m := by
      rw [Nat.even_iff]
      rw [← h]
      exact Nat.even_iff.mp hn
    exact Set.disjoint_left.mpr fun p hp hp' => by
      have hneg := (S_seq_sign n).1 hn p hp
      have hpos := (S_seq_refl_sign m).1 hm p hp'
      linarith
  · have hn_odd : Odd n := Nat.not_even_iff_odd.mp hn
    have hm_odd : Odd m := by
      have hn_mod : n % 2 = 1 := Nat.odd_iff.mp hn_odd
      rw [Nat.odd_iff]
      rw [← h]
      exact hn_mod
    exact Set.disjoint_left.mpr fun p hp hp' => by
      have hpos := (S_seq_sign n).2 hn_odd p hp
      have hneg := (S_seq_refl_sign m).2 hm_odd p hp'
      linarith

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
          induction k, hk_n_plus_1 using Nat.le_induction with
          | base =>
            exact Parallelogram_seq_subset (n + 1)
          | succ k hk ih =>
            exact Set.Subset.trans ( Parallelogram_seq_subset _ ) ih;
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
            rcases hp with ⟨ q, hq, x, hx, rfl ⟩ ; rw [ convexHull_insert ] at hq
            focus
              norm_num at hq
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
  have hinj : Function.Injective reflection := by
    intro p q hpq
    calc
      p = reflection (reflection p) := (reflection_involution p).symm
      _ = reflection (reflection q) := by rw [hpq]
      _ = q := reflection_involution q
  have h_reflection_bij :
      ∀ (S T : Set Point), Disjoint S T → Disjoint (reflection '' S) (reflection '' T) := by
    intro S T hST
    exact Set.disjoint_image_of_injective hinj hST
  have himage : ∀ k, S_seq_refl k = reflection '' S_seq k := by
    intro k
    calc
      S_seq_refl k = openSegment ℝ (reflection O_point) (reflection (A_seq (k + 1))) := by
        simp [S_seq_refl, O_prime_reflection_O]
      _ = reflection '' S_seq k := by
        rw [S_seq, reflection_openSegment]
  have himage_back : ∀ k, S_seq k = reflection '' S_seq_refl k := by
    intro k
    rw [himage k]
    ext p
    simp [Set.mem_image, reflection_involution]
  rw [himage n, himage_back m]
  exact h_reflection_bij _ _ h_disjoint_refl

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
  have h_p_convex : p ∈ convexHull ℝ {!₂[0, 0], !₂[1, 0], !₂[1, 1/2], !₂[0, 1/2]} := by
    rw [ convexHull_eq ];
    use Fin 4;
    refine ⟨ { 0, 1, 2, 3 }, fun i => if i = 0 then ( 1 - p 0 ) * ( 1 - p 1 * 2 ) else if i = 1 then p 0 * ( 1 - p 1 * 2 ) else if i = 2 then p 0 * p 1 * 2 else ( 1 - p 0 ) * p 1 * 2, fun i => if i = 0 then !₂[0, 0] else if i = 1 then !₂[1, 0] else if i = 2 then !₂[1, 1 / 2] else !₂[0, 1 / 2], ?_, ?_, ?_, ?_ ⟩ <;> simp +decide [ Finset.centerMass ];
    · exact ⟨ mul_nonneg ( by linarith ) ( by linarith ), mul_nonneg ( by linarith ) ( by linarith ), mul_nonneg ( by linarith ) ( by linarith ), mul_nonneg ( by linarith ) ( by linarith ) ⟩;
    · ring;
    · ext i <;> fin_cases i <;> norm_num <;> ring_nf
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
  · intro x hx
    have hx' := Parallelogram_covered n hx
    aesop;
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
        have hn_pos := (signed_dist_A_seq_sign n).1 hn
        have hn1_odd : Odd (n + 1) := by
          simpa [Nat.odd_add_one] using hn
        have hn1_neg := (signed_dist_A_seq_sign (n + 1)).2 hn1_odd
        unfold signed_dist_from_diagonal at hn_pos hn1_neg
        exact ⟨hn_pos, hn1_neg⟩
      unfold O_point at *; norm_num at *; nlinarith;
    · -- By definition of $Triangle_OA_prime_P$, we know that $p$ is a convex combination of $O$, $reflection (A_seq n)$, and $A_seq (n + 1)$.
      obtain ⟨a, b, c, ha, hb, hc, hsum, hp_eq⟩ :
          ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧
            p = a • O_point + b • reflection (A_seq n) + c • A_seq (n + 1) := by
        unfold Triangle_OA_prime_P at hp;
        norm_num [ convexHull_insert ] at hp;
        rcases hp with ⟨ q, ⟨ a, b, ha, hb, hab, rfl ⟩, ⟨ c, d, hc, hd, hcd, rfl ⟩ ⟩ ; exact ⟨ c, d * a, d * b, by positivity, by positivity, by positivity, by nlinarith, by ext ; simpa using by ring ⟩ ;
      -- Since $n$ is odd, by `signed_dist_A_seq_sign`, we have $signed_dist_from_diagonal (A_seq n) < 0$ and $signed_dist_from_diagonal (A_seq (n + 1)) > 0$.
      have h_signed_dist_A_seq_neg : signed_dist_from_diagonal (A_seq n) < 0 := by
        exact signed_dist_A_seq_sign n |>.2 hn
      have h_signed_dist_A_seq_pos : signed_dist_from_diagonal (A_seq (n + 1)) > 0 := by
        have hn1_even : Even (n + 1) := by
          simpa [Nat.even_add_one] using hn
        exact (signed_dist_A_seq_sign (n + 1)).1 hn1_even
      rw [hp_eq]
      unfold signed_dist_from_diagonal at *
      unfold reflection at *
      norm_num [O_point] at *
      nlinarith

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
      -- By definition of $A_seq$, we know that $A_seq (n + 1) = t • O_prime + (1 - t) • reflection (A_seq n)$ for some $t \in (0, 1)$.
      obtain ⟨t, ht⟩ : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ A_seq (n + 1) = t • O_prime + (1 - t) • reflection (A_seq n) := by
        have := A_seq_between n; simp_all +decide [ openSegment_eq_image ] ;
        obtain ⟨ t, ht₁, ht₂ ⟩ := this; exact ⟨ 1 - t, by linarith, by linarith, by simpa [ add_comm ] using ht₂.symm ⟩ ;
      intro hzero
      have h_f_A : (separating_functional n) (A_seq (n + 1)) = 0 :=
        (separating_functional_properties n).2.1
      rw [ht.2.2, map_add, map_smul, map_smul, hzero] at h_f_A
      have h_O_zero : (separating_functional n) O_prime = 0 := by
        simpa [smul_eq_mul, ht.1.ne'] using h_f_A
      exact (separating_functional_values n).2 h_O_zero
    exact mul_left_cancel₀ h_sep_nonzero <| by linarith;
  -- The set of points in $P_{n+1}$ where $f=0$ is the segment $[O, A_{n+1}]$.
  have h_segment : {p ∈ Parallelogram_seq (n + 1) | separating_functional n p = 0} = segment ℝ O_point (A_seq (n + 1)) := by
    ext p_of_subset_of_subset;
    constructor <;> intro hp;
    · -- By definition of $P_{n+1}$, we know that $p_of_subset_of_subset$ is a convex combination of $O$, $A_{n+1}$, $O'$, and $A'_{n+1}$.
      obtain ⟨a, b, c, d, ha, hb, hc, hd, habcd⟩ : ∃ a b c d : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ a + b + c + d = 1 ∧ p_of_subset_of_subset = a • O_point + b • A_seq (n + 1) + c • O_prime + d • reflection (A_seq (n + 1)) := by
        have h_convex_comb : p_of_subset_of_subset ∈ convexHull ℝ {O_point, A_seq (n + 1), O_prime, reflection (A_seq (n + 1))} := by
          focus
            exact hp.1
        rw [ convexHull_insert ] at h_convex_comb;
        · norm_num [ segment_eq_image ] at h_convex_comb;
          rcases h_convex_comb with ⟨ i, hi, x, hx, rfl ⟩
          rw [ convexHull_insert ] at hi
          focus
            norm_num at hi
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
        have hfp_zero := hp.2
        rw [h_f_simplified, ← h_cd_zero.1] at hfp_zero
        have h_mul : (c + d) * (separating_functional n) O_prime = 0 := by
          nlinarith
        exact (mul_eq_zero.mp h_mul).resolve_right h_cd_zero.2
      norm_num [ show c = 0 by linarith, show d = 0 by linarith ] at *;
      exact ⟨ a, b, ha, hb, habcd.1, by simp [ habcd.2 ] ⟩;
    · refine ⟨ ?_, ?_ ⟩;
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
          simpa [A_seq] using A_seq_mem_closed_segment 0;
        -- Since $A_seq 1$ lies on the segment $O' (reflection A_0)$, its y-coordinate is $1/2$.
        have hA1_y : (A_seq 1) 1 = 1 / 2 := by
          obtain ⟨ a, b, ha, hb, hab, h ⟩ := hA1_segment;
          have := congr_arg (fun p : Point => p 1) h; norm_num [ O_prime, reflection, A_0 ] at *; nlinarith;
        exact absurd ( hL_region h0 ) ( by rintro ⟨ h1, h2, h3, h4 ⟩ ; linarith );
      · exact hL_disj _ ( Set.mem_union_left _ <| Set.mem_union_right _ ⟨ n, rfl ⟩ ) h0 ( by simpa using A_succ_mem_S_seq_refl_pred ( n + 1 ) ( Nat.succ_pos _ ) );
    · rcases n <;> simp_all +decide [ Set.disjoint_left ];
      · -- By definition of $A_seq$, we know that $A_seq 1$ is the point on $[O', A_0']$ such that $|O - A_seq 1| = 1$.
        obtain ⟨t, ht⟩ : ∃ t : ℝ, t ∈ Set.Ioo 0 1 ∧ A_seq 1 = O_prime + t • (reflection A_0 - O_prime) := by
          have hA1 : A_seq 1 ∈ openSegment ℝ O_prime (reflection A_0) := by
            simpa [A_seq] using A_seq_in_open_segment 0;
          rw [ openSegment_eq_image ] at hA1;
          obtain ⟨ t, ht, h ⟩ := hA1; exact ⟨ t, ht, by ext i; have := congr_arg (fun p : Point => p i) h; norm_num at *; linarith ⟩ ;
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
    · exact h_disjoint y ‹_› ‹_› ( by ext i; have := congr_arg (fun p : Point => p i) hy₃; norm_num at *; linarith );
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
    exact h_finite.isCompact_convexHull ℝ;
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
      exact fun s => s.finite_toSet.isCompact_convexHull ℝ;
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
      have hsym := Parallelogram_symmetric (A_seq (n + 1)) (reflection y) hx_parallelogram
      simpa [Parallelogram_seq, reflection_involution] using hsym;
    exact Tn_inter_Pn_subset_closure_S_seq n ⟨ hy_triangle, hy_parallelogram ⟩;
  -- Since reflection is a continuous function, applying it to the closure of S_seq n should give me the closure of the reflection of S_seq n.
  have h_reflection_closure : reflection '' closure (S_seq n) ⊆ closure (reflection '' S_seq n) := by
    intro z hz
    obtain ⟨w, hw_closure, rfl⟩ := hz
    have hw_closure_S_seq : w ∈ closure (S_seq n) := hw_closure
    have h_reflection_closure_S_seq : reflection w ∈ closure (reflection '' S_seq n) := by
      have h_reflection_closure_S_seq : Continuous reflection := by
        exact continuous_reflection
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
              · use fun t => ( 1 - t ) • v + t • hv_unit;
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
    induction n with
    | zero =>
      exact hL_subset.trans ( Region_subset_P0 )
    | succ n ih =>
      apply L_subset_Parallelogram_succ n L hL_unit ih (by
      exact fun s hs => by push Not at h_disjoint; exact h_disjoint s hs |> Disjoint.symm;) hL_subset;
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

def S_shifted : Set (Set Point) := {s | ∃ t ∈ S_collection, s = (fun p => p + (!₂[0, 1/2] : Point)) '' t}

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
    obtain ⟨a, b, hab, ht⟩ := ht_unit
    refine ⟨a + (!₂[0, 1 / 2] : Point), b + (!₂[0, 1 / 2] : Point), ?_, ?_⟩
    · simpa [dist_eq_norm, add_sub_add_right_eq_sub] using hab
    · rw [ht]
      simpa [add_comm, add_left_comm, add_assoc] using
        (openSegment_translate_image (𝕜 := ℝ) (!₂[0, 1 / 2] : Point) a b)
  · -- By definition of $S_shifted$, if $s \in S_shifted$ and $t \in S_shifted$, then there exist $t1, t2 \in S_collection$ such that $s = t1 + (0, 1/2)$ and $t = t2 + (0, 1/2)$.
    intro s t hs ht hne
    obtain ⟨t1, ht1, rfl⟩ := hs
    obtain ⟨t2, ht2, rfl⟩ := ht;
    -- Since $t1$ and $t2$ are disjoint, their images under the translation by $(0, 1/2)$ are also disjoint.
    have h_disjoint : Disjoint t1 t2 := by
      exact S_collection_pairwise_disjoint t1 t2 ht1 ht2 ( by aesop );
    exact Set.disjoint_image_of_injective (fun x y hxy => add_right_cancel hxy) h_disjoint

/-
The shifted collection is blocking in the upper region.
-/
lemma S_shifted_is_blocking : IsBlocking S_shifted Region_Upper := by
  intro L hL_unit hL_subset;
  -- Let $v = (0, 1/2)$.
  set v : Point := !₂[0, 1 / 2];
  -- Let $L' = L - v$.
  set L' : Set Point := {p | p + v ∈ L};
  -- Since $L'$ is a unit segment in $Region_R$, by the blocking property of $S_collection$, there exists $s \in S_collection$ such that $L'$ intersects $s$.
  obtain ⟨s, hs⟩ : ∃ s ∈ S_collection, ¬Disjoint s L' := by
    apply S_collection_is_blocking L';
    · obtain ⟨ x, y, hxy, hL_eq ⟩ := hL_unit
      refine ⟨x - v, y - v, ?_, ?_⟩
      · rw [dist_eq_norm] at hxy ⊢
        convert hxy using 2
        ext i <;> simp
      · ext p
        unfold L'
        constructor
        · intro hp
          rw [hL_eq, openSegment_eq_image] at hp
          rcases hp with ⟨t, ht, hp⟩
          rw [openSegment_eq_image]
          refine ⟨t, ht, ?_⟩
          ext i <;> fin_cases i
          · have hpi := congr_arg (fun q : Point => q 0) hp
            simp [v] at hpi ⊢
            linarith
          · have hpi := congr_arg (fun q : Point => q 1) hp
            simp [v] at hpi ⊢
            linarith
        · intro hp
          rw [hL_eq, openSegment_eq_image]
          rw [openSegment_eq_image] at hp
          rcases hp with ⟨t, ht, hp⟩
          refine ⟨t, ht, ?_⟩
          ext i <;> fin_cases i
          · have hpi := congr_arg (fun q : Point => q 0) hp
            simp [v] at hpi ⊢
            linarith
          · have hpi := congr_arg (fun q : Point => q 1) hp
            simp [v] at hpi ⊢
            linarith
    · intro p hp
      have hL'_subset : p + v ∈ Region_Upper := by
        exact hL_subset hp;
      exact ⟨ by have := hL'_subset.1; norm_num [ v ] at this; linarith, by have := hL'_subset.2.1; norm_num [ v ] at this; linarith, by have := hL'_subset.2.2.1; norm_num [ v ] at this; linarith, by have := hL'_subset.2.2.2; norm_num [ v ] at this; linarith ⟩;
  refine ⟨ (fun p => p + v) '' s, ⟨ s, hs.1, rfl ⟩, ?_ ⟩
  rw [Set.not_disjoint_iff_nonempty_inter] at hs ⊢
  obtain ⟨p, hp_s, hp_L'⟩ := hs.2
  exact ⟨p + v, ⟨⟨p, hp_s, rfl⟩, hp_L'⟩⟩

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
    · rcases h with ( ⟨ h₀, h₁, h₂, h₃ ⟩ | ⟨ h₀, h₁, h₂, h₃ ⟩ ) <;> refine ⟨ ⟨ h₀, h₁, by linarith, by linarith ⟩, ?_ ⟩ <;> intro x hx₁ hx₂ hx₃ <;> have := congr_arg (fun p : Point => p 0) hx₃ <;> have := congr_arg (fun p : Point => p 1) hx₃ <;> norm_num at * <;> linarith;
  have h_disjoint : Disjoint Region_R Region_Upper := by
    exact Set.disjoint_left.mpr fun x hx₁ hx₂ => by
      linarith [ hx₁.2.2.2, hx₂.2.2.1 ]
  have h_open : IsOpen Region_R ∧ IsOpen Region_Upper := by
    constructor
    · unfold Region_R
      exact (isOpen_Ioi.preimage (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 0)).inter
        ((isOpen_Iio.preimage (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 0)).inter
          ((isOpen_Ioi.preimage (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 1)).inter
            (isOpen_Iio.preimage (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 1))))
    · unfold Region_Upper
      exact (isOpen_Ioi.preimage (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 0)).inter
        ((isOpen_Iio.preimage (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 0)).inter
          ((isOpen_Ioi.preimage (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 1)).inter
            (isOpen_Iio.preimage (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 1))))
  have hL_sub_union : L ⊆ Region_R ∪ Region_Upper := by
    intro x hx
    have hx_diff : x ∈ Region_Square \ H_mid :=
      ⟨hL_sub hx, fun hx_mid => hL_disj.le_bot ⟨hx, hx_mid⟩⟩
    simpa [h_union] using hx_diff
  exact IsPreconnected.subset_or_subset h_open.1 h_open.2 h_disjoint hL_sub_union
    hL_conn.isPreconnected

/-
The horizontal middle segment is a unit segment.
-/
lemma H_mid_is_unit_segment : IsUnitSegment H_mid := by
  refine ⟨ !₂[0, 0.5], !₂[1, 0.5], ?_, rfl ⟩;
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
          · use fun t => ( 1 - t ) • x + t • y;
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
  have h_unit_segments : IsUnitSegment (openSegment ℝ !₂[0, 0] !₂[0, 1]) ∧ IsUnitSegment (openSegment ℝ !₂[1, 0] !₂[1, 1]) ∧ IsUnitSegment (openSegment ℝ !₂[0, 0] !₂[1, 0]) ∧ IsUnitSegment (openSegment ℝ !₂[0, 1] !₂[1, 1]) := by
    unfold IsUnitSegment;
    norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
    exact ⟨ ⟨ _, _, by norm_num, rfl ⟩, ⟨ _, _, by norm_num, rfl ⟩, ⟨ _, _, by norm_num, rfl ⟩, ⟨ _, _, by norm_num, rfl ⟩ ⟩;
  refine ⟨ h_unit_segments, ?_ ⟩;
  rintro s t ( rfl | rfl | rfl | rfl ) ( rfl | rfl | rfl | rfl ) <;> norm_num [ openSegment_eq_image ];
  all_goals rw [ Set.disjoint_left ] ; norm_num [ Set.mem_image ];
  all_goals
    intro h a x hx₁ hx₂ hx₃ y hy₁ hy₂ hy₃
    have hx0 := congr_arg (fun p : Point => p 0) hx₃
    have hx1 := congr_arg (fun p : Point => p 1) hx₃
    have hy0 := congr_arg (fun p : Point => p 0) hy₃
    have hy1 := congr_arg (fun p : Point => p 1) hy₃
    norm_num at *
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
    have hcoord := congr_arg (fun x : Point => x 1) hst.2
    simpa [hP_bound] using hcoord
  constructor <;> nlinarith

/-
The unit square is a closed set.
-/
lemma UnitSquare_isClosed : IsClosed UnitSquare := by
  -- The unit square is the intersection of four closed half-spaces, which are defined by the inequalities 0 ≤ p 0 ≤ 1 and 0 ≤ p 1 ≤ 1.
  have h_unit_square_closed : IsClosed {p : Point | 0 ≤ p 0 ∧ p 0 ≤ 1} ∧ IsClosed {p : Point | 0 ≤ p 1 ∧ p 1 ≤ 1} := by
    exact ⟨ isClosed_Icc.preimage (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 0), isClosed_Icc.preimage (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 1) ⟩;
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
    simpa [hL] using hP.1) hP.2; aesop;
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
          exact ⟨ (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 1).continuousAt.tendsto.comp h_endpoints.1, (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 1).continuousAt.tendsto.comp h_endpoints.2 ⟩;
        exact ⟨ ⟨ le_of_tendsto_of_tendsto tendsto_const_nhds h_endpoints.1 <| Filter.eventually_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ by norm_num, by norm_num ⟩ ) fun x hx => ( ‹∀ p : Point, ∀ x : ℝ, 0 < x → x < 1 → ( 1 - x ) • A + x • B = p → 0 ≤ p 1 ∧ p 1 ≤ 1› _ _ hx.1 hx.2 rfl ) |>.1, le_of_tendsto_of_tendsto h_endpoints.1 tendsto_const_nhds <| Filter.eventually_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ by norm_num, by norm_num ⟩ ) fun x hx => ( ‹∀ p : Point, ∀ x : ℝ, 0 < x → x < 1 → ( 1 - x ) • A + x • B = p → 0 ≤ p 1 ∧ p 1 ≤ 1› _ _ hx.1 hx.2 rfl ) |>.2 ⟩, ⟨ le_of_tendsto_of_tendsto tendsto_const_nhds h_endpoints.2 <| Filter.eventually_of_mem ( Ioo_mem_nhdsLT_of_mem ⟨ by norm_num, by norm_num ⟩ ) fun x hx => ( ‹∀ p : Point, ∀ x : ℝ, 0 < x → x < 1 → ( 1 - x ) • A + x • B = p → 0 ≤ p 1 ∧ p 1 ≤ 1› _ _ hx.1 hx.2 rfl ) |>.1, le_of_tendsto_of_tendsto h_endpoints.2 tendsto_const_nhds <| Filter.eventually_of_mem ( Ioo_mem_nhdsLT_of_mem ⟨ by norm_num, by norm_num ⟩ ) fun x hx => ( ‹∀ p : Point, ∀ x : ℝ, 0 < x → x < 1 → ( 1 - x ) • A + x • B = p → 0 ≤ p 1 ∧ p 1 ≤ 1› _ _ hx.1 hx.2 rfl ) |>.2 ⟩ ⟩;
      have h_dist : |A 1 - B 1| = 1 := by
        simp_all +decide [ dist_eq_norm, EuclideanSpace.norm_eq ];
        cases hAB.1 <;> cases abs_cases ( A 1 - B 1 ) <;> linarith;
      cases abs_cases ( A 1 - B 1 ) <;> [ right; left ] <;> constructor <;> linarith [ h_endpoints.1.1, h_endpoints.1.2, h_endpoints.2.1, h_endpoints.2.2 ];
    cases' h_endpoints with h h <;> [ exact ⟨ A, B, hL, by tauto ⟩ ; exact ⟨ B, A, by rw [ hL, openSegment_symm ], by tauto ⟩ ];
  -- Since A and B are (0,0) and (0,1), the open segment between them is exactly the vertical line segment from (0,0) to (0,1), which is V_L.
  obtain ⟨A, B, hL, hA, hB, hA1, hB1⟩ := h_endpoints
  have h_open_segment : openSegment ℝ A B = openSegment ℝ !₂[0, 0] !₂[0, 1] := by
    congr <;> ext i <;> fin_cases i <;> aesop;
  rw [hL, h_open_segment]
  rfl

/-
If a unit segment in the unit square is contained in the line x=1, it must be the right vertical side V_R.
-/
lemma unit_segment_on_boundary_x1_eq_V_R (L : Set Point) (hL_unit : IsUnitSegment L) (hL_sub : L ⊆ UnitSquare) (h_subset : L ⊆ {p | p 0 = 1}) : L = V_R := by
  obtain ⟨ p, q, hp, hq, hpq ⟩ := hL_unit;
  -- Since p 0 = 1 and q 0 = 1, we can express p and q as (1, y1) and (1, y2) respectively.
  obtain ⟨y1, y2, hy1, hy2⟩ : ∃ y1 y2 : ℝ, p = !₂[1, y1] ∧ q = !₂[1, y2] := by
    have h_p : p 0 = 1 := by
      have h_p0 : p 0 = 1 := by
        have h_seq : Filter.Tendsto (fun t : ℝ => (1 - t) • p + t • q) (nhdsWithin 0 (Set.Ioi 0)) (nhds p) := by
          exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ ( by norm_num ) )
        exact tendsto_nhds_unique ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 0).continuousAt.tendsto.comp h_seq) ( tendsto_const_nhds.congr' <| Filter.eventuallyEq_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, zero_lt_one ⟩ ) fun t ht => by have := h_subset <| show ( 1 - t ) • p + t • q ∈ openSegment ℝ p q from ⟨ 1 - t, t, by linarith [ ht.1, ht.2 ], by linarith [ ht.1, ht.2 ], by simp +decide ⟩ ; aesop );
      exact h_p0
    have h_q : q 0 = 1 := by
      convert h_subset ( show ( 1 / 2 : ℝ ) • p + ( 1 / 2 : ℝ ) • q ∈ openSegment ℝ p q from ?_ ) using 1
      focus
        norm_num [ h_p ]
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
      have hcont : Continuous fun t : ℝ => (1 - t) • p + t • q := by
        exact ((continuous_const.sub continuous_id).smul continuous_const).add
          (continuous_id.smul continuous_const)
      exact ⟨ tendsto_nhdsWithin_of_tendsto_nhds ( hcont.tendsto' _ _ <| by norm_num ), tendsto_nhdsWithin_of_tendsto_nhds ( hcont.tendsto' _ _ <| by norm_num ) ⟩;
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
        -- Since $p \in L$ and $p \in \text{openSegment} \, \mathbb{R} \, !₂[0, 1] \, !₂[1, 1]$, we have $L \cap \text{openSegment} \, \mathbb{R} \, !₂[0, 1] \, !₂[1, 1] \neq \emptyset$.
        have h_inter : p ∈ L ∧ p ∈ openSegment ℝ !₂[0, 1] !₂[1, 1] := by
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
      exact openSegment_eq O_point (A_seq (n + 1)) (A_seq (m + 1)) hseg
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


end Erdos1071

/-
We have proved the existence of finite maximal disjoint collections of
unit segments in both the open unit square and the closed unit square.

For the open unit square `Region_Square`, we showed that `S_finite`
(consisting of 5 segments) is a maximal disjoint collection.  The
proof involved showing that `S_finite` blocks `Region_Square`. We
decomposed `Region_Square` into `Region12345` and `Region6_Total`,
showed that `S_finite` blocks each (using provided lemmas), and that
the intersection of these regions within `Region_Square` is covered by
`S_finite`.

For the closed unit square `UnitSquare`, we showed that `S_total` (the
union of `S_finite` and the 4 sides `S_sides`) is a maximal disjoint
collection.  The proof relied on the fact that any unit segment in
`UnitSquare` disjoint from `S_sides` must be contained in
`Region_Square` (since it cannot contain corners), and thus is blocked
by `S_finite`.
-/

namespace Erdos1071b

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.cases false
set_option linter.flexible false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option linter.unreachableTactic false

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 50000000
-- Several generated square-boundary blocking arguments time out at the default heartbeat limit.

abbrev Point := EuclideanSpace ℝ (Fin 2)

def IsUnitSegment (s : Set Point) : Prop :=
  ∃ x y : Point, dist x y = 1 ∧ s = openSegment ℝ x y

def IsDisjointCollection (S : Set (Set Point)) : Prop :=
  (∀ s ∈ S, IsUnitSegment s) ∧ (∀ s t, s ∈ S → t ∈ S → s ≠ t → Disjoint s t)

def IsInRegion (S : Set (Set Point)) (R : Set Point) : Prop :=
  ∀ s ∈ S, s ⊆ R

def UnitSquare : Set Point := {p | ∀ i, 0 ≤ p i ∧ p i ≤ 1}

def IsBlocking (S : Set (Set Point)) (R : Set Point) : Prop :=
  ∀ L, IsUnitSegment L → L ⊆ R → ∃ s ∈ S, ¬Disjoint s L

open Set

def V_L : Set Point := openSegment ℝ !₂[0, 0] !₂[0, 1]

def V_R : Set Point := openSegment ℝ !₂[1, 0] !₂[1, 1]

def H_bot : Set Point := openSegment ℝ !₂[0, 0] !₂[1, 0]

def H_top : Set Point := openSegment ℝ !₂[0, 1] !₂[1, 1]

/-
Define the points O(0,0), O'(1,1/2), and A_0(1,0).
-/
def O_point : Point := !₂[0, 0]

def A_0 : Point := !₂[1, 0]

/-
Definitions for Corollary 2: The open unit square, the shifted collection, and the combined collection S_cor2.
-/
def Region_Square : Set Point := {p | 0 < p 0 ∧ p 0 < 1 ∧ 0 < p 1 ∧ p 1 < 1}

/-
Define the set of sides of the unit square and the collection S_cor3.
-/
def S_sides : Set (Set Point) := {V_L, V_R, H_bot, H_top}

/-
Define the boundary of the unit square.
-/
def SquareBoundary : Set Point := {p | p ∈ UnitSquare ∧ (p 0 = 0 ∨ p 0 = 1 ∨ p 1 = 0 ∨ p 1 = 1)}

/-
Define the point V_point (x0, y0) by x0 = (Sqrt[6]+Sqrt[2])/4 and y0 = (Sqrt[6]-Sqrt[2])/4.
-/
noncomputable def V_point : Point := !₂[(Real.sqrt 6 + Real.sqrt 2) / 4, (Real.sqrt 6 - Real.sqrt 2) / 4]

/-
Define the polynomial for x1.
-/
def poly_X (x : ℝ) : ℝ :=
  1 - 64 * x + 1184 * x^2 - 5312 * x^3 + 9536 * x^4 - 8192 * x^5 + 4480 * x^6 + 384 * x^7 -
  6880 * x^8 + 5632 * x^9 - 256 * x^10 - 1024 * x^11 + 4352 * x^12 - 8192 * x^13 +
  6144 * x^14 - 2048 * x^15 + 256 * x^16

/-
There exists a root x1 of poly_X in the interval (0.95, 0.96).
-/
theorem exists_root_x1 : ∃ x, 0.95 < x ∧ x < 0.96 ∧ poly_X x = 0 := by
  -- By the Intermediate Value Theorem, since $f(0.95) > 0$ and $f(0.96) < 0$, there exists some $c \in (0.95, 0.96)$ such that $f(c) = 0$.
  have h_ivt : ∃ c ∈ Set.Ioo (0.95 : ℝ) (0.96 : ℝ), poly_X c = 0 := by
    apply_rules [ intermediate_value_Ioo' ] <;> norm_num [ poly_X ];
    exact Continuous.continuousOn ( by unfold poly_X; continuity );
  aesop

/-
Define x1 as a root of poly_X in (0.95, 0.96).
-/
noncomputable def x1 : ℝ := Classical.choose exists_root_x1

theorem x1_prop : 0.95 < x1 ∧ x1 < 0.96 ∧ poly_X x1 = 0 := Classical.choose_spec exists_root_x1

/-
Define the point X_point (x1, 0).
-/
noncomputable def X_point : Point := !₂[x1, 0]

/-
Define y1 based on V_point and x1.
-/
noncomputable def y1 : ℝ := (V_point 1) * (1 - x1) / (V_point 0 - x1)

/-
Define the point Y_point (1, y1).
-/
noncomputable def Y_point : Point := !₂[1, y1]

/-
Define the x/y reflection called sigma as (x,y) maps to (y,x).
-/
def sigma (p : Point) : Point := !₂[p 1, p 0]

/-
Define the five segments.
-/
def segment1 : Set Point := openSegment ℝ O_point V_point

def segment2 : Set Point := openSegment ℝ O_point (sigma V_point)

def segment3 : Set Point := openSegment ℝ V_point (sigma V_point)

def segment4 : Set Point := openSegment ℝ X_point Y_point

def segment5 : Set Point := openSegment ℝ (sigma X_point) (sigma Y_point)

/-
Define the finite collection S_finite consisting of the five segments.
-/
def S_finite : Set (Set Point) := {segment1, segment2, segment3, segment4, segment5}

/-
V_point lies on segment4.
-/
theorem V_on_segment4 : V_point ∈ segment4 := by
  rw [segment4, openSegment_eq_image]
  let vx : ℝ := V_point 0
  let t : ℝ := (vx - x1) / (1 - x1)
  have hx1_lt_one : x1 < 1 := by
    have hx := x1_prop
    linarith [hx.2.1]
  have hden : 1 - x1 ≠ 0 := by
    linarith
  have hsqrt6_low : (61 / 25 : ℝ) < Real.sqrt 6 :=
    Real.lt_sqrt_of_sq_lt (by norm_num)
  have hsqrt2_low : (7 / 5 : ℝ) < Real.sqrt 2 :=
    Real.lt_sqrt_of_sq_lt (by norm_num)
  have hsqrt6_high : Real.sqrt 6 < (5 / 2 : ℝ) :=
    (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 5 / 2)).2 (by norm_num)
  have hsqrt2_high : Real.sqrt 2 < (3 / 2 : ℝ) :=
    (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 3 / 2)).2 (by norm_num)
  have hx1_lt_vx : x1 < vx := by
    have hx := x1_prop
    unfold vx V_point
    norm_num
    linarith [hx.2.1, hsqrt6_low, hsqrt2_low]
  have hvx_lt_one : vx < 1 := by
    unfold vx V_point
    norm_num
    linarith [hsqrt6_high, hsqrt2_high]
  refine ⟨t, ⟨?_, ?_⟩, ?_⟩
  · exact div_pos (sub_pos.mpr hx1_lt_vx) (sub_pos.mpr hx1_lt_one)
  · rw [div_lt_one (sub_pos.mpr hx1_lt_one)]
    linarith [hvx_lt_one]
  · ext i <;> fin_cases i
    · simp [t, vx, X_point, Y_point]
      field_simp [hden]
      ring
    · have hvx_ne_x1 : vx - x1 ≠ 0 := by
        linarith [hx1_lt_vx]
      have hVx_ne_x1 : V_point 0 - x1 ≠ 0 := by
        simpa [vx] using hvx_ne_x1
      simp [t, vx, X_point, Y_point, y1]
      field_simp [hden, hVx_ne_x1]

/-
sigma(V_point) lies on segment5.
-/
theorem sigma_V_on_segment5 : sigma V_point ∈ segment5 := by
  convert Set.mem_image_of_mem sigma ( V_on_segment4 ) using 1;
  ext; simp
  constructor;
  · rintro ⟨ a, ha, b, hb, hab, rfl ⟩;
    refine ⟨ a • X_point + ha • Y_point, ⟨ a, ha, b, hb, hab, rfl ⟩, ?_ ⟩;
    ext i ; fin_cases i <;> norm_num [ sigma ];
  · rintro ⟨ x, ⟨ a, ha, b, hb, hab, rfl ⟩, rfl ⟩;
    exact ⟨ a, ha, b, hb, hab, by ext i; fin_cases i <;> norm_num [ sigma ] ⟩

/-
The distance between any two points in a triangle is at most the maximum length of its sides.
-/
theorem dist_le_max_vertices (A B C : Point) (x y : Point)
  (hx : x ∈ convexHull ℝ {A, B, C}) (hy : y ∈ convexHull ℝ {A, B, C}) :
  dist x y ≤ max (dist A B) (max (dist B C) (dist C A)) := by
  have hxy :
      dist x y ≤ Metric.diam (convexHull ℝ ({A, B, C} : Set Point)) :=
    Metric.dist_le_diam_of_mem (by simp) hx hy
  simpa [convexHull_diam, Metric.diam_triple, dist_comm, max_assoc, max_left_comm, max_comm]
    using hxy

/-
If a point x in a triangle is at distance 1 from a vertex V, and all sides connected to V are length <= 1, then x must be a vertex.
-/
theorem dist_eq_one_implies_vertex (A B C : Point) (V : Point) (hV : V ∈ ({A, B, C} : Set Point))
    (hAB : dist A B ≤ 1) (hBC : dist B C ≤ 1) (hCA : dist C A ≤ 1)
    (x : Point) (hx : x ∈ convexHull ℝ {A, B, C}) (hdist : dist x V = 1) :
    x ∈ ({A, B, C} : Set Point) := by
      -- By the distances, $convexHull {A, B, C} \subseteq B(V, 1)$.
      have h_convexHull_ball : convexHull ℝ {A, B, C} ⊆ Metric.closedBall V (1 : ℝ) := by
        refine convexHull_min ?_ ?_;
        · simp_all +decide [ Set.insert_subset_iff, dist_comm ];
          rcases hV with ( rfl | rfl | rfl ) <;> simp_all +decide [ dist_comm ];
        · exact convex_closedBall _ _;
      -- By the distances, $convexHull {A, B, C}$ is a subset of $B(V, 1)$, and since $x$ is on the boundary of $B(V, 1)$, $x$ must be an extreme point of $convexHull {A, B, C}$.
      have h_extreme : x ∈ Set.extremePoints ℝ (convexHull ℝ {A, B, C}) := by
        refine ⟨ hx, ?_ ⟩;
        intro y hy z hz hxy
        have hxy_ball : y ∈ Metric.closedBall V (1 : ℝ) ∧ z ∈ Metric.closedBall V (1 : ℝ) := by
          exact ⟨ h_convexHull_ball hy, h_convexHull_ball hz ⟩;
        have h_eq : ‖y - V‖ = 1 ∧ ‖z - V‖ = 1 := by
          obtain ⟨ a, b, ha, hb, hab, rfl ⟩ := hxy;
          have h_eq : ‖a • (y - V) + b • (z - V)‖ = 1 := by
            convert hdist using 1;
            rw [ dist_eq_norm ] ; rw [ ← eq_sub_iff_add_eq' ] at hab ; subst_vars ; ring_nf;
            exact congr_arg Norm.norm ( by ext ; simpa using by ring );
          have h_eq : ‖a • (y - V) + b • (z - V)‖ ≤ a * ‖y - V‖ + b * ‖z - V‖ := by
            exact norm_add_le_of_le ( by rw [ norm_smul, Real.norm_of_nonneg ha.le ] ) ( by rw [ norm_smul, Real.norm_of_nonneg hb.le ] );
          constructor <;> nlinarith [
            show ‖y - V‖ ≤ 1 from by
              simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hxy_ball.1,
            show ‖z - V‖ ≤ 1 from by
              simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hxy_ball.2]
        obtain ⟨ a, b, ha, hb, hab, rfl ⟩ := hxy;
        have h_eq : ‖a • (y - V) + b • (z - V)‖ = 1 := by
          convert hdist using 1;
          rw [ dist_eq_norm ] ; rw [ show a • y + b • z = a • ( y - V ) + b • ( z - V ) + V by ext i; simpa using by rw [ ← eq_sub_iff_add_eq' ] at hab; rw [ hab ] ; ring ] ; simp +decide
        have h_eq : ‖a • (y - V) + b • (z - V)‖^2 = ‖a • (y - V)‖^2 + ‖b • (z - V)‖^2 + 2 * a * b * inner ℝ (y - V) (z - V) := by
          rw [ @norm_add_sq ℝ ];
          simp +decide [ inner_smul_left, inner_smul_right, mul_assoc, mul_comm, mul_left_comm ] ; ring;
        simp_all +decide [ norm_smul ];
        have h_eq : inner ℝ (y - V) (z - V) = 1 := by
          nlinarith [ mul_pos ha hb ];
        have h_eq : ‖(y - V) - (z - V)‖^2 = 0 := by
          rw [ @norm_sub_sq ℝ ] ; norm_num [ h_eq ];
          nlinarith;
        norm_num [ ← ‹1 = a ^ 2 + b ^ 2 + 2 * a * b * inner ℝ ( y - V ) ( z - V ) › ] at *;
        norm_num [ sub_eq_zero.mp h_eq ] at *;
        rw [ ← add_smul, hab, one_smul ];
      -- By the distances, $convexHull {A, B, C}$ is a subset of $B(V, 1)$, and since $x$ is on the boundary of $B(V, 1)$, $x$ must be an extreme point of $convexHull {A, B, C}$, which means $x$ must be one of $A$, $B$, or $C$.
      have h_extreme_points : Set.extremePoints ℝ (convexHull ℝ {A, B, C}) ⊆ {A, B, C} := by
        exact extremePoints_convexHull_subset;
      exact h_extreme_points h_extreme

/-
If two points in a triangle with sides <= 1 are at distance 1, they must be vertices.
-/
theorem unit_segment_endpoints_are_vertices (A B C : Point)
    (hAB : dist A B ≤ 1) (hBC : dist B C ≤ 1) (hCA : dist C A ≤ 1)
    (x y : Point) (hx : x ∈ convexHull ℝ {A, B, C}) (hy : y ∈ convexHull ℝ {A, B, C})
    (hdist : dist x y = 1) :
    x ∈ ({A, B, C} : Set Point) ∧ y ∈ ({A, B, C} : Set Point) := by
  rcases convexHull_exists_dist_ge hx y with ⟨V, hV, hVdist⟩
  have hVdist_ge : 1 ≤ dist V y := by
    simpa [hdist] using hVdist
  have hV_hull : V ∈ convexHull ℝ ({A, B, C} : Set Point) :=
    subset_convexHull ℝ _ hV
  have hVdist_le_max : dist V y ≤ max (dist A B) (max (dist B C) (dist C A)) :=
    dist_le_max_vertices A B C V y hV_hull hy
  have hVdist_le : dist V y ≤ 1 :=
    hVdist_le_max.trans (max_le hAB (max_le hBC hCA))
  have hVdist_eq : dist V y = 1 := le_antisymm hVdist_le hVdist_ge
  have hy_vertex : y ∈ ({A, B, C} : Set Point) :=
    dist_eq_one_implies_vertex A B C V hV hAB hBC hCA y hy (by
      simpa [dist_comm] using hVdist_eq)
  have hx_vertex : x ∈ ({A, B, C} : Set Point) :=
    dist_eq_one_implies_vertex A B C y hy_vertex hAB hBC hCA x hx hdist
  exact ⟨hx_vertex, hy_vertex⟩

/-
Triangle diameter lemma: if a triangle's sides are all at most unit length, then the only unit line segments in that closed triangle are possibly the sides.
-/
theorem triangle_diameter_lemma (A B C : Point) (hAB : dist A B ≤ 1) (hBC : dist B C ≤ 1) (hCA : dist C A ≤ 1)
    (S : Set Point) (hS : IsUnitSegment S) (hS_sub : S ⊆ convexHull ℝ {A, B, C}) :
    S = openSegment ℝ A B ∨ S = openSegment ℝ B C ∨ S = openSegment ℝ C A := by
  obtain ⟨x, y, hxy, hS_eq⟩ := hS
  have h_open_sub : openSegment ℝ x y ⊆ convexHull ℝ {A, B, C} := by
    simpa [hS_eq] using hS_sub
  have h_closed_hull : IsClosed (convexHull ℝ ({A, B, C} : Set Point)) := by
    have h_finite : Set.Finite ({A, B, C} : Set Point) := by
      simp
    exact (h_finite.isCompact_convexHull ℝ).isClosed
  have h_closure_sub : closure (openSegment ℝ x y) ⊆ convexHull ℝ {A, B, C} :=
    h_closed_hull.closure_subset_iff.mpr h_open_sub
  have hx : x ∈ convexHull ℝ {A, B, C} := by
    apply h_closure_sub
    simpa [closure_openSegment] using (left_mem_segment ℝ x y)
  have hy : y ∈ convexHull ℝ {A, B, C} := by
    apply h_closure_sub
    simpa [closure_openSegment] using (right_mem_segment ℝ x y)
  have h_vertices : x ∈ ({A, B, C} : Set Point) ∧ y ∈ ({A, B, C} : Set Point) :=
    unit_segment_endpoints_are_vertices A B C hAB hBC hCA x y hx hy hxy
  rcases h_vertices with ⟨rfl | rfl | rfl, rfl | rfl | rfl⟩
  · simp at hxy
  · exact Or.inl hS_eq
  · exact Or.inr <| Or.inr <| by
      rw [hS_eq, openSegment_symm]
  · exact Or.inl <| by
      rw [hS_eq, openSegment_symm]
  · simp at hxy
  · exact Or.inr <| Or.inl hS_eq
  · exact Or.inr <| Or.inr hS_eq
  · exact Or.inr <| Or.inl <| by
      rw [hS_eq, openSegment_symm]
  · simp at hxy

/-
The distance from O to V is 1.
-/
theorem dist_O_V : dist O_point V_point = 1 := by
  norm_num [ EuclideanSpace.dist_eq, V_point ];
  norm_num [ dist_eq_norm, O_point ] ; ring_nf ; norm_num;
  ring_nf; norm_num;

/-
The distance between V and sigma(V) is 1.
-/
theorem dist_V_sigma_V : dist V_point (sigma V_point) = 1 := by
  unfold sigma V_point;
  norm_num [ EuclideanSpace.norm_eq, dist_eq_norm ] ; ring_nf ; norm_num

/-
The distance condition is equivalent to an algebraic equation involving x1 and V_point 0.
-/
lemma dist_X_Y_iff_Q : dist X_point Y_point = 1 ↔ (1 - x1)^2 * (1 - 2 * V_point 0 * x1 + x1^2) = (V_point 0 - x1)^2 := by
  norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
  -- Substitute the definitions of X_point and Y_point into the distance formula.
  simp [X_point, Y_point, V_point];
  unfold y1;
  field_simp;
  rw [ add_div', div_eq_iff ] <;> norm_num [ V_point ];
  · grind;
  · have := x1_prop;
    nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ];
  · have := x1_prop;
    nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ]

/-
The x-coordinate of V_point.
-/
lemma V_point_0_val : V_point 0 = (Real.sqrt 6 + Real.sqrt 2) / 4 := by
  rfl

/-
Define the parametric polynomial Q and the semi-product.
-/
noncomputable def poly_Q_param (c : ℝ) (x : ℝ) : ℝ :=
  (1 - c^2) - 2 * x + (1 + 4 * c) * x^2 - (2 + 2 * c) * x^3 + x^4

noncomputable def poly_Q_pos (x : ℝ) : ℝ := poly_Q_param (V_point 0) x

noncomputable def poly_Q_neg (x : ℝ) : ℝ := poly_Q_param (-(V_point 0)) x

noncomputable def poly_semi (x : ℝ) : ℝ := poly_Q_pos x * poly_Q_neg x

/-
Define the full product polynomial.
-/
noncomputable def poly_Q_pos_prime (x : ℝ) : ℝ := poly_Q_param (V_point 1) x

noncomputable def poly_Q_neg_prime (x : ℝ) : ℝ := poly_Q_param (-(V_point 1)) x

noncomputable def poly_semi_prime (x : ℝ) : ℝ := poly_Q_pos_prime x * poly_Q_neg_prime x

noncomputable def poly_full (x : ℝ) : ℝ := poly_semi x * poly_semi_prime x

/-
poly_X is 256 times poly_full.
-/
lemma poly_X_eq_256_mul_poly_full : ∀ x, poly_X x = 256 * poly_full x := by
  unfold poly_X poly_full poly_semi poly_semi_prime poly_Q_pos poly_Q_neg poly_Q_pos_prime poly_Q_neg_prime poly_Q_param;
  -- By definition of $V_point$, we know that $V_point 0 = (Real.sqrt 6 + Real.sqrt 2) / 4$ and $V_point 1 = (Real.sqrt 6 - Real.sqrt 2) / 4$.
  have hV_point : V_point 0 = (Real.sqrt 6 + Real.sqrt 2) / 4 ∧ V_point 1 = (Real.sqrt 6 - Real.sqrt 2) / 4 := by
    exact ⟨ rfl, rfl ⟩;
  grind

/-
The distance condition is equivalent to poly_Q_pos x1 = 0.
-/
lemma dist_eq_one_iff_poly_Q_pos_eq_zero : dist X_point Y_point = 1 ↔ poly_Q_pos x1 = 0 := by
  convert dist_X_Y_iff_Q using 1;
  unfold poly_Q_pos;
  unfold poly_Q_param; ring_nf;
  constructor <;> intro h <;> linear_combination h

/-
The other factors of poly_full are negative in the interval [0.95, 0.96].
-/
lemma other_factors_neg (x : ℝ) (hx : 0.95 ≤ x ∧ x ≤ 0.96) :
  poly_Q_neg x < 0 ∧ poly_Q_pos_prime x < 0 ∧ poly_Q_neg_prime x < 0 := by
    -- Calculate the approximations for V_point 0 and V_point 1.
    have h_approx : (V_point 0) > 0.9659 ∧ (V_point 0) < 0.9661 ∧ (V_point 1) > 0.2588 ∧ (V_point 1) < 0.2589 := by
      unfold V_point; norm_num [ ← List.ofFn_inj ] ; ring_nf;
      exact ⟨ by nlinarith only [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ], by nlinarith only [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ], by nlinarith only [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ], by nlinarith only [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ] ⟩;
    unfold poly_Q_neg poly_Q_pos_prime poly_Q_neg_prime;
    unfold poly_Q_param;
    exact ⟨ by nlinarith [ pow_nonneg ( sub_nonneg.2 hx.1 ) 3 ], by nlinarith [ pow_nonneg ( sub_nonneg.2 hx.1 ) 3 ], by nlinarith [ pow_nonneg ( sub_nonneg.2 hx.1 ) 3 ] ⟩

/-
The distance between X and Y is 1.
-/
theorem dist_X_Y : dist X_point Y_point = 1 := by
  convert dist_eq_one_iff_poly_Q_pos_eq_zero.mpr _;
  have h_poly_Q_pos_zero : poly_X x1 = 256 * poly_Q_pos x1 * poly_Q_neg x1 * poly_Q_pos_prime x1 * poly_Q_neg_prime x1 := by
    convert poly_X_eq_256_mul_poly_full x1 using 1 ; ring_nf;
    unfold poly_full poly_semi poly_semi_prime; ring;
  have h_poly_Q_pos_zero : poly_Q_pos x1 * poly_Q_neg x1 * poly_Q_pos_prime x1 * poly_Q_neg_prime x1 = 0 := by
    linarith [ x1_prop.2.2 ];
  have h_poly_Q_pos_zero : poly_Q_neg x1 < 0 ∧ poly_Q_pos_prime x1 < 0 ∧ poly_Q_neg_prime x1 < 0 := by
    exact other_factors_neg x1 ⟨ by exact le_of_lt ( x1_prop.1 ), by exact le_of_lt ( x1_prop.2.1 ) ⟩;
  aesop

/-
Define the regions that subdivide the square.
-/
def Region1 : Set Point := convexHull ℝ {O_point, V_point, sigma V_point}

def Region2 : Set Point := convexHull ℝ {O_point, V_point, X_point}

def Region3 : Set Point := convexHull ℝ {O_point, sigma V_point, sigma X_point}

def Region4 : Set Point := convexHull ℝ {X_point, A_0, Y_point}

def Region5 : Set Point := convexHull ℝ {sigma X_point, sigma A_0, sigma Y_point}

def Region6a : Set Point := convexHull ℝ {V_point, sigma V_point, Y_point}

def Region6b : Set Point := convexHull ℝ {sigma V_point, Y_point, sigma Y_point}

/-
If a point is in an open segment (endpoints distinct), its distance to an endpoint is strictly less than the segment length.
-/
lemma mem_openSegment_implies_dist_lt {A B P : Point} (hAB : A ≠ B) (h : P ∈ openSegment ℝ A B) : dist A P < dist A B := by
  rcases h with ⟨ u, v, hu, hv, huv, rfl ⟩;
  rw [ show v = 1 - u by linarith ];
  rw [ dist_eq_norm, dist_eq_norm ];
  rw [ show A - ( u • A + ( 1 - u ) • B ) = ( 1 - u ) • ( A - B ) by ext ; simpa using by ring ] ; rw [ norm_smul, Real.norm_of_nonneg ( by linarith ) ] ; exact mul_lt_of_lt_one_left ( norm_pos_iff.mpr <| sub_ne_zero.mpr hAB ) <| by linarith;

/-
sigma is an isometry.
-/
theorem sigma_isometry (p q : Point) : dist (sigma p) (sigma q) = dist p q := by
  simp +decide [ dist_eq_norm, EuclideanSpace.norm_eq ];
  exact congrArg Real.sqrt ( by ring! )

/-
The distance from O to sigma(V) is 1.
-/
theorem dist_O_sigma_V : dist O_point (sigma V_point) = 1 := by
  have h := (sigma_isometry O_point V_point).trans dist_O_V
  simpa [O_point, sigma] using h

/-
The distance from O to X is less than 1.
-/
theorem dist_O_X_lt_1 : dist O_point X_point < 1 := by
  unfold O_point X_point;
  norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
  rw [ Real.sqrt_sq ] <;> have := x1_prop <;> norm_num at this ⊢ <;> nlinarith

/-
The distance from V to X is less than 1.
-/
theorem dist_V_X_lt_1 : dist V_point X_point < 1 := by
  have hXY : X_point ≠ Y_point := by
    intro h
    have hx : x1 = 1 := by
      have := congrArg (fun p : Point => p 0) h
      simpa [X_point, Y_point] using this
    linarith [x1_prop.2.1]
  have h_dist_X_V_lt_dist_X_Y : dist X_point V_point < dist X_point Y_point :=
    mem_openSegment_implies_dist_lt hXY (by simpa [segment4] using V_on_segment4)
  simpa [dist_comm, dist_X_Y] using h_dist_X_V_lt_dist_X_Y

/-
The distance from X to A0 is less than 1.
-/
theorem dist_X_A0_lt_1 : dist X_point A_0 < 1 := by
  norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
  unfold X_point A_0 ; norm_num [ X_point, A_0 ];
  rw [ Real.sqrt_sq_eq_abs, abs_lt ] ; constructor <;> nlinarith [ x1_prop ]

/-
The distance from A0 to Y is less than 1.
-/
theorem dist_A0_Y_lt_1 : dist A_0 Y_point < 1 := by
  -- By definition of Y_point, we have Y_point = !₂[1, y1].
  have hY : dist A_0 Y_point = Real.sqrt (y1^2) := by
    norm_num [ dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two ];
    unfold A_0 Y_point; norm_num;
  -- From the equation above, y1^2 = 1 - (1 - x1)^2.
  have hy1_sq : y1^2 = 1 - (1 - x1)^2 := by
    -- By definition of Y_point, we have Y_point = !₂[1, y1]. We know dist(X, Y) = 1.
    have h_dist_X_Y : dist X_point Y_point = 1 := by
      exact dist_X_Y;
    norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] at *;
    unfold X_point Y_point at * ; norm_num at * ; linarith!;
  rw [ hY, Real.sqrt_lt' ] <;> nlinarith [ show 0 < 1 - x1 by nlinarith [ x1_prop ] ]

/-
The distance from V to Y is less than 1.
-/
theorem dist_V_Y_lt_1 : dist V_point Y_point < 1 := by
  have hVYX : V_point ∈ openSegment ℝ Y_point X_point := by
    simpa [segment4, openSegment_symm ℝ Y_point X_point] using V_on_segment4
  have hYX : Y_point ≠ X_point := by
    intro h
    have hdist : dist X_point Y_point = 0 := by simpa [h]
    linarith [dist_X_Y, hdist]
  have hlt := mem_openSegment_implies_dist_lt (A := Y_point) (B := X_point)
    (P := V_point) hYX hVYX
  simpa [dist_comm, dist_X_Y] using hlt

/-
The distance between sigma(X) and sigma(Y) is 1.
-/
theorem dist_sigma_X_sigma_Y : dist (sigma X_point) (sigma Y_point) = 1 := by
  rw [sigma_isometry, dist_X_Y]

/-
Numeric bounds for V_point.
-/
lemma V_bounds : 0.96 < V_point 0 ∧ V_point 0 < 0.97 ∧ 0.25 < V_point 1 ∧ V_point 1 < 0.26 := by
  unfold V_point; norm_num [ ← List.ofFn_inj ] ; ring_nf;
  exact ⟨ by nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ], by nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ], by nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ], by nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ] ⟩

/-
Every segment in S_finite is a unit segment.
-/
theorem S_finite_consists_of_unit_segments : ∀ s ∈ S_finite, IsUnitSegment s := by
  unfold S_finite;
  simp +zetaDelta at *;
  refine ⟨ ?_, ?_, ?_, ?_, ?_ ⟩;
  · exact ⟨ O_point, V_point, dist_O_V, rfl ⟩;
  · exact ⟨ O_point, sigma V_point, by simpa using dist_O_sigma_V, rfl ⟩;
  · use V_point, sigma V_point;
    exact ⟨ dist_V_sigma_V, rfl ⟩;
  · exact ⟨ X_point, Y_point, dist_X_Y, rfl ⟩;
  · exact ⟨ _, _, dist_sigma_X_sigma_Y, rfl ⟩

/-
V_point is in the open unit square.
-/
lemma V_in_Region_Square : V_point ∈ Region_Square := by
  exact ⟨ by linarith [ V_bounds ], by linarith [ V_bounds ], by linarith [ V_bounds ], by linarith [ V_bounds ] ⟩

/-
sigma(V_point) is in the open unit square.
-/
lemma sigma_V_in_Region_Square : sigma V_point ∈ Region_Square := by
  exact ⟨ by have := V_bounds; norm_num [ sigma ] at *; linarith, by have := V_bounds; norm_num [ sigma ] at *; linarith, by have := V_bounds; norm_num [ sigma ] at *; linarith, by have := V_bounds; norm_num [ sigma ] at *; linarith ⟩

/-
The open segment from O to a point inside the square is inside the square.
-/
lemma segment_from_corner_in_square (v : Point) (hv : v ∈ Region_Square) : openSegment ℝ O_point v ⊆ Region_Square := by
  intro p hp;
  obtain ⟨ a, b, ha, hb, hab, rfl ⟩ := hp;
  exact ⟨ by simpa [ show O_point = 0 from by ext i; fin_cases i <;> rfl ] using by nlinarith [ hv.1, hv.2.1 ], by simpa [ show O_point = 0 from by ext i; fin_cases i <;> rfl ] using by nlinarith [ hv.1, hv.2.1 ], by simpa [ show O_point = 0 from by ext i; fin_cases i <;> rfl ] using by nlinarith [ hv.2.2.1, hv.2.2.2 ], by simpa [ show O_point = 0 from by ext i; fin_cases i <;> rfl ] using by nlinarith [ hv.2.2.1, hv.2.2.2 ] ⟩

/-
The open segment between two points in the square is in the square.
-/
lemma segment_inside_square (u v : Point) (hu : u ∈ Region_Square) (hv : v ∈ Region_Square) : openSegment ℝ u v ⊆ Region_Square := by
  -- Since $u$ and $v$ are in $Region_Square$, we have $0 < u 0 < 1$, $0 < u 1 < 1$, $0 < v 0 < 1$, and $0 < v 1 < 1$.
  have h_bounds : 0 < u 0 ∧ u 0 < 1 ∧ 0 < u 1 ∧ u 1 < 1 ∧ 0 < v 0 ∧ v 0 < 1 ∧ 0 < v 1 ∧ v 1 < 1 := by
    exact ⟨ hu.1, hu.2.1, hu.2.2.1, hu.2.2.2, hv.1, hv.2.1, hv.2.2.1, hv.2.2.2 ⟩;
  rintro w ⟨ a, b, ha, hb, hab, rfl ⟩;
  exact ⟨ by simpa using by nlinarith, by simpa using by nlinarith, by simpa using by nlinarith, by simpa using by nlinarith ⟩

/-
y1 is strictly between 0 and 1.
-/
lemma y1_bounds : 0 < y1 ∧ y1 < 1 := by
  -- Since $V_point 1 = \frac{\sqrt{6} - \sqrt{2}}{4}$ and $x1$ is between $0.95$ and $0.96$, we can show that $y1$ is positive and less than 1.
  have hy1_pos : 0 < y1 := by
    apply_rules [ mul_pos, div_pos ] <;> norm_num [ V_point_0_val, V_point ];
    · exact lt_of_lt_of_le ( Classical.choose_spec exists_root_x1 |>.2.1 ) ( by norm_num );
    · have := x1_prop;
      nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ]
  have hy1_lt_1 : y1 < 1 := by
    -- By definition of $y1$, we have $y1^2 = 1 - (1 - x1)^2$.
    have hy1_sq : y1^2 = 1 - (1 - x1)^2 := by
      have := dist_X_Y;
      norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] at this;
      unfold X_point Y_point at this; norm_num at this; linarith;
    nlinarith [ show x1 < 1 by exact lt_of_lt_of_le ( Classical.choose_spec exists_root_x1 |>.2.1 ) ( by norm_num ) ]
  exact ⟨hy1_pos, hy1_lt_1⟩

/-
segment4 is contained in the open unit square.
-/
lemma segment4_in_square : segment4 ⊆ Region_Square := by
  -- By definition of open segment, any point p in segment4 can be written as p = (1-t)X_point + tY_point for some t in (0,1).
  intro p hp
  obtain ⟨t, ht⟩ : ∃ t ∈ Set.Ioo (0 : ℝ) 1, p = (1 - t) • X_point + t • Y_point := by
    rcases hp with ⟨ a, b, ha, hb, hab, rfl ⟩ ; exact ⟨ b, ⟨ by linarith, by linarith ⟩, by simp +decide [ ← eq_sub_iff_add_eq' ] at *; aesop ⟩ ;
  -- Substitute the coordinates of X_point and Y_point into the expression for p.
  have hp_coords : p 0 = (1 - t) * x1 + t ∧ p 1 = t * y1 := by
    simp [ht, X_point, Y_point];
  -- Since $0 < x1 < 1$ and $0 < y1 < 1$, we have $0 < (1 - t) * x1 + t < 1$ and $0 < t * y1 < 1$.
  have hx1_bounds : 0 < x1 ∧ x1 < 1 := by
    exact ⟨ lt_trans ( by norm_num ) ( x1_prop.1 ), lt_trans ( x1_prop.2.1 ) ( by norm_num ) ⟩
  have hy1_bounds : 0 < y1 ∧ y1 < 1 := by
    exact y1_bounds;
  exact ⟨ by nlinarith [ ht.1.1, ht.1.2 ], by nlinarith [ ht.1.1, ht.1.2 ], by nlinarith [ ht.1.1, ht.1.2 ], by nlinarith [ ht.1.1, ht.1.2 ] ⟩

/-
segment5 is contained in the open unit square.
-/
lemma segment5_in_square : segment5 ⊆ Region_Square := by
  -- Since segment4 is contained in Region_Square, and sigma is an isometry, segment5 is also contained in Region_Square.
  have h_segment5_in_square : segment4 ⊆ Region_Square := by
    exact segment4_in_square;
  have h_segment5_in_square : segment5 = (fun p => sigma p) '' segment4 := by
    ext; simp [openSegment];
    constructor;
    · rintro ⟨ a, ha, b, hb, hab, rfl ⟩;
      refine ⟨ a • X_point + ha • Y_point, ⟨ a, ha, b, hb, hab, rfl ⟩, ?_ ⟩;
      ext i; fin_cases i <;> norm_num [ sigma ] ;
    · rintro ⟨ x, ⟨ a, ha, b, hb, hab, rfl ⟩, rfl ⟩;
      exact ⟨ a, ha, b, hb, hab, by ext i; fin_cases i <;> norm_num [ sigma ] ⟩;
  simp_all +decide [ Set.subset_def ];
  intro p hp; specialize ‹∀ x ∈ segment4, x ∈ Region_Square› p hp; unfold Region_Square at *; aesop;

/-
All segments in S_finite are contained in the open unit square.
-/
theorem S_finite_in_region : IsInRegion S_finite Region_Square := by
  exact fun s hs => by rcases hs with ( rfl | rfl | rfl | rfl | rfl ) <;> [ exact segment_from_corner_in_square _ ( by exact
    V_in_Region_Square ) ; exact segment_from_corner_in_square _ ( by exact
    sigma_V_in_Region_Square ) ; exact segment_inside_square _ _ ( by exact
    V_in_Region_Square ) ( by exact
    sigma_V_in_Region_Square ) ; exact segment4_in_square ; exact segment5_in_square ] ;

/-
segment1 and segment5 are disjoint.
-/
lemma disjoint_1_5 : Disjoint segment1 segment5 := by
  refine Set.disjoint_left.mpr ?_;
  intro p hp hp'; obtain ⟨ u, v, hu, hv, huv, rfl ⟩ := hp; obtain ⟨ w, z, hw, hz, hwz, hp' ⟩ := hp';
  unfold sigma at hp';
  unfold X_point Y_point at * ; norm_num at *;
  have h_y : w * x1 + z = u * 0 + v * V_point 1 := by
    have hcoord := congrArg (fun q : Point => q 1) hp'
    norm_num [O_point, V_point, hwz] at hcoord ⊢
    exact hcoord
  have h_y_contra : w * x1 + z > w * 0.95 + z := by
    have hmul : w * 0.95 < w * x1 := mul_lt_mul_of_pos_left x1_prop.1 hw
    nlinarith
  have h_y_large : w * x1 + z > 0.95 := by
    nlinarith
  have h_y_small : u * 0 + v * V_point 1 < 0.26 := by
    have hV := V_bounds
    nlinarith
  nlinarith

/-
segment2 and segment4 are disjoint.
-/
lemma disjoint_2_4 : Disjoint segment2 segment4 := by
  refine Set.disjoint_left.mpr ?_
  intro x hx hx'
  rw [segment2] at hx
  rw [segment4] at hx'
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hx
  obtain ⟨c, d, hc, hd, hcd, hcd'⟩ := hx'
  have hcoord : c * x1 + d * 1 = a * 0 + b * (V_point 1) := by
    have hcoord' := congrArg (fun q : Point => q 0) hcd'
    norm_num [X_point, Y_point, O_point, sigma, V_point] at hcoord' ⊢
    exact hcoord'
  have hleft : 0.95 < c * x1 + d * 1 := by
    nlinarith [x1_prop.1, hc, hd, hcd]
  have hb_lt_one : b < 1 := by
    nlinarith [ha, hb, hab]
  have hVpos : 0 < V_point 1 := by
    nlinarith [V_bounds.2.2.1]
  have hright : a * 0 + b * (V_point 1) < 0.26 := by
    have hbV : b * (V_point 1) < 1 * 0.26 := by
      exact mul_lt_mul hb_lt_one (le_of_lt V_bounds.2.2.2) hVpos (by norm_num)
    nlinarith
  nlinarith

/-
segment4 and segment5 are disjoint.
-/
lemma disjoint_4_5 : Disjoint segment4 segment5 := by
  rw [segment4, segment5, openSegment_eq_image, openSegment_eq_image]
  refine Set.disjoint_left.mpr ?_
  rintro p ⟨u, hu, rfl⟩ ⟨w, hw, hp⟩
  have h0 := congrArg (fun q : Point => q 0) hp
  have h1 := congrArg (fun q : Point => q 1) hp
  norm_num [X_point, Y_point, sigma] at h0 h1
  have hx1_pos : 0 < x1 := by
    have hx := x1_prop
    linarith
  have hy1_lt_one : y1 < 1 := y1_bounds.2
  have hw_lt_u : w < u := by
    have hw_lt_uy : w < u * y1 := by nlinarith [h1, hw.2, hx1_pos]
    nlinarith [hw_lt_uy, hu.1, hy1_lt_one]
  have hleft_lt_u : (1 - u) * x1 + u < u := by
    have hwy_lt_w : w * y1 < w := by nlinarith [hw.1, hy1_lt_one]
    nlinarith [h0, hwy_lt_w, hw_lt_u]
  nlinarith [hleft_lt_u, hu.2, hx1_pos]

/-
segment1 and segment4 are disjoint.
-/
lemma disjoint_1_4 : Disjoint segment1 segment4 := by
  refine Set.disjoint_left.mpr ?_;
  intro x hx1 hx4;
  -- Since $x$ is in both $segment1$ and $segment4$, it must lie on the line segment $OV$ and also on the line segment $XY$.
  obtain ⟨t, ht⟩ : ∃ t ∈ Set.Ioo (0 : ℝ) 1, x = t • O_point + (1 - t) • V_point := by
    rw [ segment1 ] at hx1;
    rw [ openSegment_eq_image ] at hx1;
    rcases hx1 with ⟨ t, ht, rfl ⟩ ; exact ⟨ 1 - t, ⟨ by linarith [ ht.1, ht.2 ], by linarith [ ht.1, ht.2 ] ⟩, by ext i; fin_cases i <;> norm_num ⟩ ;
  obtain ⟨s, hs⟩ : ∃ s ∈ Set.Ioo (0 : ℝ) 1, x = s • X_point + (1 - s) • Y_point := by
    rw [ segment4 ] at hx4;
    rw [ openSegment_eq_image ] at hx4;
    rcases hx4 with ⟨ s, hs, rfl ⟩ ; exact ⟨ 1 - s, ⟨ by linarith [ hs.1, hs.2 ], by linarith [ hs.1, hs.2 ] ⟩, by simp +decide [ add_comm ] ⟩ ;
  -- By equating the two expressions for $x$, we get $t • O_point + (1 - t) • V_point = s • X_point + (1 - s) • Y_point$.
  have h_eq : t • O_point + (1 - t) • V_point = s • X_point + (1 - s) • Y_point := by
    rw [ ← ht.2, ← hs.2 ];
  have h0 := congrArg (fun q : Point => q 0) h_eq
  have h1 := congrArg (fun q : Point => q 1) h_eq
  unfold O_point X_point Y_point at h0 h1
  norm_num at h0 h1
  have hb_ne : V_point 1 ≠ 0 := by
    have hb_pos : 0 < V_point 1 := by
      have hb25 : 0.25 < V_point 1 := V_bounds.2.2.1
      linarith
    linarith
  have hden_ne : V_point 0 - x1 ≠ 0 := by
    have hxlt : x1 < V_point 0 := by
      linarith [x1_prop.2.1, V_bounds.1]
    linarith
  have hy_def : y1 = V_point 1 * (1 - x1) / (V_point 0 - x1) := rfl
  rw [hy_def] at h1
  field_simp [hden_ne, hb_ne] at h1
  have hy_line :
      (1 - t) * (V_point 0 - x1) =
        (1 - s) * (1 - x1) := by
    exact h1
  have hx_line :
      (1 - t) * V_point 0 - x1 =
        (1 - s) * (1 - x1) := by
    linear_combination h0
  nlinarith [hy_line, hx_line, ht.1.1, x1_prop.1]

/-
segment2 and segment5 are disjoint.
-/
lemma disjoint_2_5 : Disjoint segment2 segment5 := by
  have := @unit_segment_endpoints_are_vertices;
  contrapose! this;
  refine ⟨ 0, EuclideanSpace.single 1 1, EuclideanSpace.single 1 1, ?_, ?_, ?_, ?_ ⟩ <;> norm_num;
  refine ⟨ EuclideanSpace.single 1 ( 1 / 2 ), ?_, EuclideanSpace.single 1 ( 1 / 2 + 1 / 2 ), ?_, ?_ ⟩ <;> norm_num [ segment_eq_image ];
  · exact ⟨ 1 / 2, by norm_num, by ext i; fin_cases i <;> norm_num ⟩;
  · exact ⟨ 1, by norm_num ⟩;
  · norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
    exact this ( Set.disjoint_left.mpr fun x hx1 hx2 => by
      obtain ⟨ a, b, ha, hb, hab, rfl ⟩ := hx1;
      obtain ⟨ c, d, hc, hd, hcd, h ⟩ := hx2;
      have h0 := congrArg (fun q : Point => q 0) h;
      have h1 := congrArg (fun q : Point => q 1) h;
      have hden : V_point 0 - x1 ≠ 0 := by
        nlinarith [V_bounds.1, x1_prop.2.1];
      unfold sigma X_point Y_point O_point y1 at h0 h1;
      norm_num at h0 h1;
      rw [← sub_eq_zero] at h0;
      field_simp [hden] at h0;
      unfold V_point at h0 h1;
      norm_num at h0 h1;
      rcases h0 with hsqrt | h0;
      · nlinarith [hsqrt, Real.sqrt_nonneg 6,
          Real.mul_self_sqrt (show 6 ≥ 0 by norm_num),
          Real.mul_self_sqrt (show 2 ≥ 0 by norm_num)];
      · have hb_eq_one : b = 1 := by
          nlinarith [h0, h1, hcd, Real.mul_self_sqrt (show 6 ≥ 0 by norm_num),
            Real.mul_self_sqrt (show 2 ≥ 0 by norm_num), x1_prop];
        nlinarith )

/-
segment3 and segment4 are disjoint.
-/
lemma disjoint_3_4 : Disjoint segment3 segment4 := by
  have h_disjoint : ∀ p ∈ segment3, p ≠ V_point := by
    intro p hp hp'
    obtain ⟨ a, b, ha, hb, hab, hp_eq ⟩ := hp
    have hp_eq' : a • V_point + b • sigma V_point = V_point := hp_eq.trans hp'
    have h0 := congrArg (fun q : Point => q 0) hp_eq'
    have h1 := congrArg (fun q : Point => q 1) hp_eq'
    simp [sigma] at h0 h1
    nlinarith [V_bounds]
  exact Set.disjoint_left.mpr fun p hp3 hp4 => h_disjoint p hp3 <| by
    have h_inter : segment3 ∩ segment4 ⊆ {V_point} := by
      have h_line3 : ∀ p ∈ segment3, p 0 + p 1 = (V_point 0) + (V_point 1) := by
        intro p hp; obtain ⟨ a, b, ha, hb, hab, rfl ⟩ := hp; norm_num [ Fin.sum_univ_two ] ; ring_nf;
        unfold sigma; norm_num; rw [ ← eq_sub_iff_add_eq' ] at hab; subst_vars; ring;
      have h_line4 : ∀ p ∈ segment4, p 1 = ((Y_point 1) - (X_point 1)) / ((Y_point 0) - (X_point 0)) * (p 0 - (X_point 0)) + (X_point 1) := by
        intros p hp4
        have h_line4_eq : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ p = (1 - t) • X_point + t • Y_point := by
          rw [ segment4 ] at hp4; rw [ openSegment_eq_image ] at hp4; aesop;
        rcases h_line4_eq with ⟨ t, ht₀, ht₁, rfl ⟩ ; norm_num [ X_point, Y_point ] ; ring_nf;
        nlinarith [ inv_mul_cancel_left₀ ( show ( 1 - x1 ) ≠ 0 by linarith [ show x1 < 1 by exact lt_of_lt_of_le ( Classical.choose_spec ( exists_root_x1 ) |>.2.1 ) ( by norm_num ) ] ) ( t * y1 ) ]
      have h_eq : ∀ p ∈ segment3 ∩ segment4, p 0 = V_point 0 := by
        intros p hp
        have h_eq : p 0 + ((Y_point 1 - X_point 1) / (Y_point 0 - X_point 0)) * (p 0 - X_point 0) + X_point 1 = V_point 0 + V_point 1 := by
          linarith [ h_line3 p hp.1, h_line4 p hp.2 ];
        unfold Y_point X_point at *;
        rw [ div_mul_eq_mul_div, add_div', div_add', div_eq_iff ] at h_eq <;> norm_num at *;
        · unfold y1 at h_eq;
          rw [ div_mul_eq_mul_div, add_div', div_eq_iff ] at h_eq <;> norm_num at *;
          · by_cases h : 1 - x1 = 0 <;> simp +decide [ h, mul_assoc, mul_comm, mul_left_comm ] at h_eq ⊢;
            · linarith [ x1_prop ];
            · exact mul_left_cancel₀ h <| by nlinarith [ x1_prop, V_bounds ] ;
          · intro h; norm_num [ h ] at h_eq;
            exact absurd ( h_eq.resolve_left ( by linarith [ show 0 < V_point 0 from by exact div_pos ( by positivity ) ( by positivity ), show 0 < V_point 1 from by exact div_pos ( by nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ) ] ) ( by positivity ) ] ) ) ( by linarith [ show x1 < 1 by exact lt_of_lt_of_le ( Classical.choose_spec exists_root_x1 |>.2.1 ) ( by norm_num ) ] );
          · exact sub_ne_zero_of_ne <| by linarith [ V_bounds, x1_prop ] ;
        · linarith [ x1_prop ];
        · linarith [ x1_prop ];
        · linarith [ x1_prop ];
      intros p hp
      have hp0 : p 0 = V_point 0 := h_eq p hp
      have hp1 : p 1 = V_point 1 := by
        linarith [ h_line3 p hp.1 ];
      have hpV : p = V_point := by
        ext i
        fin_cases i <;> assumption
      simpa [hpV]
    exact h_inter ⟨ hp3, hp4 ⟩

/-
segment3 and segment5 are disjoint.
-/
lemma disjoint_3_5 : Disjoint segment3 segment5 := by
  convert Set.disjoint_left.mpr _;
  rintro p ⟨ a, b, ha, hb, hab, rfl ⟩ ⟨ c, d, hc, hd, hcd, h ⟩
  have h0 := congrArg (fun q : Point => q 0) h
  have h1 := congrArg (fun q : Point => q 1) h
  unfold sigma at h0 h1
  norm_num at h0 h1
  unfold X_point Y_point at h0 h1
  norm_num at h0 h1
  unfold y1 at h0
  norm_num [show a = 1 - b by linarith, show c = 1 - d by linarith] at h0 h1
  unfold V_point at *
  norm_num at *
  rw [mul_div, div_eq_iff] at h0
  · have := x1_prop;
    norm_num [ show b = 1 - a by linarith, show d = 1 - c by linarith ] at *;
    nlinarith [ show 0 < Real.sqrt 6 * Real.sqrt 2 by positivity, show 0 < Real.sqrt 6 by positivity, show 0 < Real.sqrt 2 by positivity, mul_pos ha hc, mul_pos ha ( sub_pos.mpr this.1 ), mul_pos ha ( sub_pos.mpr this.2.1 ), mul_pos hc ( sub_pos.mpr this.1 ), mul_pos hc ( sub_pos.mpr this.2.1 ), Real.mul_self_sqrt ( show 6 ≥ 0 by norm_num ), Real.mul_self_sqrt ( show 2 ≥ 0 by norm_num ) ];
  · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), x1_prop ]

/-
segment1 and segment2 are disjoint.
-/
lemma disjoint_1_2 : Disjoint segment1 segment2 := by
  unfold segment1 segment2;
  norm_num [ openSegment_eq_image ];
  norm_num [ Set.disjoint_left ];
  rintro a x hx₁ hx₂ rfl y hy₁ hy₂ H
  have H0 := congrArg (fun q : Point => q 0) H
  have H1 := congrArg (fun q : Point => q 1) H
  norm_num [ O_point, V_point, sigma ] at *
  nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 2,
    Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num),
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-
segment1 and segment3 are disjoint.
-/
lemma disjoint_1_3 : Disjoint segment1 segment3 := by
  unfold segment1 segment3;
  norm_num [ openSegment_eq_image ];
  norm_num [ Set.disjoint_left ];
  rintro a x hx₁ hx₂ rfl y hy₁ hy₂ H; have := congrArg (fun q : Point => q 0) H; have := congrArg (fun q : Point => q 1) H; norm_num [ O_point, V_point, sigma ] at *;
  nlinarith [ Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ), Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ), Real.mul_self_sqrt ( show 6 ≥ 0 by norm_num ), Real.mul_self_sqrt ( show 2 ≥ 0 by norm_num ) ]

/-
segment2 and segment3 are disjoint.
-/
lemma disjoint_2_3 : Disjoint segment2 segment3 := by
  rw [ Set.disjoint_left ];
  unfold segment2 segment3;
  norm_num [ openSegment_eq_image ];
  rintro a x hx₁ hx₂ rfl y hy₁ hy₂ H; have := congrArg (fun q : Point => q 0) H; have := congrArg (fun q : Point => q 1) H; norm_num [ O_point, V_point, sigma ] at *;
  nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ) ]

/-
The distance between sigma(V) and Y is less than 1.
-/
lemma dist_sigma_V_Y_lt_1 : dist (sigma V_point) Y_point < 1 := by
  -- By definition of $y1$, we know that $y1 = \frac{(Real.sqrt 6 - Real.sqrt 2)}{4} \cdot \frac{(1 - x1)}{\frac{(Real.sqrt 6 + Real.sqrt 2)}{4} - x1}$.
  have hy1 : y1 = (Real.sqrt 6 - Real.sqrt 2) / 4 * (1 - x1) / ((Real.sqrt 6 + Real.sqrt 2) / 4 - x1) := by
    unfold y1 V_point; ring_nf;
    repeat' erw [ Matrix.cons_val_succ' ] ; norm_num ; ring;
  -- By definition of $x1$, we know that $x1$ is in the interval $(0.95, 0.96)$.
  have hx1_bounds : 0.95 < x1 ∧ x1 < 0.96 := by
    exact ⟨ Classical.choose_spec exists_root_x1 |>.1, Classical.choose_spec exists_root_x1 |>.2.1 ⟩;
  -- By definition of $V_point$, we know that $V_point 0 = \frac{\sqrt{6} + \sqrt{2}}{4}$ and $V_point 1 = \frac{\sqrt{6} - \sqrt{2}}{4}$.
  have hV_bounds : 0.96 < V_point 0 ∧ V_point 0 < 0.97 ∧ 0.25 < V_point 1 ∧ V_point 1 < 0.26 := by
    exact V_bounds;
  -- By definition of $Y_point$, we know that $Y_point = !₂[1, y1]$.
  have hY_bounds : 0 < y1 ∧ y1 < 1 := by
    exact y1_bounds;
  norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] at *;
  rw [ Real.sqrt_lt' ] <;> norm_num [ sigma, V_point, Y_point ] at *;
  rw [ eq_div_iff ] at hy1 <;> try linarith [ hx1_bounds, hV_bounds, hY_bounds, hy1, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ) ] ;
  nlinarith only [ hy1, hx1_bounds, hV_bounds, hY_bounds, Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ]

/-
The distance between Y and sigma(Y) is less than 1.
-/
lemma dist_Y_sigma_Y_lt_1 : dist Y_point (sigma Y_point) < 1 := by
  norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
  rw [ Real.sqrt_lt' ] <;> norm_num [ Y_point, sigma ];
  -- By definition of $y1$, we know that $0 < y1 < 1$.
  have hy1_bounds : 0 < y1 ∧ y1 < 1 := by
    exact y1_bounds;
  nlinarith [ show y1 > 1 / 2 by { rw [ show y1 = ( V_point 1 ) * ( 1 - x1 ) / ( V_point 0 - x1 ) by rfl ] ; rw [ gt_iff_lt ] ; rw [ lt_div_iff₀ ] <;> nlinarith [ V_bounds, x1_prop ] } ]

/-
The distance between V and sigma(Y) is less than 1.
-/
lemma dist_V_sigma_Y_lt_1 : dist V_point (sigma Y_point) < 1 := by
  rw [← sigma_isometry V_point (sigma Y_point)]
  simpa [sigma, Y_point] using dist_sigma_V_Y_lt_1

/-
Region_Corner is the triangle with vertices Y, sigma Y, and (1,1).
-/
def Region_Corner : Set Point := convexHull ℝ {Y_point, sigma Y_point, !₂[1, 1]}

/-
The diameter of Region6b is less than 1.
-/
lemma Region6b_diameter_lt_1 : ∀ x y : Point, x ∈ Region6b → y ∈ Region6b → dist x y < 1 := by
  have h_sigma_V_sigma_Y_lt_1 : dist (sigma V_point) (sigma Y_point) < 1 := by
    rw [ sigma_isometry ];
    exact dist_V_Y_lt_1;
  intros x y hx hy;
  -- By the triangle diameter lemma, since the sides of Region6b are all less than 1, any two points in Region6b are also less than 1 apart.
  have h_triangle_diameter : ∀ x y : Point, x ∈ convexHull ℝ {sigma V_point, Y_point, sigma Y_point} → y ∈ convexHull ℝ {sigma V_point, Y_point, sigma Y_point} → dist x y ≤ max (dist (sigma V_point) Y_point) (max (dist Y_point (sigma Y_point)) (dist (sigma Y_point) (sigma V_point))) := by
    apply dist_le_max_vertices;
  refine lt_of_le_of_lt ( h_triangle_diameter x y hx hy ) ?_;
  simp_all +decide [ dist_comm ];
  exact ⟨ by simpa only [ dist_comm ] using dist_sigma_V_Y_lt_1, by simpa only [ dist_comm ] using dist_Y_sigma_Y_lt_1 ⟩

/-
Distance from O to sigma(X) is less than 1.
-/
lemma dist_O_sigma_X_lt_1 : dist O_point (sigma X_point) < 1 := by
  convert dist_O_X_lt_1 using 1;
  unfold O_point sigma; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] ; ring_nf;

/-
Distance from sigma(V) to sigma(X) is less than 1.
-/
lemma dist_sigma_V_sigma_X_lt_1 : dist (sigma V_point) (sigma X_point) < 1 := by
  rw [ sigma_isometry ] ; exact dist_V_X_lt_1;

/-
Distance from sigma(X) to sigma(A0) is less than 1.
-/
lemma dist_sigma_X_sigma_A0_lt_1 : dist (sigma X_point) (sigma A_0) < 1 := by
  rw [ @dist_eq_norm ];
  norm_num [ EuclideanSpace.norm_eq ];
  rw [ Real.sqrt_lt' ] <;> norm_num [ sigma, X_point, A_0 ];
  exact abs_lt.mpr ⟨ by linarith [ x1_prop.1 ], by linarith [ x1_prop.2.1 ] ⟩

/-
Distance from sigma(A0) to sigma(Y) is less than 1.
-/
lemma dist_sigma_A0_sigma_Y_lt_1 : dist (sigma A_0) (sigma Y_point) < 1 := by
  rw [ sigma_isometry ] ; exact dist_A0_Y_lt_1

/-
S_finite blocks Region1.
-/
lemma Region1_blocking : IsBlocking S_finite Region1 := by
  intro L hL hL_sub
  have hL_sub' : L ⊆ convexHull ℝ {O_point, V_point, sigma V_point} := by
    simpa [Region1] using hL_sub
  have hcases :
      L = openSegment ℝ O_point V_point ∨
        L = openSegment ℝ V_point (sigma V_point) ∨
          L = openSegment ℝ (sigma V_point) O_point := by
    refine triangle_diameter_lemma O_point V_point (sigma V_point) ?_ ?_ ?_ L hL hL_sub'
    · exact dist_O_V.le
    · exact dist_V_sigma_V.le
    · rw [dist_comm]
      exact dist_O_sigma_V.le
  rcases hcases with hL_eq | hL_eq | hL_eq
  · refine ⟨segment1, ?_, ?_⟩
    · simp [S_finite]
    · rw [hL_eq, segment1]
      simp only [disjoint_self, bot_eq_empty]
      rw [openSegment_eq_image]
      exact Set.nonempty_iff_ne_empty.mp
        ((Set.nonempty_Ioo.mpr (show (0 : ℝ) < 1 by norm_num)).image _)
  · refine ⟨segment3, ?_, ?_⟩
    · simp [S_finite]
    · rw [hL_eq, segment3]
      simp only [disjoint_self, bot_eq_empty]
      rw [openSegment_eq_image]
      exact Set.nonempty_iff_ne_empty.mp
        ((Set.nonempty_Ioo.mpr (show (0 : ℝ) < 1 by norm_num)).image _)
  · refine ⟨segment2, ?_, ?_⟩
    · simp [S_finite]
    · rw [hL_eq, segment2]
      simp only [openSegment_symm, disjoint_self, bot_eq_empty]
      rw [openSegment_eq_image]
      exact Set.nonempty_iff_ne_empty.mp
        ((Set.nonempty_Ioo.mpr (show (0 : ℝ) < 1 by norm_num)).image _)

/-
If the distance between endpoints is less than 1, the open segment is not a unit segment.
-/
lemma not_isUnitSegment_of_dist_lt_1 {A B : Point} (h : dist A B < 1) : ¬ IsUnitSegment (openSegment ℝ A B) := by
  rintro ⟨ x, y, hxy, h ⟩;
  -- Since open segments determine their endpoints (up to order), we must have {A, B} = {x, y}.
  have h_eq_set : ({A, B} : Set Point) = ({x, y} : Set Point) := by
    -- Applying the lemma that states the closure of an open segment is the closed segment.
    have h_closure : closure (openSegment ℝ A B) = segment ℝ A B ∧ closure (openSegment ℝ x y) = segment ℝ x y := by
      bound;
    simp_all +decide [ segment_eq_image ];
    have h_eq_set : ∀ t : ℝ, t ∈ Set.Icc 0 1 → ∃ s : ℝ, s ∈ Set.Icc 0 1 ∧ (1 - t) • x + t • y = (1 - s) • A + s • B := by
      exact fun t ht => h_closure.subset ⟨ t, ht, rfl ⟩ |> fun ⟨ s, hs, hs' ⟩ => ⟨ s, hs, hs'.symm ⟩;
    have h_eq_set : ∃ s₁ s₂ : ℝ, s₁ ∈ Set.Icc 0 1 ∧ s₂ ∈ Set.Icc 0 1 ∧ x = (1 - s₁) • A + s₁ • B ∧ y = (1 - s₂) • A + s₂ • B := by
      exact Exists.elim ( h_eq_set 0 ( by norm_num ) ) fun s₁ hs₁ => Exists.elim ( h_eq_set 1 ( by norm_num ) ) fun s₂ hs₂ => ⟨ s₁, s₂, hs₁.1, hs₂.1, by simpa using hs₁.2, by simpa using hs₂.2 ⟩;
    obtain ⟨ s₁, s₂, hs₁, hs₂, rfl, rfl ⟩ := h_eq_set;
    have h_eq_set : s₁ = 0 ∧ s₂ = 1 ∨ s₁ = 1 ∧ s₂ = 0 := by
      have h_eq_set : dist ((1 - s₁) • A + s₁ • B) ((1 - s₂) • A + s₂ • B) = |s₂ - s₁| * dist A B := by
        norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
        rw [ show ( ( 1 - s₁ ) * A 0 + s₁ * B 0 - ( ( 1 - s₂ ) * A 0 + s₂ * B 0 ) ) ^ 2 + ( ( 1 - s₁ ) * A 1 + s₁ * B 1 - ( ( 1 - s₂ ) * A 1 + s₂ * B 1 ) ) ^ 2 = ( s₂ - s₁ ) ^ 2 * ( ( A 0 - B 0 ) ^ 2 + ( A 1 - B 1 ) ^ 2 ) by ring, Real.sqrt_mul ( sq_nonneg _ ), Real.sqrt_sq_eq_abs ];
      cases abs_cases ( s₂ - s₁ ) <;> first | left; constructor <;> nlinarith [ hs₁.1, hs₁.2, hs₂.1, hs₂.2 ] | right; constructor <;> nlinarith [ hs₁.1, hs₁.2, hs₂.1, hs₂.2 ] ;
    rcases h_eq_set with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> norm_num;
    exact Set.pair_comm _ _;
  -- Since {A, B} = {x, y}, we have A = x and B = y or A = y and B = x.
  have h_cases : (A = x ∧ B = y) ∨ (A = y ∧ B = x) := by
    simp_all +decide [ Set.Subset.antisymm_iff, Set.subset_def ];
    aesop;
  cases h_cases <;> simp_all +decide [ dist_comm ]

/-
S_finite blocks Region2.
-/
lemma Region2_blocking : IsBlocking S_finite Region2 := by
  intro L hLL_sub hL_sub
  -- By the triangle diameter lemma, L must be one of the open segments OV, VX, or XO.
  have hL_segment : L = openSegment ℝ O_point V_point ∨ L = openSegment ℝ V_point X_point ∨ L = openSegment ℝ X_point O_point := by
    apply triangle_diameter_lemma O_point V_point X_point;
    · exact dist_O_V.le;
    · exact le_of_lt ( dist_V_X_lt_1 );
    · exact le_of_lt ( by simpa only [ dist_comm ] using dist_O_X_lt_1 );
    · assumption;
    · exact hL_sub;
  rcases hL_segment with ( rfl | rfl | rfl );
  · use openSegment ℝ O_point V_point;
    refine ⟨ ?_, ?_ ⟩;
    · exact Set.mem_insert _ _;
    · norm_num [ openSegment_eq_image ];
      exact Set.Nonempty.ne_empty ⟨ 1 / 2, by norm_num ⟩;
  · exact absurd hLL_sub ( not_isUnitSegment_of_dist_lt_1 ( dist_V_X_lt_1 ) );
  · exact absurd hLL_sub ( not_isUnitSegment_of_dist_lt_1 ( by linarith [ dist_comm O_point X_point, dist_O_X_lt_1 ] ) )

/-
S_finite blocks Region3.
-/
lemma Region3_blocking : IsBlocking S_finite Region3 := by
  intro L hL hL_subset
  have hL_segment : L = openSegment ℝ O_point (sigma V_point) ∨ L = openSegment ℝ (sigma V_point) (sigma X_point) ∨ L = openSegment ℝ (sigma X_point) O_point := by
    apply_rules [ triangle_diameter_lemma ];
    · exact dist_O_sigma_V.le.trans ( by norm_num );
    · exact le_of_lt ( dist_sigma_V_sigma_X_lt_1 );
    · exact le_of_lt ( by simpa [ dist_comm ] using dist_O_sigma_X_lt_1 );
  rcases hL_segment with ( rfl | rfl | rfl ) <;> simp_all +decide [ S_finite ];
  · unfold segment1 segment2 segment3 segment4 segment5; norm_num [ Set.disjoint_left ] ;
    exact Or.inr <| Or.inl <| Set.Nonempty.ne_empty <| by exact ⟨ ( 1 / 2 : ℝ ) • O_point + ( 1 / 2 : ℝ ) • sigma V_point, by exact ⟨ 1 / 2, 1 / 2, by norm_num ⟩ ⟩ ;
  · exact absurd hL ( not_isUnitSegment_of_dist_lt_1 ( by linarith [ dist_sigma_V_sigma_X_lt_1 ] ) );
  · contrapose! hL; simp_all +decide [ Set.disjoint_left ] ;
    exact not_isUnitSegment_of_dist_lt_1 ( by simpa [ dist_comm ] using dist_O_sigma_X_lt_1 )

/-
S_finite blocks Region5.
-/
lemma Region5_blocking : IsBlocking S_finite Region5 := by
  -- Apply the triangle diameter lemma to the triangle sigma(X), sigma(A0), sigma(Y).
  have h_triangle : ∀ L : Set Point, IsUnitSegment L → L ⊆ Region5 → L = openSegment ℝ (sigma X_point) (sigma A_0) ∨ L = openSegment ℝ (sigma A_0) (sigma Y_point) ∨ L = openSegment ℝ (sigma Y_point) (sigma X_point) := by
    intros L hL hL_sub
    apply triangle_diameter_lemma;
    · exact le_of_lt ( dist_sigma_X_sigma_A0_lt_1 );
    · exact le_of_lt ( by simpa [ dist_comm ] using dist_sigma_A0_sigma_Y_lt_1 );
    · simpa [dist_comm] using dist_sigma_X_sigma_Y.le;
    · assumption;
    · exact hL_sub;
  intro L hL hL_sub
  obtain hL_cases | hL_cases | hL_cases := h_triangle L hL hL_sub
  all_goals generalize_proofs at *;
  · -- Since $L$ is a unit segment and its endpoints are inside the square, its length must be strictly less than 1.
    have hL_length_lt_1 : dist (sigma X_point) (sigma A_0) < 1 := by
      exact dist_sigma_X_sigma_A0_lt_1;
    exact False.elim <| not_isUnitSegment_of_dist_lt_1 hL_length_lt_1 <| hL_cases ▸ hL;
  · have h_dist_lt_1 : dist (sigma A_0) (sigma Y_point) < 1 := by
      convert dist_sigma_A0_sigma_Y_lt_1 using 1
    generalize_proofs at *; (
    exact False.elim <| not_isUnitSegment_of_dist_lt_1 h_dist_lt_1 <| hL_cases ▸ hL);
  · use segment5; simp [hL_cases, S_finite];
    unfold segment5; simp +decide [ Set.disjoint_left ] ;
    refine ⟨ ( 1 / 2 : ℝ ) • sigma X_point + ( 1 / 2 : ℝ ) • sigma Y_point, ?_, ?_ ⟩ <;> norm_num [ openSegment_eq_image ];
    · exact ⟨ 1 / 2, by norm_num ⟩;
    · exact ⟨ 1 / 2, by norm_num, by ext i; fin_cases i <;> norm_num <;> ring ⟩

/-
If an open segment is contained in a closed region, its endpoints are also in the region (assuming distinct endpoints).
-/
lemma endpoints_in_closed_region {R : Set Point} (hR : IsClosed R) {x y : Point} (h_subset : openSegment ℝ x y ⊆ R) (h_nonempty : (openSegment ℝ x y).Nonempty) : x ∈ R ∧ y ∈ R := by
  have h_closure : closure (openSegment ℝ x y) ⊆ R := by
    exact hR.closure_subset_iff.mpr h_subset;
  have h_closure_eq : closure (openSegment ℝ x y) = segment ℝ x y := by
    exact closure_openSegment x y;
  exact ⟨ h_closure <| h_closure_eq.symm ▸ left_mem_segment _ _ _, h_closure <| h_closure_eq.symm ▸ right_mem_segment _ _ _ ⟩

/-
Region6_Total is the convex hull of {V, sigma V, Y, sigma Y, (1,1)}.
-/
def Region6_Total : Set Point := convexHull ℝ {V_point, sigma V_point, Y_point, sigma Y_point, !₂[1, 1]}

/-
The distance from V to (1,1) is less than 1.
-/
def Corner_point : Point := !₂[1, 1]

lemma dist_V_Corner_lt_1 : dist V_point Corner_point < 1 := by
  norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
  rw [ Real.sqrt_lt' ] <;> norm_num [ V_point, Corner_point ];
  nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ]

/-
Distance from Y to Corner is less than 1.
-/
lemma dist_Y_Corner_lt_1 : dist Y_point Corner_point < 1 := by
  unfold Y_point Corner_point;
  norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
  rw [ Real.sqrt_sq_eq_abs, abs_lt ];
  constructor <;> linarith [ y1_bounds ]

/-
Distance from sigma(V) to Corner is less than 1.
-/
lemma dist_sigma_V_Corner_lt_1 : dist (sigma V_point) Corner_point < 1 := by
  convert dist_V_Corner_lt_1 using 1;
  unfold sigma Corner_point; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] ;
  ring_nf

/-
The distance between two convex combinations is bounded by the weighted sum of distances between the points.
-/
lemma dist_convex_combination_le {ι : Type*} {s : Finset ι} {v : ι → Point} {a b : ι → ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ j ∈ s, 0 ≤ b j)
    (ha_sum : ∑ i ∈ s, a i = 1) (hb_sum : ∑ j ∈ s, b j = 1) :
    dist (∑ i ∈ s, a i • v i) (∑ j ∈ s, b j • v j) ≤ ∑ i ∈ s, ∑ j ∈ s, a i * b j * dist (v i) (v j) := by
      simp +decide only [dist_eq_norm];
      -- By Fubini's theorem, we can interchange the order of summation.
      have h_fubini : ∑ x ∈ s, a x • v x - ∑ x ∈ s, b x • v x = ∑ i ∈ s, ∑ j ∈ s, a i • b j • (v i - v j) := by
        simp +decide only [smul_sub, Finset.sum_sub_distrib];
        simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, ← Finset.smul_sum, ← Finset.sum_smul, ha_sum, hb_sum ];
      rw [ h_fubini ];
      refine le_trans ( norm_sum_le s fun i => ∑ j ∈ s, a i • b j • (v i - v j) )
        ( Finset.sum_le_sum fun i hi => le_trans
          ( norm_sum_le s fun j => a i • b j • (v i - v j) )
          ( Finset.sum_le_sum fun j hj => ?_ ) );
      simp +decide [ norm_smul, mul_assoc, abs_of_nonneg ( ha i hi ), abs_of_nonneg ( hb j hj ) ]

/-
If the distance between two convex combinations is 1 and the diameter is 1, then any pair of points with positive weights must be at distance 1.
-/
lemma convex_combination_dist_eq_one_implies_support_dist_eq_one
  {ι : Type*} {s : Finset ι} {v : ι → Point} {a b : ι → ℝ}
  (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ j ∈ s, 0 ≤ b j)
  (ha_sum : ∑ i ∈ s, a i = 1) (hb_sum : ∑ j ∈ s, b j = 1)
  (h_diam : ∀ i ∈ s, ∀ j ∈ s, dist (v i) (v j) ≤ 1)
  (h_dist : dist (∑ i ∈ s, a i • v i) (∑ j ∈ s, b j • v j) = 1) :
  ∀ i ∈ s, ∀ j ∈ s, a i > 0 → b j > 0 → dist (v i) (v j) = 1 := by
    -- Applying the lemma about distance and convex combination.
    have h_dist_le : ∑ i ∈ s, ∑ j ∈ s, a i * b j * dist (v i) (v j) = 1 := by
      have h_dist_le : 1 ≤ ∑ i ∈ s, ∑ j ∈ s, a i * b j * dist (v i) (v j) := by
        convert dist_convex_combination_le ha hb ha_sum hb_sum |> le_trans h_dist.ge using 1;
      refine le_antisymm ?_ h_dist_le;
      refine le_trans ( Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ( h_diam i hi j hj ) ( mul_nonneg ( ha i hi ) ( hb j hj ) ) ) ?_;
      simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, ha_sum, hb_sum ];
    intro i hi j hj hi_pos hj_pos
    have h_eq : a i * b j * dist (v i) (v j) = a i * b j := by
      by_contra h_neq;
      have h_eq : ∑ i ∈ s, ∑ j ∈ s, a i * b j * dist (v i) (v j) < ∑ i ∈ s, ∑ j ∈ s, a i * b j := by
        apply Finset.sum_lt_sum;
        · exact fun i hi => Finset.sum_le_sum fun j hj => mul_le_of_le_one_right ( mul_nonneg ( ha i hi ) ( hb j hj ) ) ( h_diam i hi j hj );
        · refine ⟨ i, hi, Finset.sum_lt_sum ?_ ?_ ⟩;
          · exact fun k hk => mul_le_of_le_one_right ( mul_nonneg hi_pos.le ( hb k hk ) ) ( h_diam i hi k hk );
          · exact ⟨ j, hj, lt_of_le_of_ne ( mul_le_of_le_one_right ( mul_nonneg hi_pos.le hj_pos.le ) ( h_diam i hi j hj ) ) h_neq ⟩;
      simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
    nlinarith only [ mul_pos hi_pos hj_pos, h_eq, h_diam i hi j hj ]

/-
If every pair of points with positive weights forms the set {A, B}, then the points are constant on the supports of the weights, taking distinct values A and B.
-/
lemma constant_on_support_of_pair_condition {ι : Type*} {s : Finset ι} {v : ι → Point} {a b : ι → ℝ} {A B : Point}
    (h_distinct : A ≠ B)
    (ha_exists : ∃ i ∈ s, a i > 0) (hb_exists : ∃ j ∈ s, b j > 0)
    (h_pair : ∀ i ∈ s, ∀ j ∈ s, a i > 0 → b j > 0 → ({v i, v j} : Set Point) = {A, B}) :
    ((∀ i ∈ s, a i > 0 → v i = A) ∧ (∀ j ∈ s, b j > 0 → v j = B)) ∨
    ((∀ i ∈ s, a i > 0 → v i = B) ∧ (∀ j ∈ s, b j > 0 → v j = A)) := by
      obtain ⟨ j, hj₁, hj₂ ⟩ := hb_exists;
      cases' eq_or_ne ( v j ) A with h h <;> simp_all +decide [ Set.Subset.antisymm_iff, Set.subset_def ];
      · grind;
      · grind

/-
If all pairs of points with positive weights in two convex combinations form the set {A, B}, then the convex combinations themselves form the set {A, B}.
-/
lemma support_implies_endpoints {ι : Type*} {s : Finset ι} {v : ι → Point} {a b : ι → ℝ} {A B : Point}
    (h_distinct : A ≠ B)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ j ∈ s, 0 ≤ b j)
    (ha_sum : ∑ i ∈ s, a i = 1) (hb_sum : ∑ j ∈ s, b j = 1)
    (h_pair : ∀ i ∈ s, ∀ j ∈ s, a i > 0 → b j > 0 → ({v i, v j} : Set Point) = {A, B}) :
    ({∑ i ∈ s, a i • v i, ∑ j ∈ s, b j • v j} : Set Point) = {A, B} := by
  have ha_exists : ∃ i ∈ s, a i > 0 := by
    have ha_sum_ne : (∑ i ∈ s, a i) ≠ 0 := by
      rw [ha_sum]
      norm_num
    obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha_sum_ne
    exact ⟨i, hi, lt_of_le_of_ne (ha i hi) (Ne.symm hne)⟩
  have hb_exists : ∃ j ∈ s, b j > 0 := by
    have hb_sum_ne : (∑ j ∈ s, b j) ≠ 0 := by
      rw [hb_sum]
      norm_num
    obtain ⟨j, hj, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb_sum_ne
    exact ⟨j, hj, lt_of_le_of_ne (hb j hj) (Ne.symm hne)⟩
  have sum_eq_of_support :
      ∀ {w : ι → ℝ}, (∀ i ∈ s, 0 ≤ w i) → (∑ i ∈ s, w i = 1) → ∀ C : Point,
        (∀ i ∈ s, w i > 0 → v i = C) → ∑ i ∈ s, w i • v i = C := by
    intro w hw hw_sum C hc
    calc
      ∑ i ∈ s, w i • v i = ∑ i ∈ s, w i • C := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        by_cases hwi : w i = 0
        · simp [hwi]
        · rw [hc i hi (lt_of_le_of_ne (hw i hi) (Ne.symm hwi))]
      _ = C := by
        simp [← Finset.sum_smul, hw_sum]
  rcases constant_on_support_of_pair_condition h_distinct ha_exists hb_exists h_pair with hAB | hBA
  · have hleft : ∑ i ∈ s, a i • v i = A :=
      sum_eq_of_support ha ha_sum A hAB.1
    have hright : ∑ j ∈ s, b j • v j = B :=
      sum_eq_of_support hb hb_sum B hAB.2
    rw [hleft, hright]
  · have hleft : ∑ i ∈ s, a i • v i = B :=
      sum_eq_of_support ha ha_sum B hBA.1
    have hright : ∑ j ∈ s, b j • v j = A :=
      sum_eq_of_support hb hb_sum A hBA.2
    rw [hleft, hright]
    ext x
    simp [or_comm]

/-
UnionRegions is the union of all 8 regions. S_total is the union of S_finite and S_sides.
-/
def UnionRegions : Set Point := Region1 ∪ Region2 ∪ Region3 ∪ Region4 ∪ Region5 ∪ Region6a ∪ Region6b ∪ Region_Corner

def S_total : Set (Set Point) := S_finite ∪ S_sides

/-
Applying sigma twice returns the original point.
-/
lemma sigma_sigma_eq_id (p : Point) : sigma (sigma p) = p := by
  ext i
  fin_cases i <;> rfl

/-
If a point satisfies the linear inequalities for Region2, it is in Region2.
-/
open Set

/-
If a point satisfies the linear inequalities for Region4, it is in Region4.
-/
open Set

lemma in_Region4_of_coords (p : Point) (hp : p ∈ Region_Square)
    (h1 : x1 ≤ p 0) -- Right of X
    (h2 : p 1 ≤ y1) -- Below Y
    (h3 : p 1 * (1 - x1) ≤ y1 * (p 0 - x1)) -- Below XY
    : p ∈ Region4 := by
      -- By definition of $Region4$, we know that $p$ is a convex combination of the vertices $X_point$, $A_0$, and $Y_point$.
      have h_convex_comb : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • X_point + b • A_0 + c • Y_point := by
        use (1 - p 0) / (1 - x1), 1 - (1 - p 0) / (1 - x1) - p 1 / y1, p 1 / y1;
        refine ⟨ div_nonneg ( by linarith [ hp.2.1 ] ) ( by linarith [ show x1 < 1 by exact lt_of_lt_of_le ( Classical.choose_spec exists_root_x1 |>.2.1 ) ( by norm_num ) ] ), ?_, ?_, ?_, ?_ ⟩ <;> norm_num [ X_point, A_0, Y_point ];
        · rw [ div_le_iff₀ ] <;> nlinarith [ show 0 < y1 by exact y1_bounds.1, show x1 < 1 by exact lt_of_lt_of_le ( Classical.choose_spec exists_root_x1 |>.2.1 ) ( by norm_num ), mul_div_cancel₀ ( 1 - p 0 ) ( by linarith [ show x1 < 1 by exact lt_of_lt_of_le ( Classical.choose_spec exists_root_x1 |>.2.1 ) ( by norm_num ) ] : ( 1 - x1 ) ≠ 0 ) ];
        · exact div_nonneg ( by linarith [ hp.2.2.1 ] ) ( by linarith [ y1_bounds.1 ] );
        · ring;
        · ext i ; fin_cases i <;> norm_num;
          · linarith! [ div_mul_cancel₀ ( 1 - p 0 ) ( show ( 1 - x1 ) ≠ 0 by linarith [ show x1 < 1 by exact lt_of_lt_of_le ( Classical.choose_spec exists_root_x1 |>.2.1 ) <| by norm_num ] ) ];
          · rw [ div_mul_cancel₀ _ ( ne_of_gt ( by linarith [ show 0 < y1 from by linarith [ show 0 < y1 from by linarith [ show 0 < y1 from by exact y1_bounds.1 ] ] ] ) ) ];
      obtain ⟨ a, b, c, ha, hb, hc, habc ⟩ := h_convex_comb
      rw [Region4]
      refine mem_convexHull_of_exists_fintype
        (ι := Fin 3) (s := ({X_point, A_0, Y_point} : Set Point))
        (fun i => if i = 0 then a else if i = 1 then b else c)
        (fun i => if i = 0 then X_point else if i = 1 then A_0 else Y_point) ?_ ?_ ?_ ?_
      · intro i
        fin_cases i <;> simpa using (by first | exact ha | exact hb | exact hc)
      · simpa [Fin.sum_univ_three, add_assoc] using habc.1
      · intro i
        fin_cases i <;> simp
      · simpa [Fin.sum_univ_three] using habc.2.symm

/-
If a point satisfies the linear inequalities for Region1, it is in Region1.
-/
open Set

/-
If a point satisfies the linear inequalities for Region3, it is in Region3.
-/
open Set

/-
If a point satisfies the linear inequality for Region_Corner, it is in Region_Corner.
-/
open Set

lemma in_Region_Corner_of_coords (p : Point) (hp : p ∈ Region_Square)
    (h1 : 1 + y1 ≤ p 0 + p 1) -- Above Y-sigma Y
    : p ∈ Region_Corner := by
      have hy_pos : 0 < 1 - y1 := by linarith [y1_bounds.2]
      have hy_ne : (1 - y1) ≠ 0 := ne_of_gt hy_pos
      have h_comb : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧
          p = a • Y_point + b • sigma Y_point + c • !₂[1, 1] := by
        use (1 - p 1) / (1 - y1), (1 - p 0) / (1 - y1),
          1 - (1 - p 1) / (1 - y1) - (1 - p 0) / (1 - y1)
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · exact div_nonneg (by linarith [hp.2.2.2]) (le_of_lt hy_pos)
        · exact div_nonneg (by linarith [hp.2.1]) (le_of_lt hy_pos)
        · rw [sub_sub, le_sub_iff_add_le]
          rw [zero_add, ← add_div, div_le_iff₀ hy_pos]
          nlinarith
        · ring
        · ext i
          fin_cases i <;> simp [Y_point, sigma]
          · field_simp [hy_ne]
            ring
          · field_simp [hy_ne]
            ring
      obtain ⟨a, b, c, ha, hb, hc, habc⟩ := h_comb
      rw [Region_Corner]
      refine mem_convexHull_of_exists_fintype
        (ι := Fin 3) (s := ({Y_point, sigma Y_point, !₂[1, 1]} : Set Point))
        (fun i => if i = 0 then a else if i = 1 then b else c)
        (fun i => if i = 0 then Y_point else if i = 1 then sigma Y_point else !₂[1, 1]) ?_ ?_ ?_ ?_
      · intro i
        fin_cases i <;> simpa using (by first | exact ha | exact hb | exact hc)
      · simpa [Fin.sum_univ_three, add_assoc] using habc.1
      · intro i
        fin_cases i <;> simp
      · simpa [Fin.sum_univ_three] using habc.2.symm

/-
A point is in Region5 iff its reflection is in Region4.
-/
open Set

lemma mem_Region5_iff_sigma_mem_Region4 (p : Point) : p ∈ Region5 ↔ sigma p ∈ Region4 := by
  unfold Region4 Region5;
  norm_num [ convexHull_eq, sigma ];
  constructor <;> rintro ⟨ ι, t, w, hw₁, hw₂, x, hx₁, hx₂ ⟩;
  · refine ⟨ι, t, w, hw₁, hw₂, fun i => !₂[(x i) 1, (x i) 0], ?_, ?_⟩
    · intro i hi; specialize hx₁ i hi; aesop;
    · ext i
      fin_cases i <;> simp +decide [← hx₂, Finset.centerMass, Finset.sum_apply, Algebra.smul_def]
  · refine ⟨ι, t, w, hw₁, hw₂, fun i => !₂[x i 1, x i 0], ?_, ?_⟩
    · intro i hi; specialize hx₁ i hi; aesop;
    · convert congr_arg ( fun q => !₂[q 1, q 0] ) hx₂ using 1;
      · ext i
        fin_cases i <;>
          simp +decide [Finset.centerMass, Finset.sum_apply, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _,
            Finset.sum_add_distrib, add_mul, mul_add, mul_assoc, mul_comm, mul_left_comm, Finset.sum_smul]
      · ext i; fin_cases i <;> rfl;

/-
A point is in Region3 iff its reflection is in Region2.
-/
open Set

lemma mem_Region3_iff_sigma_mem_Region2 (p : Point) : p ∈ Region3 ↔ sigma p ∈ Region2 := by
  let sigmaLinear : Point →ₗ[ℝ] Point :=
    { toFun := sigma
      map_add' := by
        intro x y
        ext i <;> fin_cases i <;> rfl
      map_smul' := by
        intro c x
        ext i <;> fin_cases i <;> rfl }
  have h_sigma_Region2 : sigma '' Region2 = Region3 := by
    change sigmaLinear '' Region2 = Region3
    rw [Region2, Region3, LinearMap.image_convexHull]
    congr 1
    apply Set.ext
    intro q
    simp [sigmaLinear, sigma, O_point, V_point, X_point] <;> aesop
  rw [ ← h_sigma_Region2, mem_image ];
  constructor <;> intro h;
  · rcases h with ⟨ x, hx, hxp ⟩
    rw [← hxp, sigma_sigma_eq_id]
    exact hx
  · exact ⟨ _, h, sigma_sigma_eq_id p ⟩

/-
The collection S_finite is finite.
-/
lemma S_finite_finite : Set.Finite S_finite := by
  exact Set.toFinite { segment1, segment2, segment3, segment4, segment5 }

/-
The collection S_total is finite.
-/
lemma S_total_finite : Set.Finite S_total := by
  apply Set.Finite.union ?_ ?_;
  · exact S_finite_finite;
  · exact Set.toFinite { V_L, V_R, H_bot, H_top }

/-
S_total is a disjoint collection of unit segments.
-/
lemma S_total_is_disjoint_collection : IsDisjointCollection S_total := by
  -- Since S_finite and S_sides are disjoint and each consists of unit segments, their union S_total is also a disjoint collection of unit segments.
  apply And.intro;
  · intro s hs
    apply Or.elim hs;
    · exact fun a ↦ S_finite_consists_of_unit_segments s a;
    · rintro ( rfl | rfl | rfl | rfl ) <;> unfold IsUnitSegment;
      · unfold V_L; use !₂[0, 0], !₂[0, 1]; norm_num;
        norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
      · use !₂[1, 0], !₂[1, 1];
        unfold V_R; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] ;
      · unfold H_bot; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] ;
        exact ⟨ _, _, by norm_num, rfl ⟩;
      · exact ⟨ _, _, by norm_num [ EuclideanSpace.dist_eq ], rfl ⟩;
  · intro s t hs ht hst;
    cases' hs with hs hs <;> cases' ht with ht ht <;> simp_all +decide [ S_finite, S_sides ];
    · rcases hs with ( rfl | rfl | rfl | rfl | rfl ) <;> rcases ht with ( rfl | rfl | rfl | rfl | rfl ) <;> norm_num [ disjoint_1_2, disjoint_1_3, disjoint_1_4, disjoint_1_5, disjoint_2_3, disjoint_2_4, disjoint_2_5, disjoint_3_4, disjoint_3_5, disjoint_4_5 ];
      · exact False.elim (hst rfl);
      · exact Disjoint.symm disjoint_1_2;
      · grind;
      · exact Disjoint.symm disjoint_1_3;
      · exact Disjoint.symm disjoint_2_3;
      · exact False.elim (hst rfl);
      · exact Disjoint.symm disjoint_1_4;
      · exact Disjoint.symm disjoint_2_4;
      · exact Disjoint.symm disjoint_3_4;
      · exact False.elim (hst rfl);
      · exact Disjoint.symm disjoint_1_5;
      · exact Disjoint.symm disjoint_2_5;
      · exact Disjoint.symm disjoint_3_5;
      · exact Disjoint.symm disjoint_4_5;
      · grind;
    · have h_boundary_segments : ∀ s ∈ ({V_L, V_R, H_bot, H_top} : Set (Set Point)), ∀ t ∈ ({segment1, segment2, segment3, segment4, segment5} : Set (Set Point)), Disjoint s t := by
        intro s hs t ht
        have h_disjoint : s ⊆ SquareBoundary ∧ t ⊆ Region_Square := by
          have h_boundary_s : s ⊆ SquareBoundary := by
            rcases hs with ( rfl | rfl | rfl | rfl ) <;> intro p hp <;> unfold SquareBoundary <;> simp_all +decide [ Set.subset_def ];
            · rcases hp with ⟨ a, b, ha, hb, hab, rfl ⟩ ; norm_num [ UnitSquare ] at *;
              exact Or.inl ⟨ by linarith, by linarith ⟩;
            · rcases hp with ⟨ a, b, ha, hb, hab, rfl ⟩ ; norm_num [ UnitSquare ];
              exact Or.inr <| Or.inl ⟨ ⟨ ⟨ by linarith, by linarith ⟩, ⟨ by linarith, by linarith ⟩ ⟩, hab ⟩;
            · rcases hp with ⟨ a, b, ha, hb, hab, rfl ⟩ ; norm_num [ UnitSquare ];
              exact Or.inr <| Or.inr ⟨ by linarith, by linarith ⟩;
            · rcases hp with ⟨ a, b, ha, hb, hab, rfl ⟩ ; norm_num [ UnitSquare ];
              exact Or.inr <| Or.inr <| Or.inr ⟨ ⟨ ⟨ by linarith, by linarith ⟩, by linarith, by linarith ⟩, by linarith ⟩;
          exact ⟨ h_boundary_s, by rcases ht with ( rfl | rfl | rfl | rfl | rfl ) <;> [ exact segment_from_corner_in_square _ ( V_in_Region_Square ) ; exact segment_from_corner_in_square _ ( sigma_V_in_Region_Square ) ; exact segment_inside_square _ _ ( V_in_Region_Square ) ( sigma_V_in_Region_Square ) ; exact segment4_in_square; exact segment5_in_square ] ⟩
        refine Set.disjoint_left.mpr fun x hx hx' => ?_;
        have := h_disjoint.1 hx; have := h_disjoint.2 hx'; simp_all +decide [ SquareBoundary, Region_Square ] ;
        rcases ‹x ∈ UnitSquare ∧ x 0 = 0 ∨ x ∈ UnitSquare ∧ x 0 = 1 ∨ x ∈ UnitSquare ∧ x 1 = 0 ∨ x ∈ UnitSquare ∧ x 1 = 1› with ( ⟨ hx₁, hx₂ ⟩ | ⟨ hx₁, hx₂ ⟩ | ⟨ hx₁, hx₂ ⟩ | ⟨ hx₁, hx₂ ⟩ ) <;> linarith;
      exact Disjoint.symm (h_boundary_segments t ht s hs)
    · -- By definition of $V_L$, $V_R$, $H_bot$, and $H_top$, they are all boundary segments of the unit square.
      have h_boundary_segments : ∀ s ∈ ({V_L, V_R, H_bot, H_top} : Set (Set Point)), ∀ t ∈ ({segment1, segment2, segment3, segment4, segment5} : Set (Set Point)), Disjoint s t := by
        intro s hs t ht
        have h_disjoint : s ⊆ SquareBoundary ∧ t ⊆ Region_Square := by
          -- Since $s$ is a boundary segment, it is contained within the boundary of the unit square.
          have h_boundary_s : s ⊆ SquareBoundary := by
            rcases hs with ( rfl | rfl | rfl | rfl ) <;> intro p hp <;> unfold SquareBoundary <;> simp_all +decide [ Set.subset_def ];
            · rcases hp with ⟨ a, b, ha, hb, hab, rfl ⟩ ; norm_num [ UnitSquare ] at *;
              exact Or.inl ⟨ by linarith, by linarith ⟩;
            · rcases hp with ⟨ a, b, ha, hb, hab, rfl ⟩ ; norm_num [ UnitSquare ];
              exact Or.inr <| Or.inl ⟨ ⟨ ⟨ by linarith, by linarith ⟩, ⟨ by linarith, by linarith ⟩ ⟩, hab ⟩;
            · rcases hp with ⟨ a, b, ha, hb, hab, rfl ⟩ ; norm_num [ UnitSquare ];
              exact Or.inr <| Or.inr ⟨ by linarith, by linarith ⟩;
            · rcases hp with ⟨ a, b, ha, hb, hab, rfl ⟩ ; norm_num [ UnitSquare ];
              exact Or.inr <| Or.inr <| Or.inr ⟨ ⟨ ⟨ by linarith, by linarith ⟩, by linarith, by linarith ⟩, by linarith ⟩;
          exact ⟨ h_boundary_s, by rcases ht with ( rfl | rfl | rfl | rfl | rfl ) <;> [ exact segment_from_corner_in_square _ ( V_in_Region_Square ) ; exact segment_from_corner_in_square _ ( sigma_V_in_Region_Square ) ; exact segment_inside_square _ _ ( V_in_Region_Square ) ( sigma_V_in_Region_Square ) ; exact segment4_in_square; exact segment5_in_square ] ⟩
        refine Set.disjoint_left.mpr fun x hx hx' => ?_;
        have := h_disjoint.1 hx; have := h_disjoint.2 hx'; simp_all +decide [ SquareBoundary, Region_Square ] ;
        rcases ‹x ∈ UnitSquare ∧ x 0 = 0 ∨ x ∈ UnitSquare ∧ x 0 = 1 ∨ x ∈ UnitSquare ∧ x 1 = 0 ∨ x ∈ UnitSquare ∧ x 1 = 1› with ( ⟨ hx₁, hx₂ ⟩ | ⟨ hx₁, hx₂ ⟩ | ⟨ hx₁, hx₂ ⟩ | ⟨ hx₁, hx₂ ⟩ ) <;> linarith;
      exact h_boundary_segments s hs t ht
    · rcases hs with ( rfl | rfl | rfl | rfl ) <;> rcases ht with ( rfl | rfl | rfl | rfl ) <;> norm_num [ V_L, V_R, H_bot, H_top, openSegment_eq_image ];
      all_goals norm_num [ Set.disjoint_left ] at *;
      all_goals rintro a x hx₁ hx₂ rfl y hy₁ hy₂; intro H; have h0 := congrArg (fun p : Point => p 0) H; have h1 := congrArg (fun p : Point => p 1) H; norm_num [ hx₁.ne', hx₂.ne', hy₁.ne', hy₂.ne' ] at *;
      · linarith;
      · linarith

/-
S_total is contained in the closed unit square.
-/
lemma S_total_in_UnitSquare : IsInRegion S_total UnitSquare := by
  intro s hs;
  cases' hs with hs hs;
  · -- Since $S_finite$ is a subset of the open unit square, every element of $S_finite$ is contained in the open unit square.
    have h_open_unit_square : ∀ s ∈ S_finite, s ⊆ Region_Square := by
      apply S_finite_in_region;
    exact Set.Subset.trans ( h_open_unit_square s hs ) ( fun x hx => by exact fun i => ⟨ hx.1 |> fun h => by fin_cases i <;> linarith! [ hx.2 ], hx.2 |> fun h => by fin_cases i <;> linarith! [ hx.1 ] ⟩ );
  · -- Each of the segments V_L, V_R, H_bot, and H_top is a subset of the unit square.
    have h_segments : V_L ⊆ UnitSquare ∧ V_R ⊆ UnitSquare ∧ H_bot ⊆ UnitSquare ∧ H_top ⊆ UnitSquare := by
      unfold V_L V_R H_bot H_top UnitSquare;
      norm_num [ Set.subset_def, openSegment_eq_image ];
      exact ⟨ by rintro x a ha₁ ha₂ rfl; exact ⟨ ⟨ by norm_num [ ha₁.le ], by norm_num [ ha₂.le ] ⟩, ⟨ by norm_num [ ha₁.le ], by norm_num [ ha₂.le ] ⟩ ⟩, by rintro x a ha₁ ha₂ rfl; exact ⟨ ⟨ by norm_num [ ha₁.le ], by norm_num [ ha₂.le ] ⟩, ⟨ by norm_num [ ha₁.le ], by norm_num [ ha₂.le ] ⟩ ⟩, by rintro x a ha₁ ha₂ rfl; exact ⟨ ⟨ by norm_num [ ha₁.le ], by norm_num [ ha₂.le ] ⟩, ⟨ by norm_num [ ha₁.le ], by norm_num [ ha₂.le ] ⟩ ⟩, by rintro x a ha₁ ha₂ rfl; exact ⟨ ⟨ by norm_num [ ha₁.le ], by norm_num [ ha₂.le ] ⟩, ⟨ by norm_num [ ha₁.le ], by norm_num [ ha₂.le ] ⟩ ⟩ ⟩;
    unfold S_sides at hs
    focus
      aesop

/-
The diameter of Region6_Total is at most 1.
-/
lemma Region6_Total_diameter_le_1 : ∀ x y : Point, x ∈ Region6_Total → y ∈ Region6_Total → dist x y ≤ 1 := by
  have h_convex_comb : ∀ x y : Point, x ∈ convexHull ℝ {V_point, sigma V_point, Y_point, sigma Y_point, !₂[1, 1]} → y ∈ convexHull ℝ {V_point, sigma V_point, Y_point, sigma Y_point, !₂[1, 1]} → dist x y ≤ max (max (max (max (dist V_point (sigma V_point)) (dist V_point Y_point)) (dist V_point (sigma Y_point))) (dist V_point !₂[1, 1])) (max (max (max (dist (sigma V_point) Y_point) (dist (sigma V_point) (sigma Y_point))) (dist (sigma V_point) !₂[1, 1])) (max (max (dist Y_point (sigma Y_point)) (dist Y_point !₂[1, 1])) (dist (sigma Y_point) !₂[1, 1]))) := by
    intros x y hx hy
    have h_convex_comb : ∃ a : Fin 5 → ℝ, (∀ i, 0 ≤ a i) ∧ (∑ i, a i = 1) ∧ x = ∑ i, a i • ![V_point, sigma V_point, Y_point, sigma Y_point, !₂[1, 1]] i := by
      simp_all +decide [ convexHull_insert ];
      rcases hx with ⟨ i, hi, j, hj, k, hk, hx ⟩;
      rcases hx with ⟨ a, b, ha, hb, hab, rfl ⟩ ; rcases hk with ⟨ c, d, hc, hd, hcd, rfl ⟩ ; rcases hj with ⟨ e, f, he, hf, hef, rfl ⟩ ; rcases hi with ⟨ g, h, hg, hh, hgh, rfl ⟩ ; norm_num [ Fin.sum_univ_succ ] at *;
      refine ⟨ fun i => if i = 0 then a else if i = 1 then b * c else if i = 2 then b * d * e else if i = 3 then b * d * f * g else b * d * f * h, ?_, ?_, ?_ ⟩ <;> simp +decide [ Fin.forall_fin_succ, * ]
      focus
        ring_nf
      · exact ⟨ mul_nonneg hb hc, mul_nonneg ( mul_nonneg hb hd ) he, mul_nonneg ( mul_nonneg ( mul_nonneg hb hd ) hf ) hg, mul_nonneg ( mul_nonneg ( mul_nonneg hb hd ) hf ) hh ⟩;
      · grind +ring;
      · ext i ; fin_cases i <;> norm_num [ Matrix.vecHead, Matrix.vecTail ] <;> ring!;
    have h_convex_comb_y : ∃ b : Fin 5 → ℝ, (∀ i, 0 ≤ b i) ∧ (∑ i, b i = 1) ∧ y = ∑ i, b i • ![V_point, sigma V_point, Y_point, sigma Y_point, !₂[1, 1]] i := by
      rw [ @convexHull_eq ] at hy;
      rcases hy with ⟨ ι, t, w, z, hw, hw', hz, rfl ⟩;
      -- By definition of $z$, we know that $z i$ is one of the vertices $V_point$, $sigma V_point$, $Y_point$, $sigma Y_point$, or $!₂[1, 1]$.
      have hz_vertices : ∀ i ∈ t, ∃ j : Fin 5, z i = ![V_point, sigma V_point, Y_point, sigma Y_point, !₂[1, 1]] j := by
        intro i hi; specialize hz i hi; rcases hz with ( h | h | h | h | h ) <;> [ exact ⟨ 0, h ⟩ ; exact ⟨ 1, h ⟩ ; exact ⟨ 2, h ⟩ ; exact ⟨ 3, h ⟩ ; exact ⟨ 4, h ⟩ ] ;
      choose! j hj using hz_vertices;
      refine ⟨ fun i => ∑ j ∈ t.filter ( fun k => j k = i ), w j, ?_, ?_, ?_ ⟩ <;> simp_all +decide [ Finset.centerMass ];
      · exact fun i => Finset.sum_nonneg fun j hj => hw j <| Finset.mem_filter.mp hj |>.1;
      · rw [ ← hw', Finset.sum_fiberwise ];
      · simp +decide [ Finset.sum_filter, Finset.sum_smul ];
        rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
    -- Apply the lemma dist_convex_combination_le with the given conditions.
    obtain ⟨a, ha_nonneg, ha_sum, hx⟩ := h_convex_comb
    obtain ⟨b, hb_nonneg, hb_sum, hy⟩ := h_convex_comb_y
    have h_dist_le : dist x y ≤ ∑ i, ∑ j, a i * b j * dist (![V_point, sigma V_point, Y_point, sigma Y_point, !₂[1, 1]] i) (![V_point, sigma V_point, Y_point, sigma Y_point, !₂[1, 1]] j) := by
      rw [ hx, hy ];
      convert dist_convex_combination_le ( fun i _ => ha_nonneg i ) ( fun i _ => hb_nonneg i ) ha_sum hb_sum using 1;
    refine le_trans h_dist_le ?_;
    have h_dist_le : ∀ i j, dist (![V_point, sigma V_point, Y_point, sigma Y_point, !₂[1, 1]] i) (![V_point, sigma V_point, Y_point, sigma Y_point, !₂[1, 1]] j) ≤ max (max (max (max (dist V_point (sigma V_point)) (dist V_point Y_point)) (dist V_point (sigma Y_point))) (dist V_point !₂[1, 1])) (max (max (max (dist (sigma V_point) Y_point) (dist (sigma V_point) (sigma Y_point))) (dist (sigma V_point) !₂[1, 1])) (max (max (dist Y_point (sigma Y_point)) (dist Y_point !₂[1, 1])) (dist (sigma Y_point) !₂[1, 1]))) := by
      simp +decide [ Fin.forall_fin_succ ];
      simp +decide [ dist_comm ];
    refine le_trans ( Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ( h_dist_le i j ) ( mul_nonneg ( ha_nonneg i ) ( hb_nonneg j ) ) ) ?_;
    simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, ha_sum, hb_sum ];
  -- By calculating the distances between each pair of points, we can verify that they are all less than or equal to 1.
  have h_dist_V_sigma_V : dist V_point (sigma V_point) = 1 := by
    exact dist_V_sigma_V
  have h_dist_V_Y : dist V_point Y_point < 1 := by
    exact dist_V_Y_lt_1
  have h_dist_V_sigma_Y : dist V_point (sigma Y_point) < 1 := by
    exact dist_V_sigma_Y_lt_1
  have h_dist_V_Corner : dist V_point !₂[1, 1] < 1 := by
    simpa [Corner_point] using dist_V_Corner_lt_1
  have h_dist_sigma_V_Y : dist (sigma V_point) Y_point < 1 := by
    exact dist_sigma_V_Y_lt_1
  have h_dist_sigma_V_sigma_Y : dist (sigma V_point) (sigma Y_point) < 1 := by
    convert Region6b_diameter_lt_1 _ _ _ _ using 1;
    · exact subset_convexHull ℝ _ ( by norm_num );
    · exact subset_convexHull ℝ _ <| by norm_num;
  have h_dist_sigma_V_Corner : dist (sigma V_point) !₂[1, 1] < 1 := by
    simpa [Corner_point] using dist_sigma_V_Corner_lt_1
  have h_dist_Y_sigma_Y : dist Y_point (sigma Y_point) < 1 := by
    exact dist_Y_sigma_Y_lt_1
  have h_dist_Y_Corner : dist Y_point !₂[1, 1] < 1 := by
    simpa [Corner_point] using dist_Y_Corner_lt_1
  have h_dist_sigma_Y_Corner : dist (sigma Y_point) !₂[1, 1] < 1 := by
    have h := sigma_isometry Y_point Corner_point
    have h' : dist (sigma Y_point) (sigma Corner_point) < 1 := by
      rw [h]
      exact dist_Y_Corner_lt_1
    simpa [Corner_point, sigma] using h'
  exact fun x y hx hy => le_trans ( h_convex_comb x y hx hy ) ( by exact max_le ( max_le ( max_le ( max_le ( by linarith ) ( by linarith ) ) ( by linarith ) ) ( by linarith ) ) ( max_le ( max_le ( max_le ( by linarith ) ( by linarith ) ) ( by linarith ) ) ( max_le ( max_le ( by linarith ) ( by linarith ) ) ( by linarith ) ) ) )

/-
S_finite blocks Region6_Total.
-/
lemma Region6_Total_blocking : IsBlocking S_finite Region6_Total := by
  -- If L is a unit segment in Region6_Total, then L must be segment3.
  have h_segment3 : ∀ L : Set Point, IsUnitSegment L → L ⊆ Region6_Total → L = openSegment ℝ V_point (sigma V_point) := by
    intros L hL_unit hL_subset
    obtain ⟨x, y, hxy⟩ := hL_unit
    have hxy_dist : dist x y = 1 := by
      exact hxy.1
    have hxy_segment : x ∈ Region6_Total ∧ y ∈ Region6_Total := by
      have hL_subset_closed : IsClosed Region6_Total := by
        -- The convex hull of a finite set of points in Euclidean space is closed.
        have h_convex_hull_closed : ∀ (s : Finset Point), IsClosed (convexHull ℝ (s : Set Point)) := by
          intro s
          have h_convex_hull_closed : IsCompact (convexHull ℝ (s : Set Point)) := by
            exact s.finite_toSet.isCompact_convexHull ℝ
          generalize_proofs at *;
          exact h_convex_hull_closed.isClosed;
        convert h_convex_hull_closed { V_point, sigma V_point, Y_point, sigma Y_point, !₂[1, 1] } using 1;
        unfold Region6_Total; aesop;
      have hxy_segment : openSegment ℝ x y ⊆ Region6_Total := by
        aesop
      have hxy_endpoints : x ∈ Region6_Total ∧ y ∈ Region6_Total := by
        apply endpoints_in_closed_region hL_subset_closed hxy_segment (by
        exact ⟨ ( 1 / 2 : ℝ ) • x + ( 1 / 2 : ℝ ) • y, by exact ⟨ 1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num ⟩ ⟩)
      exact hxy_endpoints
      skip
    have hxy_segment3 : x = V_point ∧ y = sigma V_point ∨ x = sigma V_point ∧ y = V_point := by
      have hxy_segment3 : ∀ x y : Point, x ∈ Region6_Total → y ∈ Region6_Total → dist x y = 1 → x = V_point ∧ y = sigma V_point ∨ x = sigma V_point ∧ y = V_point := by
        intros x y hx hy hxy_dist
        have hxy_segment3 : ∀ i ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, !₂[1, 1]} : Finset Point), ∀ j ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, !₂[1, 1]} : Finset Point), dist i j = 1 → i = V_point ∧ j = sigma V_point ∨ i = sigma V_point ∧ j = V_point := by
          simp +zetaDelta at *;
          refine ⟨ ?_, ?_, ?_, ?_, ?_ ⟩;
          · exact ⟨ fun h => False.elim <| absurd h <| ne_of_lt <| dist_V_Y_lt_1, fun h => False.elim <| absurd h <| ne_of_lt <| dist_V_sigma_Y_lt_1, fun h => False.elim <| absurd h <| ne_of_lt <| dist_V_Corner_lt_1 ⟩;
          · refine ⟨ ?_, ?_, ?_ ⟩;
            · intro h_dist
              have hxy_segment3 : dist (sigma V_point) Y_point < 1 := by
                exact dist_sigma_V_Y_lt_1
              exact absurd hxy_dist (by linarith [hxy_segment3]);
            · intro h_dist
              have hxy_segment3 : dist V_point Y_point = 1 := by
                rw [ ← h_dist, sigma_isometry ];
              exact absurd hxy_segment3 ( by exact ne_of_lt ( by exact dist_V_Y_lt_1 ) );
            · norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
              unfold sigma V_point; norm_num [ Fin.sum_univ_succ ] ; ring_nf ;
              exact fun h => absurd h ( by nlinarith only [ Real.sqrt_nonneg 6, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sqrt_nonneg 2, Real.sq_sqrt ( show 2 ≥ 0 by norm_num ) ] );
          · refine ⟨ ?_, ?_, ?_, ?_ ⟩;
            · intro h;
              exact absurd h ( by rw [ dist_comm ] ; exact ne_of_lt ( dist_V_Y_lt_1 ) );
            · intro h;
              exact absurd h ( by rw [ dist_comm ] ; exact ne_of_lt ( dist_sigma_V_Y_lt_1 ) );
            · intro h_dist
              have hxy_segment3 : dist Y_point (sigma Y_point) < 1 := by
                exact dist_Y_sigma_Y_lt_1
              exact absurd hxy_dist (by linarith [hxy_segment3]);
            · intro h; have := dist_Y_Corner_lt_1; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] at *;
              rw [ Real.sqrt_lt' ] at this <;> norm_num [ Corner_point ] at * ; nlinarith [ this, h ];
          · refine ⟨ ?_, ?_, ?_, ?_ ⟩;
            · intro hxy_dist
              have hxy_segment3 : dist (sigma Y_point) V_point < 1 := by
                convert dist_V_sigma_Y_lt_1 using 1;
                exact dist_comm _ _
              exact absurd hxy_dist (by linarith);
            · have := dist_sigma_V_Y_lt_1; ( have := dist_sigma_V_Corner_lt_1; ( have := dist_Y_Corner_lt_1; ( have := dist_V_Corner_lt_1; ( have := dist_V_Y_lt_1; ( have := dist_O_V; ( have := dist_O_sigma_V; ( have := dist_O_X_lt_1; ( have := dist_V_X_lt_1; ( have := dist_X_A0_lt_1; ( have := dist_A0_Y_lt_1; ( have := dist_sigma_X_sigma_Y; ( have := dist_sigma_V_sigma_X_lt_1; ( have := dist_sigma_A0_sigma_Y_lt_1; ( norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] at *; ) ) ) ) ) ) ) ) ) ) ) ) ) );
              norm_num [ Real.sqrt_lt', sigma, V_point, Y_point ] at *;
              grind;
            · intro hxy_dist
              have hxy_segment3 : dist Y_point (sigma Y_point) < 1 := by
                exact dist_Y_sigma_Y_lt_1
              exact absurd hxy_dist (by
              exact ne_of_lt ( by rwa [ dist_comm ] ));
            · intro h; have := dist_Y_Corner_lt_1; simp_all +decide [ dist_comm ] ;
              unfold Corner_point at this; simp_all +decide [ dist_eq_norm, EuclideanSpace.norm_eq ] ;
              rw [ Real.sqrt_lt' ] at this <;> norm_num [ sigma ] at *;
              linarith;
          · norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
            unfold V_point sigma Y_point; norm_num [ Fin.ext_iff ] ; ring_nf ;
            norm_num [ ← List.ofFn_inj ] ; ring_nf ; norm_num;
            exact ⟨ fun h => absurd h ( by nlinarith only [ Real.sq_sqrt ( show 6 ≥ 0 by norm_num ) ] ), fun h => absurd h ( by nlinarith only [ Real.sq_sqrt ( show 6 ≥ 0 by norm_num ) ] ), fun h => absurd h ( by rintro ( h | h ) <;> nlinarith only [ Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, y1_bounds, h ] ), fun h => absurd h ( by rintro ( h | h ) <;> nlinarith only [ Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, y1_bounds, h ] ) ⟩;
        have hxy_comb : ∃ (a : Point → ℝ) (b : Point → ℝ), (∀ i ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, !₂[1, 1]} : Finset Point), 0 ≤ a i) ∧ (∀ j ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, !₂[1, 1]} : Finset Point), 0 ≤ b j) ∧ (∑ i ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, !₂[1, 1]} : Finset Point), a i = 1) ∧ (∑ j ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, !₂[1, 1]} : Finset Point), b j = 1) ∧ x = ∑ i ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, !₂[1, 1]} : Finset Point), a i • i ∧ y = ∑ j ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, !₂[1, 1]} : Finset Point), b j • j := by
          have hxy_comb : ∀ x : Point, x ∈ convexHull ℝ ({V_point, sigma V_point, Y_point, sigma Y_point, !₂[1, 1]} : Set Point) → ∃ (a : Point → ℝ), (∀ i ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, !₂[1, 1]} : Finset Point), 0 ≤ a i) ∧ (∑ i ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, !₂[1, 1]} : Finset Point), a i = 1) ∧ x = ∑ i ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, !₂[1, 1]} : Finset Point), a i • i := by
            intro x hx;
            rw [ convexHull_eq ] at hx;
            obtain ⟨ ι, t, w, z, hw, hw', hz, rfl ⟩ := hx;
            refine ⟨ fun i => ∑ j ∈ t.filter ( fun j => z j = i ), w j, ?_, ?_, ?_ ⟩;
            · exact fun i hi => Finset.sum_nonneg fun j hj => hw j <| Finset.mem_filter.mp hj |>.1;
            · rw [ ← hw', Finset.sum_fiberwise_of_maps_to ];
              aesop;
            · simp +decide [ Finset.centerMass, hw' ];
              simp +decide [ Finset.sum_filter, Finset.sum_smul ];
              rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
          exact Exists.elim ( hxy_comb x hx ) fun a ha => Exists.elim ( hxy_comb y hy ) fun b hb => ⟨ a, b, ha.1, hb.1, ha.2.1, hb.2.1, ha.2.2, hb.2.2 ⟩;
        obtain ⟨ a, b, ha, hb, ha_sum, hb_sum, rfl, rfl ⟩ := hxy_comb;
        have hxy_comb : ∀ i ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, !₂[1, 1]} : Finset Point), ∀ j ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, !₂[1, 1]} : Finset Point), a i > 0 → b j > 0 → dist i j = 1 := by
          apply convex_combination_dist_eq_one_implies_support_dist_eq_one;
          all_goals try assumption;
          intros i hi j hj;
          have hxy_comb : ∀ i ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, !₂[1, 1]} : Finset Point), ∀ j ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, !₂[1, 1]} : Finset Point), dist i j ≤ 1 := by
            intros i hi j hj;
            have hxy_comb : ∀ i ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, !₂[1, 1]} : Finset Point), ∀ j ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, !₂[1, 1]} : Finset Point), dist i j ≤ 1 := by
              intro i hi j hj
              have hxy_comb : i ∈ Region6_Total ∧ j ∈ Region6_Total := by
                exact ⟨ subset_convexHull ℝ _ <| by simpa using hi, subset_convexHull ℝ _ <| by simpa using hj ⟩
              exact Region6_Total_diameter_le_1 i j hxy_comb.1 hxy_comb.2;
            exact hxy_comb i hi j hj;
          exact hxy_comb i hi j hj;
        have hxy_comb : ∀ i ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, !₂[1, 1]} : Finset Point), ∀ j ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, !₂[1, 1]} : Finset Point), a i > 0 → b j > 0 → ({i, j} : Set Point) = {V_point, sigma V_point} := by
          intro i hi j hj hai hbj
          rcases hxy_segment3 i hi j hj (hxy_comb i hi j hj hai hbj) with
            ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rfl
          · exact Set.pair_comm _ _
        have hxy_comb : ({∑ i ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, !₂[1, 1]} : Finset Point), a i • i, ∑ j ∈ ({V_point, sigma V_point, Y_point, sigma Y_point, !₂[1, 1]} : Finset Point), b j • j} : Set Point) = {V_point, sigma V_point} := by
          apply support_implies_endpoints;
          any_goals tauto;
          exact ne_of_apply_ne ( fun p => p 0 ) ( by norm_num [ V_point, sigma ] ; nlinarith [ Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), Real.sqrt_nonneg 6, Real.sqrt_nonneg 2 ] );
        exact pair_eq_pair_iff.mp hxy_comb;
      exact hxy_segment3 x y hxy_segment.1 hxy_segment.2 hxy_dist
    have hL_segment3 : L = openSegment ℝ V_point (sigma V_point) := by
      cases hxy_segment3 <;> simp_all +decide [ openSegment_symm ]
    exact hL_segment3;
  -- By h_segment3, any unit segment L in Region6_Total must be segment3.
  have h_L_is_segment3 : ∀ L : Set Point, IsUnitSegment L → L ⊆ Region6_Total → L = openSegment ℝ V_point (sigma V_point) := by
    assumption;
  -- By h_L_is_segment3, any unit segment L in Region6_Total must be segment3. Since segment3 is in S_finite, L must intersect with segment3.
  intros L hL hL_subset
  have hL_segment3 : L = openSegment ℝ V_point (sigma V_point) := h_L_is_segment3 L hL hL_subset
  exact ⟨openSegment ℝ V_point (sigma V_point), by
    exact Or.inr <| Or.inr <| Or.inl rfl, by
    rw [ hL_segment3, Set.not_disjoint_iff ] ; norm_num [ openSegment ];
    exact ⟨ _, 1 / 2, by norm_num, 1 / 2, by norm_num, by norm_num, rfl ⟩⟩

/-
Define the separator function sep.
-/
noncomputable def sep (p : Point) : ℝ := (1 - V_point 1) * (p 1 - V_point 0) - (y1 - V_point 0) * (p 0 - V_point 1)

/-
Define linear forms L1 and L2.
-/
noncomputable def L1 (p : Point) : ℝ := p 0 + p 1 - (V_point 0 + V_point 1)

noncomputable def L2 (p : Point) : ℝ := y1 * (p 0 - x1) - p 1 * (1 - x1)

/-
L1 is 0 at V and sigma V, and non-negative at Y.
-/
lemma L1_V : L1 V_point = 0 := by
  unfold L1; ring;

lemma L1_sigma_V : L1 (sigma V_point) = 0 := by
  unfold L1 sigma; norm_num;
  ring

lemma L1_Y_ge_0 : L1 Y_point ≥ 0 := by
  -- By definition of $y1$, we know that $y1 \geq V_point 0 + V_point 1 - 1$.
  have hy1_ge : y1 ≥ V_point 0 + V_point 1 - 1 := by
    unfold y1 V_point;
    simp +zetaDelta at *;
    rw [ div_add_one, le_div_iff₀ ];
    · have := x1_prop.2.1;
      nlinarith [ show Real.sqrt 6 > 2 by norm_num [ Real.lt_sqrt ], show Real.sqrt 2 > 1 by norm_num [ Real.lt_sqrt ], Real.mul_self_sqrt ( show 6 ≥ 0 by norm_num ), Real.mul_self_sqrt ( show 2 ≥ 0 by norm_num ), pow_two_nonneg ( Real.sqrt 6 - Real.sqrt 2 ), pow_two_nonneg ( Real.sqrt 6 - 2 ), pow_two_nonneg ( Real.sqrt 2 - 1 ) ];
    · have := x1_prop.2.1 ; norm_num at * ; nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ];
    · have := x1_prop.2.1 ; norm_num at * ; nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ];
  unfold L1; norm_num [ Y_point ] ; linarith;

/-
L2 is 0 at V and Y, and non-positive at sigma V.
-/
lemma L2_V : L2 V_point = 0 := by
  unfold L2;
  rw [ show y1 = V_point 1 * ( 1 - x1 ) / ( V_point 0 - x1 ) from rfl ];
  rw [ div_mul_cancel₀ _ ] <;> norm_num;
  nlinarith [ V_bounds, x1_prop ]

lemma L2_Y : L2 Y_point = 0 := by
  unfold L2 Y_point;
  -- Simplify the expression for L2 at Y.
  simp [y1]

lemma L2_sigma_V_le_0 : L2 (sigma V_point) ≤ 0 := by
  unfold L2 y1;
  erw [ div_mul_eq_mul_div, sub_le_iff_le_add ];
  rw [ div_le_iff₀ ] <;> norm_num [ V_point ] at *;
  · unfold sigma; norm_num; ring_nf; norm_num;
    have := x1_prop.1.le ; have := x1_prop.2.1.le ; norm_num at * ; nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_le_mul_of_nonneg_left this ( Real.sqrt_nonneg 6 ), mul_le_mul_of_nonneg_left this ( Real.sqrt_nonneg 2 ) ];
  · have := x1_prop;
    exact this.2.1.trans_le <| by nlinarith only [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt <| show 0 ≤ 6 by norm_num, Real.sq_sqrt <| show 0 ≤ 2 by norm_num, mul_pos ( Real.sqrt_pos.mpr <| show 0 < 6 by norm_num ) ( Real.sqrt_pos.mpr <| show 0 < 2 by norm_num ) ] ;

/-
The linear forms are strictly non-zero at the respective vertices.
-/
lemma L1_Y_pos : L1 Y_point > 0 := by
  -- Since $L1 Y_point$ is not zero and greater than or equal to zero, it must be strictly positive.
  apply lt_of_le_of_ne
  · exact L1_Y_ge_0
  · exact fun h => by
      unfold L1 at h; norm_num [ y1, V_point ] at h; ring_nf at h; norm_num at h;
      unfold Y_point at h ; norm_num at h;
      unfold y1 at h;
      unfold V_point at h ; norm_num at h;
      rw [ eq_comm, add_div', div_add', div_eq_iff ] at h <;> ring_nf at * <;> norm_num at *;
      · have := x1_prop.2.1;
        nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( sub_pos.mpr this ), mul_pos ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ( sub_pos.mpr this ) ];
      · have := x1_prop.1 ; have := x1_prop.2.1 ; norm_num at * ; nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ];
      · intro H; rw [ H ] at h; norm_num at h;
      · grind

lemma L2_sigma_V_neg : L2 (sigma V_point) < 0 := by
  unfold L2;
  unfold y1 sigma V_point;
  field_simp;
  refine mul_neg_of_pos_of_neg ?_ ?_;
  · linarith [ x1_prop.2.1 ];
  · rw [ sub_neg, div_lt_iff₀ ] <;> ring_nf <;> norm_num;
    · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), x1_prop ];
    · have := x1_prop.2.1 ; norm_num at * ; nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ]

lemma sep_V_neg : sep V_point < 0 := by
  unfold sep; norm_num [ V_point_0_val ] ; ring_nf ; norm_num;
  rw [ show V_point = !₂[(Real.sqrt 6 + Real.sqrt 2) / 4, (Real.sqrt 6 - Real.sqrt 2) / 4] by rfl ] ; norm_num ; ring_nf ; norm_num;
  rw [ show y1 = ( V_point 1 ) * ( 1 - x1 ) / ( V_point 0 - x1 ) by rfl ] ; norm_num [ V_point ] ; ring_nf ; norm_num;
  have h_x1_bounds : 0.95 < x1 ∧ x1 < 0.96 := by
    exact ⟨ x1_prop.1, x1_prop.2.1 ⟩;
  have h_sqrt_bounds : Real.sqrt 6 > 2.449 ∧ Real.sqrt 6 < 2.45 ∧ Real.sqrt 2 > 1.414 ∧ Real.sqrt 2 < 1.415 := by
    norm_num [ Real.lt_sqrt, Real.sqrt_lt ];
  field_simp at *;
  rw [ add_div', div_lt_div_iff_of_pos_right ] <;> nlinarith [ mul_pos ( sub_pos.mpr h_sqrt_bounds.1 ) ( sub_pos.mpr h_sqrt_bounds.2.2.1 ), Real.mul_self_sqrt ( show 6 ≥ 0 by norm_num ), Real.mul_self_sqrt ( show 2 ≥ 0 by norm_num ) ]

/-
Define linear forms L3 and L4.
-/
noncomputable def L3 (p : Point) : ℝ := y1 * (p 1 - x1) - p 0 * (1 - x1)

noncomputable def L4 (p : Point) : ℝ := p 0 + p 1 - (1 + y1)

/-
L3 is 0 at sigma V and sigma Y, and negative at Y.
-/
lemma L3_sigma_V : L3 (sigma V_point) = 0 := by
  simpa [L2, L3, sigma] using L2_V

lemma L3_sigma_Y : L3 (sigma Y_point) = 0 := by
  unfold L3 sigma Y_point;
  simp +zetaDelta at *;

lemma L3_Y_neg : L3 Y_point < 0 := by
  -- Substitute the value of L3 Y and use the fact that y1 < 1 to conclude it's negative.
  have h_L3_Y_val : L3 Y_point = y1 * (y1 - x1) - 1 * (1 - x1) := by
    unfold L3 Y_point; norm_num;
  nlinarith [ y1_bounds, x1_prop.1, x1_prop.2.1 ]

/-
L4 is 0 at Y and sigma Y, and negative at sigma V.
-/
lemma L4_Y : L4 Y_point = 0 := by
  unfold L4 Y_point; norm_num;

lemma L4_sigma_Y : L4 (sigma Y_point) = 0 := by
  unfold L4 sigma Y_point;
  ring_nf!;
  erw [ Matrix.cons_val_succ' ] ; norm_num

lemma L4_sigma_V_neg : L4 (sigma V_point) < 0 := by
  convert neg_lt_zero.mpr L1_Y_pos using 1 ; ring_nf!;
  unfold L4 L1; norm_num [ sigma ] ; ring_nf;
  unfold Y_point; norm_num; ring;

/-
sep is 0 at sigma V and Y.
-/
lemma sep_sigma_V : sep (sigma V_point) = 0 := by
  unfold sep;
  unfold y1; ring_nf;
  unfold sigma; norm_num; ring;

lemma sep_Y : sep Y_point = 0 := by
  unfold sep Y_point;
  simp +zetaDelta at *;
  ring

/-
If a point in the square satisfies L2 >= 0, it is in Region4.
-/
lemma Region4_contains_L2_ge_0 : ∀ p ∈ Region_Square, L2 p ≥ 0 → p ∈ Region4 := by
  intro p hp hL2op;
  apply in_Region4_of_coords p hp;
  · unfold L2 at hL2op;
    -- Since $y1 > 0$ and $1 - x1 > 0$, we can divide both sides of the inequality by $y1$ to get $p 0 - x1 \geq \frac{p 1 (1 - x1)}{y1}$.
    have h_div : p 0 - x1 ≥ p 1 * (1 - x1) / y1 := by
      rw [ ge_iff_le, div_le_iff₀ ] <;> linarith [ y1_bounds.1 ];
    linarith [ show 0 ≤ p 1 * ( 1 - x1 ) / y1 by exact div_nonneg ( mul_nonneg ( le_of_lt ( hp.2.2.1 ) ) ( sub_nonneg.2 ( by linarith [ show x1 < 1 by linarith [ show x1 < 0.96 by linarith [ x1_prop ] ] ] ) ) ) ( le_of_lt ( by linarith [ y1_bounds ] ) ) ];
  · unfold L2 at hL2op;
    -- Since $p$ is in the square, we know that $p_0 < 1$.
    have h_p0_lt_1 : p 0 < 1 := by
      exact hp.2.1;
    nlinarith [ show x1 > 0.95 by exact Classical.choose_spec exists_root_x1 |>.1, show x1 < 0.96 by exact Classical.choose_spec exists_root_x1 |>.2.1, show y1 > 0 by exact y1_bounds.1, show y1 < 1 by exact y1_bounds.2 ];
  · exact sub_nonneg.mp hL2op

/-
If a point in the square satisfies L3 >= 0, it is in Region5.
-/
lemma Region5_contains_L3_ge_0 : ∀ p ∈ Region_Square, L3 p ≥ 0 → p ∈ Region5 := by
  intros p hp hL3
  have hq : sigma p ∈ Region4 := by
    apply Region4_contains_L2_ge_0;
    · exact ⟨ hp.2.2.1, hp.2.2.2, hp.1, hp.2.1 ⟩;
    · exact hL3
  exact mem_Region5_iff_sigma_mem_Region4 p |>.2 hq

/-
If a point in the square satisfies L4 >= 0, it is in Region_Corner.
-/
lemma Region_Corner_contains_L4_ge_0 : ∀ p ∈ Region_Square, L4 p ≥ 0 → p ∈ Region_Corner := by
  intro p hp hL4
  apply in_Region_Corner_of_coords p hp (by
  unfold L4 at hL4; linarith!;)

/-
Define lambda_V, lambda_sigma_V, lambda_Y.
-/
noncomputable def lambda_V (p : Point) : ℝ := sep p / sep V_point

noncomputable def lambda_sigma_V (p : Point) : ℝ := L2 p / L2 (sigma V_point)

noncomputable def lambda_Y (p : Point) : ℝ := L1 p / L1 Y_point

/-
y1 * (V_point 0 - x1) = V_point 1 * (1 - x1).
-/
lemma y1_relation : y1 * (V_point 0 - x1) = V_point 1 * (1 - x1) := by
  unfold y1;
  rw [ div_mul_cancel₀ ];
  -- Since $V_point 0 > 0.96$ and $x1 < 0.96$, we have $V_point 0 - x1 > 0$.
  have h_pos : V_point 0 > 0.96 ∧ x1 < 0.96 := by
    exact ⟨ by have := V_bounds; norm_num at *; linarith, by have := x1_prop; norm_num at *; linarith ⟩
  linarith [h_pos.left, h_pos.right]

/-
The sum of the coefficients of p0 in the barycentric coordinates is 0.
-/
lemma lambda_sum_p0_coeff_eq_zero :
  (-(y1 - V_point 0)) / sep V_point + y1 / L2 (sigma V_point) + 1 / L1 Y_point = 0 := by
    have hrel : y1 * (V_point 0 - x1) - V_point 1 * (1 - x1) = 0 := by
      rw [y1_relation]
      ring
    have hsep : sep V_point ≠ 0 := ne_of_lt sep_V_neg
    have hL2 : L2 (sigma V_point) ≠ 0 := ne_of_lt L2_sigma_V_neg
    have hL1 : L1 Y_point ≠ 0 := ne_of_gt L1_Y_pos
    field_simp [hsep, hL2, hL1]
    unfold L1 L2 sep Y_point sigma at *
    norm_num at *
    ring_nf at hrel ⊢
    linear_combination
      ((1 + y1 - (V_point 0 + V_point 1)) * (V_point 0 - y1)) * hrel

/-
The sum of the coefficients of p1 in the barycentric coordinates is 0.
-/
lemma lambda_sum_p1_coeff_eq_zero :
  (1 - V_point 1) / sep V_point - (1 - x1) / L2 (sigma V_point) + 1 / L1 Y_point = 0 := by
    rw [ div_sub_div, div_add_div ];
    · unfold sep L2 L1 at *;
      unfold Y_point at *; norm_num at *; ring_nf at *;
      unfold sigma at *; norm_num at *; ring_nf at *;
      unfold y1; ring_nf at *;
      by_cases h : -x1 + V_point 0 = 0 <;> simp_all +decide [ sq, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ];
      · exact absurd h ( by linarith [ x1_prop, V_bounds ] );
      · grind;
    · exact mul_ne_zero ( by nlinarith [ sep_V_neg ] ) ( by nlinarith [ L2_sigma_V_neg ] );
    · exact ne_of_gt ( L1_Y_pos );
    · exact ne_of_lt ( by exact sep_V_neg );
    · exact ne_of_lt ( L2_sigma_V_neg )

/-
The sum of the barycentric coordinates at the origin is 1.
-/
lemma lambda_sum_at_O_point_eq_one : lambda_V O_point + lambda_sigma_V O_point + lambda_Y O_point = 1 := by
  unfold lambda_V lambda_sigma_V lambda_Y O_point;
  unfold sep L2 L1;
  rw [ div_add_div, div_add_div, div_eq_iff ] <;> norm_num [ V_point, y1, X_point, Y_point, sigma ];
  any_goals rw [ div_mul_eq_mul_div, div_sub', div_eq_iff ] <;> ring_nf <;> norm_num;
  -- By simplifying, we can see that the denominator is non-zero.
  focus
    have h_denom_nonzero : (Real.sqrt 6 + Real.sqrt 2) / 4 - x1 ≠ 0 := by
      -- By definition of $x1$, we know that $0.95 < x1 < 0.96$.
      have hx1_bounds : 0.95 < x1 ∧ x1 < 0.96 := by
        -- By definition of $x1$, we know that $0.95 < x1 < 0.96$.
        apply x1_prop.left |> fun h => ⟨h, x1_prop.right.left⟩;
      nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ];
  any_goals nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), x1_prop ];
  focus
    grind
  · constructor;
    · constructor;
      · rw [ div_sub', div_mul_eq_mul_div, sub_eq_zero ];
        · rw [ div_sub', div_mul_eq_mul_div, eq_div_iff ] <;> ring_nf <;> norm_num;
          · rw [ show ( 6 : ℝ ) = 3 * 2 by norm_num, Real.sqrt_mul ] <;> ring_nf <;> norm_num;
            nlinarith [ Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ), Real.sq_sqrt ( show 0 ≤ 2 by norm_num ), x1_prop.1, x1_prop.2.1, mul_pos ( Real.sqrt_pos.mpr ( show 0 < 3 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 0 < 2 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 0 < 3 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ), mul_pos ( Real.sqrt_pos.mpr ( show 0 < 2 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ) ];
          · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), x1_prop.1, x1_prop.2.1, x1_prop.2.2, mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ), mul_pos ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ) ];
          · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), x1_prop.1, x1_prop.2.1, x1_prop.2.2, mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ), mul_pos ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ) ];
        · norm_num;
      · rw [ div_mul_eq_mul_div, div_sub', div_eq_iff ] <;> ring_nf <;> norm_num;
        · have := x1_prop.2.2;
          unfold poly_X at this;
          grind;
        · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), x1_prop.1, x1_prop.2.1, x1_prop.2.2, mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ), mul_pos ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ) ];
        · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), x1_prop.1, x1_prop.2.1, x1_prop.2.2, mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ), mul_pos ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ) ];
    · rw [ add_div', div_sub', div_eq_iff ] <;> ring_nf <;> norm_num;
      · have := x1_prop.2.1;
        nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( sub_pos.mpr this ), mul_pos ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ( sub_pos.mpr this ) ];
      · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), x1_prop.1, x1_prop.2.1, x1_prop.2.2, mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ), mul_pos ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ) ];
      · have := x1_prop.2.1 ; norm_num at this ; nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ];
      · have := x1_prop.2.1 ; norm_num at this ; nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ];
  · constructor;
    · rw [ div_sub', div_mul_eq_mul_div, sub_eq_zero ];
      · rw [ div_sub', div_mul_eq_mul_div, eq_div_iff ] <;> ring_nf <;> norm_num;
        · rw [ show ( 6 : ℝ ) = 3 * 2 by norm_num, Real.sqrt_mul ] <;> ring_nf <;> norm_num;
          nlinarith [ Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ), Real.sq_sqrt ( show 0 ≤ 2 by norm_num ), x1_prop.1, x1_prop.2.1, mul_pos ( Real.sqrt_pos.mpr ( show 0 < 3 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 0 < 2 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 0 < 3 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ), mul_pos ( Real.sqrt_pos.mpr ( show 0 < 2 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ) ];
        · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), x1_prop.1, x1_prop.2.1, x1_prop.2.2, mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ), mul_pos ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ) ];
        · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), x1_prop.1, x1_prop.2.1, x1_prop.2.2, mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ), mul_pos ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ) ];
      · norm_num;
    · rw [ div_mul_eq_mul_div, div_sub', div_eq_iff ] <;> ring_nf <;> norm_num;
      · have := x1_prop.2.2;
        unfold poly_X at this;
        grind;
      · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), x1_prop.1, x1_prop.2.1, x1_prop.2.2, mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ), mul_pos ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ) ];
      · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), x1_prop.1, x1_prop.2.1, x1_prop.2.2, mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ), mul_pos ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ) ];
  · rw [ add_div', div_sub', div_eq_iff ] <;> ring_nf <;> norm_num;
    · have := x1_prop.2.1;
      nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( sub_pos.mpr this ), mul_pos ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ( sub_pos.mpr this ) ];
    · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), x1_prop.1, x1_prop.2.1, x1_prop.2.2, mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ), mul_pos ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ) ];
    · have := x1_prop.2.1 ; norm_num at this ; nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ];
    · have := x1_prop.2.1 ; norm_num at this ; nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ];
  · rw [ div_sub', div_mul_eq_mul_div, sub_eq_zero ];
    · rw [ div_sub', div_mul_eq_mul_div, eq_div_iff ] <;> ring_nf <;> norm_num;
      · rw [ show ( 6 : ℝ ) = 3 * 2 by norm_num, Real.sqrt_mul ] <;> ring_nf <;> norm_num;
        nlinarith [ Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ), Real.sq_sqrt ( show 0 ≤ 2 by norm_num ), x1_prop.1, x1_prop.2.1, mul_pos ( Real.sqrt_pos.mpr ( show 0 < 3 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 0 < 2 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 0 < 3 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ), mul_pos ( Real.sqrt_pos.mpr ( show 0 < 2 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ) ];
      · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), x1_prop.1, x1_prop.2.1, x1_prop.2.2, mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ), mul_pos ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ) ];
      · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), x1_prop.1, x1_prop.2.1, x1_prop.2.2, mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ), mul_pos ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ( sub_pos.mpr x1_prop.1 ) ];
    · norm_num;
  · have := x1_prop.2.2;
    unfold poly_X at this;
    grind

/-
The sum of the barycentric coordinates is 1 for any point p.
-/
lemma lambda_sum_eq_one (p : Point) : lambda_V p + lambda_sigma_V p + lambda_Y p = 1 := by
  have h_sum : ∀ p : Point, lambda_V p + lambda_sigma_V p + lambda_Y p = lambda_V O_point + lambda_sigma_V O_point + lambda_Y O_point + (p 0 - O_point 0) * ((-(y1 - V_point 0)) / sep V_point + y1 / L2 (sigma V_point) + 1 / L1 Y_point) + (p 1 - O_point 1) * ((1 - V_point 1) / sep V_point - (1 - x1) / L2 (sigma V_point) + 1 / L1 Y_point) := by
    intros p; unfold lambda_V; unfold lambda_sigma_V; unfold lambda_Y; unfold O_point; ring_nf;
    unfold sep L2 L1; ring;
  rw [ h_sum p, lambda_sum_at_O_point_eq_one, lambda_sum_p0_coeff_eq_zero, lambda_sum_p1_coeff_eq_zero ] ; ring

/-
The coefficient of p0 in the barycentric expansion of p0 is 1.
-/
lemma p0_coeff_p0 : (-(y1 - V_point 0)) / sep V_point * V_point 0 + y1 / L2 (sigma V_point) * (sigma V_point) 0 + 1 / L1 Y_point * Y_point 0 = 1 := by
  field_simp;
  rw [ neg_div', div_add_div, div_add_div ];
  · rw [ div_eq_iff ];
    · unfold L1 L2 sep Y_point sigma V_point x1;
      rw [ show y1 = ( ( Real.sqrt 6 - Real.sqrt 2 ) / 4 ) * ( 1 - Classical.choose exists_root_x1 ) / ( ( Real.sqrt 6 + Real.sqrt 2 ) / 4 - Classical.choose exists_root_x1 ) from rfl ];
      by_cases h : ( Real.sqrt 6 + Real.sqrt 2 ) / 4 - Classical.choose exists_root_x1 = 0 <;> simp_all +decide [ sub_eq_iff_eq_add ];
      · have := Classical.choose_spec exists_root_x1;
        nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ];
      · grind;
    · exact mul_ne_zero ( mul_ne_zero ( by linarith [ sep_V_neg ] ) ( by linarith [ L2_sigma_V_neg ] ) ) ( by linarith [ L1_Y_pos ] );
  · exact mul_ne_zero ( by linarith [ sep_V_neg ] ) ( by linarith [ L2_sigma_V_neg ] );
  · exact ne_of_gt ( L1_Y_pos );
  · exact ne_of_lt ( by exact sep_V_neg );
  · exact ne_of_lt ( L2_sigma_V_neg )

/-
sep V_point is equal to (V_point 1 - V_point 0) times L1 Y_point.
-/
lemma sep_eq_L1_mul_diff : sep V_point = (V_point 1 - V_point 0) * L1 Y_point := by
  unfold L1 sep; ring_nf;
  unfold Y_point; ring_nf;
  norm_num +zetaDelta at *;
  ring

/-
L2 (sigma V_point) can be factored into terms involving x1 and V_point coordinates.
-/
lemma L2_sigma_V_eq : L2 (sigma V_point) = (1 - x1) / (V_point 0 - x1) * (V_point 1 - V_point 0) * (V_point 1 + V_point 0 - x1) := by
  -- Substitute the values of sigma V_point into L2.
  have h_sub : L2 (sigma V_point) = y1 * (V_point 1 - x1) - V_point 0 * (1 - x1) := by
    exact rfl;
  -- Substitute the value of y1 into the expression for L2 at sigma V_point.
  have hy1 : y1 = V_point 1 * (1 - x1) / (V_point 0 - x1) := by
    exact rfl;
  by_cases hx : V_point 0 = x1
  · simp_all +decide [sub_eq_iff_eq_add]
    exact absurd hy1 (by linarith [y1_bounds])
  · rw [h_sub, hy1]
    field_simp [sub_ne_zero_of_ne hx]
    ring

/-
L1 Y_point can be factored into terms involving x1 and V_point coordinates.
-/
lemma L1_Y_point_eq : L1 Y_point = (1 - V_point 0) * (V_point 1 + V_point 0 - x1) / (V_point 0 - x1) := by
  unfold L1 Y_point x1;
  rw [ eq_div_iff ];
  · -- Substitute y1 from the equation y1 = V_point 1 * (1 - x1) / (V_point 0 - x1) into the left-hand side.
    have hy1 : y1 = V_point 1 * (1 - Classical.choose exists_root_x1) / (V_point 0 - Classical.choose exists_root_x1) := by
      exact rfl;
    rw [ eq_div_iff ] at hy1 <;> norm_num at *;
    · linarith;
    · intro h; norm_num [ h ] at hy1;
      exact absurd hy1 ( ne_of_gt ( y1_bounds.1 ) );
  · have := Classical.choose_spec exists_root_x1;
    norm_num [ V_point ] at *;
    nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ]

/-
The coefficient of p1 in the barycentric expansion of p0 is 0.
-/
lemma p1_coeff_p0 : (1 - V_point 1) / sep V_point * V_point 0 + (-(1 - x1)) / L2 (sigma V_point) * (sigma V_point) 0 + 1 / L1 Y_point * Y_point 0 = 0 := by
  rw [ div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div ];
  rw [ div_add_div, div_add_div, div_eq_iff ] <;> ring_nf!;
  any_goals nlinarith [ sep_V_neg, L2_sigma_V_neg, L1_Y_pos ];
  · rw [ show L2 ( sigma V_point ) = ( 1 - x1 ) / ( V_point 0 - x1 ) * ( V_point 1 - V_point 0 ) * ( V_point 1 + V_point 0 - x1 ) by exact
    L2_sigma_V_eq ];
    rw [ show sep V_point = ( V_point 1 - V_point 0 ) * L1 Y_point by exact sep_eq_L1_mul_diff ] ; ring_nf;
    field_simp;
    norm_num [ show L1 Y_point = ( 1 - V_point 0 ) * ( V_point 1 + V_point 0 - x1 ) / ( V_point 0 - x1 ) by
                exact L1_Y_point_eq ] ; ring_nf;
    rw [ show Y_point 0 = 1 by rfl ] ; ring_nf;
    norm_num;
  · exact mul_ne_zero ( mul_ne_zero ( ne_of_lt ( sep_V_neg ) ) ( ne_of_lt ( L2_sigma_V_neg ) ) ) ( ne_of_gt ( L1_Y_pos ) )

/-
A lemma stating that if S blocks two closed regions R1 and R2, and the intersection R1 ∩ R2 is covered by S (except possibly at "corner" points where segments cannot cross), then S blocks R1 ∪ R2.
-/
lemma blocking_union_lemma {S : Set (Set Point)} {R1 R2 : Set Point}
    (hR1 : IsClosed R1) (hR2 : IsClosed R2)
    (h1 : IsBlocking S R1) (h2 : IsBlocking S R2)
    (h_cover : ∀ x ∈ R1 ∩ R2, (∃ s ∈ S, x ∈ s) ∨ (∀ L, IsUnitSegment L → L ⊆ R1 ∪ R2 → x ∈ L → L ⊆ R1 ∨ L ⊆ R2)) :
    IsBlocking S (R1 ∪ R2) := by
      intro L hLL_sub hL_inter
      by_cases hL_R1 : L ⊆ R1;
      · exact h1 _ hLL_sub hL_R1;
      · by_cases hL_R2 : L ⊆ R2;
        · exact h2 _ hLL_sub hL_R2;
        · -- Since L is not in R1 and not in R2, it must intersect R1 ∩ R2.
          obtain ⟨x, hx⟩ : ∃ x, x ∈ L ∧ x ∈ R1 ∩ R2 := by
            simp_all +decide [ Set.subset_def ];
            -- Since L is connected and R1 and R2 are closed, L must intersect R1 ∩ R2.
            have h_connected : IsConnected L := by
              obtain ⟨ A, B, hAB, hL ⟩ := hLL_sub;
              convert isConnected_Ioo ( show ( 0 : ℝ ) < 1 by norm_num ) using 1;
              constructor <;> intro h <;> have := h.isPreconnected <;> simp_all +decide [ openSegment_eq_image ];
              · exact isConnected_Ioo ( by norm_num );
              · exact h.image _ ( Continuous.continuousOn <| by continuity )
            have h_connected : IsConnected L := by
              exact h_connected
            have h_inter : ∃ z ∈ L, z ∈ R1 ∩ R2 := by
              have h_inter : IsPreconnected L := by
                exact h_connected.isPreconnected;
              contrapose! h_inter;
              simp_all +decide [ IsPreconnected ];
              use Set.univ \ R2, isOpen_univ.sdiff hR2, Set.univ \ R1, isOpen_univ.sdiff hR1;
              simp_all +decide [ Set.Nonempty ];
              exact ⟨ fun x hx => by cases hL_inter x hx <;> aesop, fun x hx hx' => by cases hL_inter x hx <;> aesop ⟩
            obtain ⟨ z, hz₁, hz₂ ⟩ := h_inter
            use z;
            exact ⟨ hz₁, hz₂.1, hz₂.2 ⟩;
          cases h_cover x hx.2 <;> simp_all +decide [ Set.disjoint_left ];
          · exact ⟨ _, ‹∃ s ∈ S, x ∈ s›.choose_spec.1, _, ‹∃ s ∈ S, x ∈ s›.choose_spec.2, hx.1 ⟩;
          · grind

/-
Define L_OV and prove it is positive at sigma V.
-/
noncomputable def L_OV (p : Point) : ℝ :=
  -(V_point 1) * p 0 + (V_point 0) * p 1

lemma L_OV_sigmaV_pos : L_OV (sigma V_point) > 0 := by
  unfold L_OV V_point;
  unfold sigma; norm_num; nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ) ] ;

/-
The linear form L_OV is negative at X.
-/
lemma L_OV_X_neg : L_OV X_point < 0 := by
  unfold L_OV X_point;
  rw [ show V_point = !₂[ ( Real.sqrt 6 + Real.sqrt 2 ) / 4, ( Real.sqrt 6 - Real.sqrt 2 ) / 4 ] from rfl ] ; norm_num ; ring_nf;
  exact lt_trans ( by norm_num ) ( x1_prop.1 )

/-
Region2 lies in the non-positive half-plane of L_OV.
-/
lemma Region2_sub_H_neg : ∀ p ∈ Region2, L_OV p ≤ 0 := by
  intro p hp
  have h_convex : ∃ (a b c : ℝ), a + b + c = 1 ∧ 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ p = a • O_point + b • V_point + c • X_point := by
    rw [Region2] at hp
    generalize_proofs at *;
    rw [ convexHull_insert ] at hp;
    · norm_num [ segment_eq_image ] at hp;
      obtain ⟨ i, hi, x, hx, rfl ⟩ := hp; exact ⟨ 1 - x, x * ( 1 - i ), x * i, by ring, by nlinarith, by nlinarith, by nlinarith, by ext ; simpa using by ring ⟩ ;
    · norm_num +zetaDelta at *
  generalize_proofs at *;
  -- Substitute p into L_OV and simplify using the convex combination.
  obtain ⟨a, b, c, habc, ha, hb, hc, hp_eq⟩ := h_convex
  have hL_OV : L_OV p = a * L_OV O_point + b * L_OV V_point + c * L_OV X_point := by
    unfold L_OV; norm_num [ hp_eq ] ; ring;
  -- Since $L_OV(O) = 0$ and $L_OV(V) = 0$, the expression simplifies to $c * L_OV(X)$.
  have hL_OV_simplified : L_OV p = c * L_OV X_point := by
    -- Substitute the values of L_OV at O and V into the equation.
    have hL_OV_values : L_OV O_point = 0 ∧ L_OV V_point = 0 := by
      unfold L_OV; norm_num [ O_point, V_point ] ; ring;
    generalize_proofs at *;
    rw [hL_OV, hL_OV_values.left, hL_OV_values.right]
    simp +decide [mul_zero, add_zero]
  generalize_proofs at *; (
  exact hL_OV_simplified.symm ▸ mul_nonpos_of_nonneg_of_nonpos hc ( le_of_lt ( L_OV_X_neg ) ) |> le_trans <| by norm_num;)

/-
Define weights and intersection point, and prove weights are positive.
-/
noncomputable def w_sigmaV : ℝ := L_OV (sigma V_point)

noncomputable def w_X : ℝ := -L_OV X_point

noncomputable def s_cross : ℝ := w_X / (w_sigmaV + w_X)

noncomputable def I_cross : Point := s_cross • (sigma V_point) + (1 - s_cross) • X_point

lemma w_pos : w_sigmaV > 0 ∧ w_X > 0 := by
  exact ⟨ L_OV_sigmaV_pos, neg_pos_of_neg L_OV_X_neg ⟩

/-
Prove that s_cross is strictly between 0 and 1.
-/
lemma s_cross_bounds : 0 < s_cross ∧ s_cross < 1 := by
  have h_s_cross_bounds : 0 < s_cross ∧ s_cross < 1 := by
    have h_w_sigmaV_pos : 0 < w_sigmaV := by
      apply (w_pos).left.trans_le' ( by norm_num )
    have h_w_X_pos : 0 < w_X := by
      exact neg_pos_of_neg ( L_OV_X_neg )
    unfold s_cross; exact ⟨ by positivity, by rw [ div_lt_iff₀ ( by positivity ) ] ; linarith ⟩ ;
  exact h_s_cross_bounds

/-
Prove that L_OV vanishes at I_cross.
-/
lemma L_OV_I_cross : L_OV I_cross = 0 := by
  have hden : w_sigmaV + w_X ≠ 0 := ne_of_gt (add_pos w_pos.1 w_pos.2)
  have hlin :
      L_OV I_cross =
        s_cross * L_OV (sigma V_point) + (1 - s_cross) * L_OV X_point := by
    unfold L_OV I_cross
    norm_num [sub_smul]
    ring_nf
  rw [hlin]
  rw [show L_OV (sigma V_point) = w_sigmaV by rfl]
  rw [show L_OV X_point = -w_X by unfold w_X; ring]
  unfold s_cross
  field_simp [hden]
  ring

/-
The intersection point I_cross lies in the open segment between O and V.
-/
lemma I_cross_in_segment_OV : I_cross ∈ openSegment ℝ O_point V_point := by
  -- By definition of $I_cross$, we know that $I_cross = k • V$ for some $k \in (0, 1)$.
  obtain ⟨k, hk⟩ : ∃ k : ℝ, 0 < k ∧ k < 1 ∧ I_cross = k • V_point := by
    -- By definition of $I_cross$, we know that $I_cross = k • V$ for some $k \in (0, 1)$. We can solve for $k$ using the coordinates of $I_cross$ and $V$.
    obtain ⟨k, hk⟩ : ∃ k : ℝ, I_cross = k • V_point := by
      have hL_OV_I_cross : L_OV I_cross = 0 := by
        exact L_OV_I_cross;
      unfold L_OV at hL_OV_I_cross;
      use I_cross 0 / V_point 0;
      ext i; fin_cases i <;> norm_num <;> rw [ div_mul_eq_mul_div, eq_div_iff ] <;> linarith! [ V_bounds ] ;
    refine ⟨ k, ?_, ?_, hk ⟩;
    · have hcoord0 := congrArg (fun p : Point => p 0) hk;
      have hcoord1 := congrArg (fun p : Point => p 1) hk;
      norm_num [ I_cross, s_cross ] at *;
      unfold sigma at *; unfold X_point at *; unfold V_point at *; norm_num at *;
      nlinarith [ show 0 < w_X / ( w_sigmaV + w_X ) by exact div_pos ( by exact neg_pos.mpr ( L_OV_X_neg ) ) ( by linarith [ w_pos ] ), show 0 < ( Real.sqrt 6 - Real.sqrt 2 ) / 4 by exact div_pos ( sub_pos.mpr ( Real.lt_sqrt_of_sq_lt ( by norm_num ) ) ) ( by norm_num ), show 0 < ( Real.sqrt 6 + Real.sqrt 2 ) / 4 by positivity ];
    · have hcoord0 := congrArg (fun p : Point => p 0) hk;
      norm_num [ I_cross ] at hcoord0;
      unfold sigma at hcoord0; unfold X_point at hcoord0; norm_num at hcoord0;
      nlinarith! [ s_cross_bounds, V_bounds, x1_prop ];
  -- Since $0 < k < 1$, we can write $I_cross$ as $(1 - k) • O_point + k • V_point$, which is in the open segment between $O_point$ and $V_point$.
  have h_open_segment : I_cross = (1 - k) • O_point + k • V_point := by
    rw [ hk.2.2, show O_point = 0 from by ext i; fin_cases i <;> rfl ] ; norm_num;
  exact ⟨ 1 - k, k, by norm_num; linarith, by linarith, by norm_num [ h_open_segment ] ⟩

/-
Express X as an affine combination of I_cross and sigma V.
-/
lemma X_eq_affine_I_sigmaV : X_point = (1 / (1 - s_cross)) • I_cross - (s_cross / (1 - s_cross)) • (sigma V_point) := by
  by_cases h : 1 - s_cross = 0 <;> simp_all +decide [ div_eq_inv_mul, smul_smul ];
  · exact absurd h ( by linarith [ s_cross_bounds.2 ] );
  · rw [ show I_cross = s_cross • sigma V_point + ( 1 - s_cross ) • X_point by ext i; fin_cases i <;> norm_num [ I_cross ] ] ; ext i ; fin_cases i <;> norm_num [ h ] <;> ring

/-
If a linear combination of weights is non-negative, then a related coefficient inequality holds.
-/
lemma coeff_ineq (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (hL : c * w_sigmaV - d * w_X ≥ 0) :
  c - d * (s_cross / (1 - s_cross)) ≥ 0 := by
    field_simp;
    rw [ le_sub_comm, div_le_iff₀ ];
    · rw [ show s_cross = w_X / ( w_sigmaV + w_X ) by rfl ];
      rw [ mul_sub, mul_div, mul_one, div_le_iff₀ ] <;> nlinarith [ w_pos, mul_div_cancel₀ w_X ( by linarith [ w_pos ] : ( w_sigmaV + w_X ) ≠ 0 ) ];
    · linarith [ s_cross_bounds ]

/-
Any point in the convex hull of {O, V, sigma V, X} with non-negative L_OV value lies in Region1.
-/
lemma convexHull_sub_Region1_of_pos :
  ∀ p ∈ convexHull ℝ {O_point, V_point, sigma V_point, X_point}, L_OV p ≥ 0 → p ∈ Region1 := by
    intro p hp hp_nonneg_nonneg
    obtain ⟨a, b, c, d, ha, hb, hc, hd, habcd⟩ : ∃ a b c d : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ a + b + c + d = 1 ∧ p = a • O_point + b • V_point + c • sigma V_point + d • X_point := by
      norm_num [ convexHull_insert ] at hp;
      norm_num [ segment_eq_image ] at hp;
      rcases hp with ⟨ a, ⟨ ha₁, ha₂ ⟩, b, ⟨ hb₁, hb₂ ⟩, c, ⟨ hc₁, hc₂ ⟩, rfl ⟩ ; exact ⟨ 1 - c, c * ( 1 - b ), c * b * ( 1 - a ), c * b * a, by linarith, by nlinarith, by nlinarith [ mul_nonneg hc₁ hb₁ ], by nlinarith [ mul_nonneg hc₁ hb₁ ], by linarith, by ext i; fin_cases i <;> norm_num <;> ring ⟩ ;
    -- Substitute X using X_eq_affine_I_sigmaV:
    have hp_subst : p = a • O_point + b • V_point + (d / (1 - s_cross)) • I_cross + (c - d * (s_cross / (1 - s_cross))) • (sigma V_point) := by
      rw [ habcd.2, X_eq_affine_I_sigmaV ] ; ring_nf;
      ext ; norm_num ; ring;
    -- Since $I_cross$ is in the convex hull of $\{O, V\}$, we can write $I_cross$ as a convex combination of $O$ and $V$.
    obtain ⟨α, β, hα, hβ, hαβ⟩ : ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ α + β = 1 ∧ I_cross = α • O_point + β • V_point := by
      have hI_cross_convex : I_cross ∈ openSegment ℝ O_point V_point := by
        exact I_cross_in_segment_OV;
      rcases hI_cross_convex with ⟨ α, β, hα, hβ, hab, h ⟩ ; exact ⟨ α, β, hα.le, hβ.le, hab, h ▸ by ring_nf ⟩ ;
    -- Substitute $I_cross$ into the expression for $p$:
    have hp_final : p = (a + d / (1 - s_cross) * α) • O_point + (b + d / (1 - s_cross) * β) • V_point + (c - d * (s_cross / (1 - s_cross))) • (sigma V_point) := by
      convert hp_subst using 1 ; rw [ hαβ.2 ] ; ext ; norm_num ; ring;
    -- The coefficients of $O$, $V$, and $\sigma V$ in the expression for $p$ are non-negative and sum to 1.
    have h_coeff_nonneg : 0 ≤ a + d / (1 - s_cross) * α ∧ 0 ≤ b + d / (1 - s_cross) * β ∧ 0 ≤ c - d * (s_cross / (1 - s_cross)) ∧ (a + d / (1 - s_cross) * α) + (b + d / (1 - s_cross) * β) + (c - d * (s_cross / (1 - s_cross))) = 1 := by
      refine ⟨ ?_, ?_, ?_, ?_ ⟩;
      · exact add_nonneg ha ( mul_nonneg ( div_nonneg hd ( sub_nonneg.mpr ( by linarith [ s_cross_bounds ] ) ) ) hα );
      · exact add_nonneg hb ( mul_nonneg ( div_nonneg hd ( sub_nonneg.mpr ( by linarith [ s_cross_bounds ] ) ) ) hβ );
      · have h_coeff_nonneg : c * w_sigmaV - d * w_X ≥ 0 := by
          convert hp_nonneg_nonneg using 1 ; norm_num [ habcd.2, L_OV ] ; ring_nf;
          unfold w_sigmaV w_X; ring_nf;
          unfold L_OV; ring_nf;
          unfold O_point; norm_num;
        convert coeff_ineq c d hc hd h_coeff_nonneg using 1;
      · rw [ show α = 1 - β by linarith ] ; ring_nf;
        linarith [ inv_mul_cancel_left₀ ( show ( 1 - s_cross ) ≠ 0 by linarith [ s_cross_bounds ] ) d ];
    rw [hp_final];
    rw [Region1];
    rw [ convexHull_eq ];
    refine ⟨ Fin 3, { 0, 1, 2 }, fun i => if i = 0 then a + d / ( 1 - s_cross ) * α else if i = 1 then b + d / ( 1 - s_cross ) * β else c - d * ( s_cross / ( 1 - s_cross ) ), fun i => if i = 0 then O_point else if i = 1 then V_point else sigma V_point, ?_, ?_, ?_, ?_ ⟩ <;> simp +decide [ *, Fin.sum_univ_three, Finset.centerMass ];
    · linarith;
    · norm_num [ ← add_assoc, h_coeff_nonneg.2.2.2 ];
      norm_num [ show a + d / ( 1 - s_cross ) * α + b + d / ( 1 - s_cross ) * β + ( c - d * ( s_cross / ( 1 - s_cross ) ) ) = 1 by linarith ]

/-
Express sigma V as an affine combination of I_cross and X.
-/
lemma sigmaV_eq_affine_I_X : sigma V_point = (1 / s_cross) • I_cross - ((1 - s_cross) / s_cross) • X_point := by
  field_simp;
  rw [ show I_cross = s_cross • sigma V_point + ( 1 - s_cross ) • X_point by rfl ];
  ext i ; ring_nf;
  by_cases h : s_cross = 0 <;> simp_all +decide [ sub_smul, smul_smul ];
  · exact absurd h ( ne_of_gt ( s_cross_bounds.1 ) );
  · field_simp [h]
    ring

/-
Any point in the convex hull of {O, V, sigma V, X} with non-positive L_OV value lies in Region2.
-/
lemma convexHull_sub_Region2_of_neg :
  ∀ p ∈ convexHull ℝ {O_point, V_point, sigma V_point, X_point}, L_OV p ≤ 0 → p ∈ Region2 := by
    intro p hp hLull_subset_span;
    -- Since $p$ is in the convex hull of $\{O, V, \sigma V, X\}$, we can write it as a convex combination of these points.
    obtain ⟨a, b, c, d, ha, hb, hc, hd, habcd, hp_comb⟩ : ∃ a b c d : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ a + b + c + d = 1 ∧ p = a • O_point + b • V_point + c • sigma V_point + d • X_point := by
      rw [ convexHull_insert ] at hp;
      · norm_num [ segment_eq_image ] at hp;
        rcases hp with ⟨ q, hq, x, hx, rfl ⟩ ; rw [ convexHull_insert ] at hq <;> norm_num at hq ⊢;
        rcases hq with ⟨ y, hy, hq ⟩ ; rw [ segment_eq_image ] at hy hq; norm_num at hy hq ⊢;
        rcases hy with ⟨ y, ⟨ hy₀, hy₁ ⟩, rfl ⟩ ; rcases hq with ⟨ z, ⟨ hz₀, hz₁ ⟩, rfl ⟩ ; exact ⟨ 1 - x, by linarith, x * ( 1 - z ), by nlinarith, x * z * ( 1 - y ), by nlinarith [ mul_nonneg hx.1 hz₀ ], x * z * y, by nlinarith [ mul_nonneg hx.1 hz₀ ], by ring, by ext i; simpa using by ring ⟩ ;
      · norm_num +zetaDelta at *;
    -- Substitute sigma V using sigmaV_eq_affine_I_X:
    have hp_subst : p = a • O_point + b • V_point + (c / s_cross) • I_cross + (d - c * (1 - s_cross) / s_cross) • X_point := by
      convert hp_comb using 1;
      rw [ show sigma V_point = ( 1 / s_cross ) • I_cross - ( ( 1 - s_cross ) / s_cross ) • X_point from ?_ ]
      focus
        ext
      focus
        norm_num
      focus
        ring
      convert sigmaV_eq_affine_I_X using 1;
    -- We need to show that the coefficients of $I_cross$ and $X$ are non-negative.
    have h_coeff_nonneg : 0 ≤ c / s_cross ∧ 0 ≤ d - c * (1 - s_cross) / s_cross := by
      have h_coeff_nonneg : d * w_X - c * w_sigmaV ≥ 0 := by
        have h_coeff_nonneg : L_OV p = c * w_sigmaV - d * w_X := by
          unfold L_OV w_sigmaV w_X; norm_num [ hp_comb ] ; ring_nf;
          unfold L_OV; norm_num [ O_point, V_point, sigma, X_point ] ; ring;
        linarith;
      have h_coeff_nonneg : d - c * (1 - s_cross) / s_cross ≥ 0 := by
        have h_coeff_nonneg : d * s_cross - c * (1 - s_cross) ≥ 0 := by
          have h_coeff_nonneg : d * (w_X / (w_sigmaV + w_X)) - c * (1 - w_X / (w_sigmaV + w_X)) ≥ 0 := by
            have h_pos : 0 < w_sigmaV + w_X := by
              exact add_pos ( w_pos.1 ) ( w_pos.2 )
            field_simp [h_pos] at *; linarith;
          exact h_coeff_nonneg;
        rw [ sub_div', ge_iff_le, le_div_iff₀ ] <;> linarith [ s_cross_bounds.1, s_cross_bounds.2 ]
      exact ⟨div_nonneg hc (by
      exact div_nonneg ( by linarith [ w_pos ] ) ( by linarith [ w_pos ] )), h_coeff_nonneg⟩;
    -- Since $I_cross$ is in the convex hull of $\{O, V\}$, we can write it as a convex combination of $O$ and $V$.
    obtain ⟨e, f, he, hf, hef, hI_cross⟩ : ∃ e f : ℝ, 0 ≤ e ∧ 0 ≤ f ∧ e + f = 1 ∧ I_cross = e • O_point + f • V_point := by
      obtain ⟨e, he⟩ : ∃ e : ℝ, 0 ≤ e ∧ e ≤ 1 ∧ I_cross = e • O_point + (1 - e) • V_point := by
        have := I_cross_in_segment_OV;
        obtain ⟨ e, he, he' ⟩ := this;
        exact ⟨ e, he'.1.le, by linarith, by simpa [ ← he'.2.2.1 ] using he'.2.2.2.symm ⟩;
      exact ⟨ e, 1 - e, he.1, sub_nonneg.2 he.2.1, by ring, he.2.2 ⟩;
    -- Substitute hI_cross into hp_subst and simplify.
    have hp_simplified : p = (a + (c / s_cross) * e) • O_point + (b + (c / s_cross) * f) • V_point + (d - c * (1 - s_cross) / s_cross) • X_point := by
      convert hp_subst using 1 ; rw [ hI_cross ] ; ext ; norm_num ; ring;
    -- Since the coefficients sum to 1 and are non-negative, p is a convex combination of O, V, and X.
    have h_convex_comb : ∃ a' b' c' : ℝ, 0 ≤ a' ∧ 0 ≤ b' ∧ 0 ≤ c' ∧ a' + b' + c' = 1 ∧ p = a' • O_point + b' • V_point + c' • X_point := by
      use a + c / s_cross * e, b + c / s_cross * f, d - c * (1 - s_cross) / s_cross;
      refine ⟨ ?_, ?_, ?_, ?_, hp_simplified ⟩ <;> try nlinarith;
      rw [ ← eq_sub_iff_add_eq' ] at hef ; subst_vars ; ring_nf;
      rw [ mul_assoc, mul_inv_cancel₀ ( ne_of_gt ( show 0 < s_cross from by linarith [ s_cross_bounds ] ) ), mul_one ] ; linarith;
    obtain ⟨ a', b', c', ha', hb', hc', habcd', rfl ⟩ := h_convex_comb; exact (by
    rw [ show Region2 = convexHull ℝ { O_point, V_point, X_point } from rfl ];
    rw [ convexHull_eq ];
    refine ⟨ Fin 3, { 0, 1, 2 }, fun i => if i = 0 then a' else if i = 1 then b' else c', fun i => if i = 0 then O_point else if i = 1 then V_point else X_point, ?_, ?_, ?_, ?_ ⟩ <;> simp +decide [ *, Fin.sum_univ_three, Finset.centerMass ];
    · linarith;
    · simp +decide [ ← add_assoc, habcd' ] at * ; aesop ( simp_config := { singlePass := true } ) ;);

/-
L2 is zero at X.
-/
lemma L2_X : L2 X_point = 0 := by
  unfold L2 X_point; norm_num;

/-
L2 is positive at A0.
-/
lemma L2_A0_pos : L2 A_0 > 0 := by
  unfold L2 A_0;
  -- Substitute the values of y1 and x1 from their definitions.
  simp [y1, x1];
  refine mul_pos ?_ ?_;
  · refine div_pos ?_ ?_;
    · refine mul_pos ?_ ?_;
      · exact V_bounds.2.2.1.trans_le' <| by norm_num;
      · have := Classical.choose_spec exists_root_x1;
        norm_num at * ; linarith;
    · have := Classical.choose_spec exists_root_x1;
      exact sub_pos_of_lt ( by have := V_bounds; norm_num at *; linarith );
  · have := Classical.choose_spec exists_root_x1;
    norm_num at * ; linarith

/-
L2 is negative at O.
-/
lemma L2_O_neg : L2 O_point < 0 := by
  unfold L2; norm_num;
  unfold O_point x1 y1;
  have := Classical.choose_spec exists_root_x1; ( unfold V_point; norm_num; );
  rw [ div_mul_eq_mul_div, div_pos_iff ];
  refine Or.inl ⟨ ?_, ?_ ⟩;
  · exact mul_pos ( mul_pos ( by nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ) ] ) ( by unfold x1; norm_num; linarith ) ) ( by linarith );
  · unfold x1; nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ] ;

/-
L3 is zero at sigma X.
-/
lemma L3_sigma_X : L3 (sigma X_point) = 0 := by
  unfold L3 sigma X_point; norm_num;

/-
L3 is positive at sigma A0.
-/
lemma L3_sigma_A0_pos : L3 (sigma A_0) > 0 := by
  unfold L3 sigma A_0 ; norm_num;
  unfold y1 x1;
  refine mul_pos ?_ ?_;
  · refine div_pos ?_ ?_;
    · -- Since $V_point$ is in the open unit square, its coordinates are positive.
      have hV_pos : 0 < V_point 1 := by
        exact V_bounds.2.2.1.trans_le' <| by norm_num;
      exact mul_pos hV_pos ( sub_pos_of_lt ( by have := Classical.choose_spec exists_root_x1; nlinarith [ sq_nonneg ( ( Classical.choose exists_root_x1 ) ^ 2 - 1 ), sq_nonneg ( ( Classical.choose exists_root_x1 ) ^ 2 - 2 ), sq_nonneg ( ( Classical.choose exists_root_x1 ) ^ 2 - 3 ), sq_nonneg ( ( Classical.choose exists_root_x1 ) ^ 2 - 4 ) ] ) );
    · have := Classical.choose_spec exists_root_x1;
      exact sub_pos_of_lt ( by have := V_bounds; norm_num at *; linarith );
  · have := Classical.choose_spec exists_root_x1;
    norm_num at * ; linarith

/-
L3 is negative at O.
-/
lemma L3_O_neg : L3 O_point < 0 := by
  unfold L3;
  unfold y1 x1 O_point; norm_num;
  have hV_bounds : 0.96 < V_point 0 ∧ V_point 0 < 0.97 ∧ 0.25 < V_point 1 ∧ V_point 1 < 0.26 := by
    exact V_bounds
  generalize_proofs at *;
  have := Classical.choose_spec ‹∃ x : ℝ, 19 / 20 < x ∧ x < 24 / 25 ∧ poly_X x = 0›; norm_num [ poly_X ] at *; rw [ div_mul_eq_mul_div, lt_div_iff₀ ] <;> nlinarith;

/-
L2 is non-negative on Region4.
-/
lemma Region4_sub_L2_ge_0 : ∀ p ∈ Region4, L2 p ≥ 0 := by
  -- Since L2 is non-negative at all vertices of Region4, it is non-negative on the convex hull of these vertices.
  have h_L2_nonneg_vertices : ∀ p ∈ ({X_point, A_0, Y_point} : Set Point), L2 p ≥ 0 := by
    -- Since L2 is non-negative at X, A0, and Y, it is non-negative on the convex hull of these points.
    simp [L2_X, L2_A0_pos, L2_Y];
    exact le_of_lt ( L2_A0_pos );
  -- Since L2 is non-negative at all vertices of Region4, it is non-negative on the convex hull of these vertices by the properties of convex combinations.
  intros p hp
  have h_convex_comb : ∃ (a b c : ℝ), 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • X_point + b • A_0 + c • Y_point := by
    unfold Region4 at hp; simp_all +decide [ convexHull_insert ] ;
    rcases hp with ⟨ q, ⟨ a, b, ha, hb, hab, rfl ⟩, ⟨ c, d, hc, hd, hcd, rfl ⟩ ⟩ ; exact ⟨ c, hc, d * a, mul_nonneg hd ha, d * b, mul_nonneg hd hb, by nlinarith, by ext i; simpa using by ring ⟩ ;
  obtain ⟨ a, b, c, ha, hb, hc, habc, rfl ⟩ := h_convex_comb
  have h_aff :
      L2 (a • X_point + b • A_0 + c • Y_point) =
        a * L2 X_point + b * L2 A_0 + c * L2 Y_point := by
    unfold L2
    norm_num
    ring_nf
    have hsum :
        y1 * x1 = y1 * a * x1 + y1 * b * x1 + y1 * c * x1 := by
      calc
        y1 * x1 = (a + b + c) * (y1 * x1) := by
          rw [habc]
          ring
        _ = y1 * a * x1 + y1 * b * x1 + y1 * c * x1 := by
          ring
    rw [hsum]
    ring
  have hX := h_L2_nonneg_vertices X_point (by simp)
  have hA := h_L2_nonneg_vertices A_0 (by simp)
  have hY := h_L2_nonneg_vertices Y_point (by simp)
  calc
    L2 (a • X_point + b • A_0 + c • Y_point) =
        a * L2 X_point + b * L2 A_0 + c * L2 Y_point := h_aff
    _ ≥ 0 := by
      change 0 ≤ a * L2 X_point + b * L2 A_0 + c * L2 Y_point
      have h1 : 0 ≤ a * L2 X_point := mul_nonneg ha hX
      have h2 : 0 ≤ b * L2 A_0 := mul_nonneg hb hA
      have h3 : 0 ≤ c * L2 Y_point := mul_nonneg hc hY
      linarith

/-
L3 is non-negative on Region5.
-/
lemma Region5_sub_L3_ge_0 : ∀ p ∈ Region5, L3 p ≥ 0 := by
  intro p hp;
  -- Since $p$ is in the convex hull of $\{ \sigma X, \sigma A0, \sigma Y \}$, we can write $p$ as a convex combination of these points.
  obtain ⟨a, b, c, ha, hb, hc, habc, hp_comb⟩ : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • sigma X_point + b • sigma A_0 + c • sigma Y_point := by
    rw [ Region5 ] at hp;
    rw [ convexHull_insert ] at hp;
    · norm_num [ segment_eq_image ] at hp;
      rcases hp with ⟨ i, hi, x, hx, rfl ⟩ ; exact ⟨ 1 - x, x * ( 1 - i ), x * i, by linarith, by nlinarith, by nlinarith, by linarith, by ext ; simpa using by ring ⟩ ;
    · norm_num +zetaDelta at *;
  -- Since $L3$ is affine, we have $L3(p) = a * L3(\sigma X) + b * L3(\sigma A0) + c * L3(\sigma Y)$.
  have hL3_affine : L3 p = a * L3 (sigma X_point) + b * L3 (sigma A_0) + c * L3 (sigma Y_point) := by
    unfold L3; norm_num [ hp_comb ] ; ring_nf;
    linear_combination' habc * y1 * x1;
  -- Since $L3(\sigma X) = 0$, $L3(\sigma A0) > 0$, and $L3(\sigma Y) = 0$, we have $L3(p) = b * L3(\sigma A0)$.
  have hL3_simplified : L3 p = b * L3 (sigma A_0) := by
    rw [ hL3_affine, show L3 ( sigma X_point ) = 0 from ?_, show L3 ( sigma Y_point ) = 0 from ?_ ] <;> ring_nf;
    · exact L3_sigma_Y;
    · exact L3_sigma_X;
  exact hL3_simplified.symm ▸ mul_nonneg hb ( le_of_lt ( L3_sigma_A0_pos ) )

/-
Region2 is in the half-plane L2 <= 0. Region3 is in the half-plane L3 <= 0.
-/
lemma Region2_sub_L2_le_0 : ∀ p ∈ Region2, L2 p ≤ 0 := by
  intro p hp
  obtain ⟨a, b, c, ha, hb, hc, habc, hp_eq⟩ : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • O_point + b • V_point + c • X_point := by
    rw [ show Region2 = convexHull ℝ { O_point, V_point, X_point } from rfl ] at hp;
    norm_num [ convexHull_insert ] at hp;
    rcases hp with ⟨ q, ⟨ a, b, ha, hb, hab, rfl ⟩, ⟨ c, d, hc, hd, hcd, rfl ⟩ ⟩ ; use c, d * a, d * b; simp_all +decide [ segment_eq_image ] ; ring_nf;
    exact ⟨ mul_nonneg hd ha, mul_nonneg hd hb, by nlinarith, by rw [ mul_smul, mul_smul ] ; abel1 ⟩;
  -- Since $L2$ is affine, we have $L2(p) = a * L2(O) + b * L2(V) + c * L2(X)$.
  have hL2_affine : L2 p = a * L2 O_point + b * L2 V_point + c * L2 X_point := by
    unfold L2; norm_num [ hp_eq ] ; ring_nf;
    rw [ ← eq_sub_iff_add_eq' ] at habc ; subst habc ; ring;
  nlinarith [ L2_O_neg, L2_V, L2_X ]

lemma Region3_sub_L3_le_0 : ∀ p ∈ Region3, L3 p ≤ 0 := by
  -- Using the fact that L3 is linear and that L3(O) < 0, L3(sigma V) = 0, and L3(sigma X) = 0, we can show that L3(p) ≤ 0 for any point p in Region3.
  intros p hp
  have h_comb : ∃ t u v : ℝ, 0 ≤ t ∧ 0 ≤ u ∧ 0 ≤ v ∧ t + u + v = 1 ∧ p = t • O_point + u • sigma V_point + v • sigma X_point := by
    have h_convex_comb : p ∈ convexHull ℝ {O_point, sigma V_point, sigma X_point} := by
      exact hp;
    rw [ convexHull_insert ] at h_convex_comb;
    · norm_num [ segment_eq_image ] at h_convex_comb;
      rcases h_convex_comb with ⟨ i, hi, x, hx, rfl ⟩ ; exact ⟨ 1 - x, x * ( 1 - i ), x * i, by linarith, by nlinarith, by nlinarith, by linarith, by ext ; simpa using by ring ⟩ ;
    · norm_num +zetaDelta at *;
  obtain ⟨t, u, v, ht, hu, hv, hsum, hp_eq⟩ := h_comb
  have hL3 : L3 p = t * L3 O_point + u * L3 (sigma V_point) + v * L3 (sigma X_point) := by
    unfold L3; simp +decide [ hp_eq, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm ] ;
    grind;
  rw [hL3];
  exact add_nonpos ( add_nonpos ( mul_nonpos_of_nonneg_of_nonpos ht ( by exact le_of_lt ( by exact
    L3_O_neg ) ) ) ( mul_nonpos_of_nonneg_of_nonpos hu ( by exact le_of_eq ( by exact L3_sigma_V ) ) ) ) ( mul_nonpos_of_nonneg_of_nonpos hv ( by exact le_of_eq ( by exact
    L3_sigma_X ) ) )

/-
L3 is negative at V.
-/
lemma L3_V_neg : L3 V_point < 0 := by
  unfold L3 y1 V_point x1;
  field_simp;
  refine mul_neg_of_pos_of_neg ?_ ?_;
  · exact sub_pos_of_lt ( by have := Classical.choose_spec exists_root_x1; nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ) ] );
  · have := Classical.choose_spec exists_root_x1 ; norm_num;
    rw [ div_lt_iff₀ ] <;> norm_num at *;
    · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ];
    · nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ]

/-
We define an auxiliary polynomial and identify its roots. The roots are 1 and `V_point 0 + V_point 1 - 1`.
-/
noncomputable def poly_sep_aux (y : ℝ) : ℝ :=
  (1 - V_point 1) * (1 - V_point 0) - (y - V_point 0) * (y - V_point 1)

/-
The value of the separator function at `sigma Y_point` is equal to the value of the auxiliary polynomial at `y1`.
-/
lemma sep_sigma_Y_eq_poly : sep (sigma Y_point) = poly_sep_aux y1 := by
  exact rfl

/-
We show that the auxiliary polynomial can be factored as `(y - root1) * (1 - y)`.
-/
lemma poly_sep_aux_eq_factored (y : ℝ) :
  poly_sep_aux y = (y - (V_point 0 + V_point 1 - 1)) * (1 - y) := by
    unfold poly_sep_aux; ring;

/-
We prove that `V_point 0 + V_point 1 - 1` is strictly less than `y1`.
-/
lemma root1_lt_y1 : V_point 0 + V_point 1 - 1 < y1 := by
  unfold y1 V_point;
  rw [ lt_div_iff₀ ] <;> norm_num;
  · unfold x1;
    have := Classical.choose_spec exists_root_x1;
    nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( sub_pos.mpr this.1 ), mul_pos ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ( sub_pos.mpr this.1 ) ];
  · unfold x1;
    have := Classical.choose_spec exists_root_x1;
    nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ]

/-
The auxiliary polynomial is positive strictly between its roots.
-/
lemma poly_sep_aux_pos_of_between_roots (y : ℝ) (h1 : V_point 0 + V_point 1 - 1 < y) (h2 : y < 1) :
  poly_sep_aux y > 0 := by
    exact poly_sep_aux_eq_factored y ▸ mul_pos ( by linarith ) ( by linarith )

/-
The separator function is strictly positive at `sigma Y_point`.
-/
lemma sep_sigma_Y_pos : sep (sigma Y_point) > 0 := by
  rw [sep_sigma_Y_eq_poly]
  apply poly_sep_aux_pos_of_between_roots
  · exact root1_lt_y1
  · exact y1_bounds.2

/-
We define the barycentric coordinates for Region6b and verify their values at the vertices.
-/
noncomputable def mu_sigmaV (p : Point) : ℝ := L4 p / L4 (sigma V_point)

noncomputable def mu_Y (p : Point) : ℝ := L3 p / L3 Y_point

noncomputable def mu_sigmaY (p : Point) : ℝ := sep p / sep (sigma Y_point)

lemma mu_values :
  mu_sigmaV (sigma V_point) = 1 ∧ mu_sigmaV Y_point = 0 ∧ mu_sigmaV (sigma Y_point) = 0 ∧
  mu_Y (sigma V_point) = 0 ∧ mu_Y Y_point = 1 ∧ mu_Y (sigma Y_point) = 0 ∧
  mu_sigmaY (sigma V_point) = 0 ∧ mu_sigmaY Y_point = 0 ∧ mu_sigmaY (sigma Y_point) = 1 := by
  have hL4 : L4 (sigma V_point) ≠ 0 := ne_of_lt L4_sigma_V_neg
  have hL3 : L3 Y_point ≠ 0 := ne_of_lt L3_Y_neg
  have hsep : sep (sigma Y_point) ≠ 0 := ne_of_gt sep_sigma_Y_pos
  unfold mu_sigmaV mu_Y mu_sigmaY
  simp [L3_sigma_V, L3_sigma_Y, L4_Y, L4_sigma_Y, sep_sigma_V, sep_Y, hL4, hL3,
    hsep]

/-
We simplify the value of `L4` at `sigma V_point`.
-/
lemma val_L4_sigma_V : L4 (sigma V_point) = V_point 0 + V_point 1 - 1 - y1 := by
  unfold L4 sigma; ring!

/-
We simplify the value of `L3` at `Y_point`.
-/
lemma val_L3_Y : L3 Y_point = y1^2 - x1 * y1 + x1 - 1 := by
  unfold L3 Y_point; ring_nf;
  erw [ Matrix.cons_val_succ' ] ; norm_num ; ring

/-
We factor `L3 Y_point`.
-/
lemma L3_Y_factored : L3 Y_point = (y1 - 1) * (y1 + 1 - x1) := by
  rw [ val_L3_Y ] ; ring

/-
We prove an algebraic identity relating `x1`, `y1`, and `V_point` that is crucial for showing the coefficient of `p0` vanishes.
-/
lemma algebraic_identity_for_p0_coeff :
  (1 - V_point 0) * (y1 + 1 - x1) = (1 - x1) * (y1 - (V_point 0 + V_point 1 - 1)) := by
    -- By definition of y1, we have y1 * (V_point 0 - x1) = V_point 1 * (1 - x1).
    have h_y1_def : y1 * (V_point 0 - x1) = V_point 1 * (1 - x1) := by
      exact y1_relation
    generalize_proofs at *; (
    linarith! [ h_y1_def ] ;)

/-
We prove that the numerator of the coefficient of `p0` is zero, using the previously established algebraic identity.
-/
lemma numerator_p0_coeff_eq_zero :
  -(y1 - 1) * (y1 + 1 - x1) + (x1 - 1) * (y1 - (V_point 0 + V_point 1 - 1)) + (y1 - V_point 0) * (y1 + 1 - x1) = 0 := by
  calc
    -(y1 - 1) * (y1 + 1 - x1) + (x1 - 1) * (y1 - (V_point 0 + V_point 1 - 1)) + (y1 - V_point 0) * (y1 + 1 - x1)
        = (1 - V_point 0) * (y1 + 1 - x1) + (x1 - 1) * (y1 - (V_point 0 + V_point 1 - 1)) := by
      ring
    _ = (1 - x1) * (y1 - (V_point 0 + V_point 1 - 1)) + (x1 - 1) * (y1 - (V_point 0 + V_point 1 - 1)) := by
      rw [algebraic_identity_for_p0_coeff]
    _ = 0 := by
      ring

/-
The value of `L4` at `sigma V_point` is non-zero.
-/
lemma L4_sigma_V_ne_zero : L4 (sigma V_point) ≠ 0 := by
  rw [val_L4_sigma_V]
  have h : V_point 0 + V_point 1 - 1 < y1 := root1_lt_y1
  linarith

/-
We rewrite the values of `L4`, `L3`, and `sep` in forms convenient for finding a common denominator.
-/
lemma L4_sigma_V_eq_neg_root_diff : L4 (sigma V_point) = -(y1 - (V_point 0 + V_point 1 - 1)) := by
  rw [val_L4_sigma_V]
  ring

lemma L3_Y_eq_neg_factored : L3 Y_point = -(1 - y1) * (y1 + 1 - x1) := by
  rw [L3_Y_factored]
  ring

lemma sep_sigma_Y_eq_factored : sep (sigma Y_point) = (y1 - (V_point 0 + V_point 1 - 1)) * (1 - y1) := by
  rw [sep_sigma_Y_eq_poly, poly_sep_aux_eq_factored]

/-
The coefficient of `p0` in the sum of barycentric coordinates for Region6b is zero.
-/
lemma mu_sum_p0_coeff_eq_zero :
  1 / L4 (sigma V_point) + (x1 - 1) / L3 Y_point - (y1 - V_point 0) / sep (sigma Y_point) = 0 := by
    have h_common_denom : L4 (sigma V_point) ≠ 0 ∧ L3 Y_point ≠ 0 ∧ sep (sigma Y_point) ≠ 0 := by
      exact ⟨ by linarith [ show L4 ( sigma V_point ) < 0 from L4_sigma_V_neg ], by linarith [ show L3 Y_point < 0 from L3_Y_neg ], by linarith [ show sep ( sigma Y_point ) > 0 from sep_sigma_Y_pos ] ⟩;
    -- Substitute the factored forms of L4, L3, and sep into the coefficients.
    have h_coeff_p0 : (-(y1 - 1) * (y1 + 1 - x1) + (x1 - 1) * (y1 - (V_point 0 + V_point 1 - 1)) + (y1 - V_point 0) * (y1 + 1 - x1)) = 0 := by
      convert numerator_p0_coeff_eq_zero using 1;
    rw [ div_add_div, div_sub_div, div_eq_iff ] <;> simp_all +decide [ sub_eq_iff_eq_add ];
    -- Substitute the factored forms of L4, L3, and sep into the equation.
    have h_subst : (- (1 - y1) * (y1 + 1 - x1) + (-(y1 - (V_point 0 + V_point 1 - 1))) * (x1 - 1)) * ((y1 - (V_point 0 + V_point 1 - 1)) * (1 - y1)) = (-(y1 - (V_point 0 + V_point 1 - 1))) * (-(1 - y1) * (y1 + 1 - x1)) * (y1 - V_point 0) := by
      linear_combination -h_coeff_p0 * ( y1 - ( V_point 0 + V_point 1 - 1 ) ) * ( 1 - y1 );
    convert h_subst using 1 <;> push_cast [ L3_Y_eq_neg_factored, L4_sigma_V_eq_neg_root_diff, sep_sigma_Y_eq_factored ] <;> ring

/-
The coefficient of `p1` in the sum of barycentric coordinates for Region6b is zero.
-/
lemma mu_sum_p1_coeff_eq_zero :
  1 / L4 (sigma V_point) + y1 / L3 Y_point + (1 - V_point 1) / sep (sigma Y_point) = 0 := by
    have hrel : y1 * (V_point 0 - x1) - V_point 1 * (1 - x1) = 0 := by
      rw [y1_relation]
      ring
    have hL4 : L4 (sigma V_point) ≠ 0 := L4_sigma_V_ne_zero
    have hL3 : L3 Y_point ≠ 0 := ne_of_lt L3_Y_neg
    have hsep : sep (sigma Y_point) ≠ 0 := ne_of_gt sep_sigma_Y_pos
    field_simp [hL4, hL3, hsep]
    rw [L4_sigma_V_eq_neg_root_diff, L3_Y_eq_neg_factored, sep_sigma_Y_eq_factored]
    ring_nf at hrel ⊢
    linear_combination
      (V_point 0 * y1 - V_point 0 + V_point 1 * y1 - V_point 1 - y1 ^ 2 + 1) * hrel

/-
We prove an algebraic identity relating `y1`, `x1`, and `V_point` that is crucial for showing the constant term of the barycentric sum is 1.
-/
lemma algebraic_identity_for_const_coeff :
  (y1 + 1 - x1) * (V_point 1 - y1 * V_point 0) + y1 * x1 * (y1 - (V_point 0 + V_point 1 - 1)) = 0 := by
  have hrel : y1 * (V_point 0 - x1) - V_point 1 * (1 - x1) = 0 := by
    rw [y1_relation]
    ring
  calc
    (y1 + 1 - x1) * (V_point 1 - y1 * V_point 0) +
        y1 * x1 * (y1 - (V_point 0 + V_point 1 - 1))
        = -(y1 + 1) * (y1 * (V_point 0 - x1) - V_point 1 * (1 - x1)) := by
      ring
    _ = 0 := by
      rw [hrel]
      ring

/-
Barycentric coordinates for Region2.
-/
noncomputable def Region2_gamma (p : Point) : ℝ := -L_OV p / (x1 * V_point 1)

noncomputable def Region2_beta (p : Point) : ℝ := p 1 / V_point 1

noncomputable def Region2_alpha (p : Point) : ℝ := 1 - Region2_beta p - Region2_gamma p

/-
Any point p can be decomposed into a linear combination of O, V, X using the defined barycentric coordinates.
-/
lemma Region2_decomp (p : Point) : p = Region2_alpha p • O_point + Region2_beta p • V_point + Region2_gamma p • X_point := by
  unfold Region2_alpha Region2_beta Region2_gamma;
  ext i
  focus
    norm_num [ L_OV ]
  focus
    ring_nf
  fin_cases i <;> norm_num [ O_point, X_point, V_point ] <;> ring_nf;
  · unfold x1; norm_num; ring_nf;
    field_simp;
    rw [ eq_div_iff ] <;> norm_num
    focus
      ring_nf
    focus
      generalize_proofs at *
    · by_cases h : Classical.choose ‹∃ x : ℝ, 19 < x * 20 ∧ x * 25 < 24 ∧ poly_X x = 0› = 0 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ; ring_nf!;
      · linarith [ Classical.choose_spec ‹∃ x : ℝ, 19 < x * 20 ∧ x * 25 < 24 ∧ poly_X x = 0› ];
    · exact sub_ne_zero_of_ne <| by norm_num;
  · have hsqrt_ne : Real.sqrt 6 - Real.sqrt 2 ≠ 0 := by
      intro hsqrt
      nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 2,
        Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num),
        Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    field_simp [hsqrt_ne]

/-
The beta coordinate for Region2 is non-negative for points in the square.
-/
lemma Region2_beta_nonneg (p : Point) (hp : p ∈ Region_Square) : 0 ≤ Region2_beta p := by
  -- Since $p \in \text{Region\_Square}$, we have $p 1 \geq 0$ by definition of $\text{Region\_Square}$.
  have hp1_nonneg : 0 ≤ p 1 := by
    have h_def : p ∈ {p : Point | ∀ i, 0 < p i ∧ p i < 1} := by
      convert hp using 1;
      unfold Region_Square; ext; simp +decide [ Set.pi ] ;
      tauto
    exact le_of_lt ( h_def 1 |>.1 );
  exact div_nonneg hp1_nonneg ( show 0 ≤ V_point 1 by exact div_nonneg ( by norm_num ) ( by norm_num ) )

/-
The gamma coordinate for Region2 is non-negative if L_OV <= 0.
-/
lemma Region2_gamma_nonneg (p : Point) (hOV : L_OV p ≤ 0) : 0 ≤ Region2_gamma p := by
  apply div_nonneg (by
  exact neg_nonneg_of_nonpos hOV) (by
  -- Since $V_point 1$ is positive and $x1$ is positive, their product is positive.
  have h_pos : 0 < V_point 1 ∧ 0 < x1 := by
    -- Since $V_point 1 = \frac{1}{4}$ and $x1 = \frac{9526}{10001}$, both are positive.
    simp [V_point, x1];
    exact ⟨ by norm_num, by have := Classical.choose_spec exists_root_x1; exact this.1 |> fun h => by linarith ⟩;
  exact mul_nonneg h_pos.2.le h_pos.1.le)

/-
Identity relating L2 and Region2_alpha.
-/
lemma L2_eq_neg_x1_y1_mul_alpha (p : Point) : L2 p = -x1 * y1 * Region2_alpha p := by
  unfold L2 Region2_alpha Region2_beta Region2_gamma L_OV; ring_nf;
  -- By definition of y1 and V_point, we know that y1 * (V_point 0 - x1) = V_point 1 * (1 - x1).
  have h_y1_V_point : y1 * (V_point 0 - x1) = V_point 1 * (1 - x1) := by
    exact y1_relation;
  by_cases h : V_point 1 = 0 <;> by_cases h' : x1 = 0 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
  · exact absurd h' ( by linarith [ x1_prop.1 ] );
  · unfold V_point at * ; norm_num at *;
    exact absurd h ( sub_ne_zero_of_ne ( by norm_num ) );
  · exact absurd h' ( by exact ne_of_gt ( show 0 < x1 from by exact lt_of_le_of_lt ( by norm_num ) ( x1_prop.1 ) ) );
  · field_simp [h, h']
    ring_nf at h_y1_V_point ⊢
    linear_combination (p 1) * h_y1_V_point

/-
The alpha coordinate for Region2 is non-negative if L2 <= 0.
-/
lemma Region2_alpha_nonneg (p : Point) (hL2 : L2 p ≤ 0) : 0 ≤ Region2_alpha p := by
  -- Substitute L2 p from L2_eq_neg_x1_y1_mul_alpha into the inequality L2 p ≤ 0.
  have h_sub : -x1 * y1 * Region2_alpha p ≤ 0 := by
    exact hL2.trans' ( by rw [ show L2 p = -x1 * y1 * Region2_alpha p from L2_eq_neg_x1_y1_mul_alpha p ] );
  exact le_of_not_gt fun h => by nlinarith [ show 0 < x1 * y1 by exact mul_pos ( by have := x1_prop; norm_num at this; linarith ) ( by have := y1_bounds; norm_num at this; linarith ) ] ;

/-
If a point satisfies the inequalities for Region2, it is in Region2.
-/
lemma Region2_of_ineq (p : Point) (hp : p ∈ Region_Square) (hL2 : L2 p < 0) (hOV : L_OV p ≤ 0) : p ∈ Region2 := by
  -- By definition of Region2, we need to show that p is in the convex hull of {O, V, X}.
  have h_convex : p ∈ convexHull ℝ {O_point, V_point, X_point} := by
    -- By definition of Region2, we need to show that p is a convex combination of O, V, and X.
    have h_convex : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • O_point + b • V_point + c • X_point := by
      use Region2_alpha p, Region2_beta p, Region2_gamma p
      generalize_proofs at *; exact ⟨by
      exact Region2_alpha_nonneg p hL2.le
      skip, by
        exact Region2_beta_nonneg p hp |> le_trans <| by norm_num;, by
        exact Region2_gamma_nonneg p hOV, by
        unfold Region2_alpha Region2_beta Region2_gamma; ring;, by
        exact Region2_decomp p⟩
      skip
      skip
    generalize_proofs at *; exact (by
    rcases h_convex with ⟨ a, b, c, ha, hb, hc, habc, rfl ⟩ ; rw [ convexHull_eq ] ; norm_num [ ha, hb, hc, habc ] ;
    refine ⟨ Fin 3, { 0, 1, 2 }, fun i => if i = 0 then a else if i = 1 then b else c, ?_, ?_, fun i => if i = 0 then O_point else if i = 1 then V_point else X_point, ?_, ?_ ⟩ <;> simp +decide [ *, Fin.sum_univ_three, Finset.centerMass ];
    · linarith;
    · norm_num [ ← add_assoc, habc ]);
  simpa [Region2] using h_convex

/-
Symmetry of the unit square under sigma.
-/
lemma sigma_mem_Region_Square_iff (p : Point) : sigma p ∈ Region_Square ↔ p ∈ Region_Square := by
  constructor <;> intro hp <;> unfold Region_Square at * <;> aesop

/-
L3 is the reflection of L2.
-/
lemma L3_eq_L2_sigma (p : Point) : L3 p = L2 (sigma p) := by
  ring!

/-
If a point satisfies the inequalities for Region3, it is in Region3.
-/
lemma Region3_of_ineq (p : Point) (hp : p ∈ Region_Square) (hL3 : L3 p < 0) (hOV : L_OV (sigma p) ≤ 0) : p ∈ Region3 := by
  -- Apply `mem_Region3_iff_sigma_mem_Region2` to translate the question about p and Region3 into a question about sigma p and Region2.
  apply (mem_Region3_iff_sigma_mem_Region2 p).mpr;
  apply Region2_of_ineq;
  · exact (sigma_mem_Region_Square_iff p).mpr hp;
  · linarith [ L3_eq_L2_sigma p ];
  · assumption

/-
Barycentric coordinates for Region1.
-/
noncomputable def Region1_denom : ℝ := (V_point 0)^2 - (V_point 1)^2

noncomputable def Region1_beta (p : Point) : ℝ := L_OV (sigma p) / Region1_denom

noncomputable def Region1_gamma (p : Point) : ℝ := L_OV p / Region1_denom

noncomputable def Region1_alpha (p : Point) : ℝ := 1 - Region1_beta p - Region1_gamma p

/-
The denominator for Region1 barycentric coordinates is positive.
-/
lemma Region1_denom_pos : Region1_denom > 0 := by
  exact sub_pos.mpr ( by rw [ sq, sq ] ; exact ( by have := V_bounds; norm_num [ V_point ] at this ⊢; nlinarith ) )

/-
Decomposition of a point using Region1 barycentric coordinates.
-/
lemma Region1_decomp (p : Point) : p = Region1_alpha p • O_point + Region1_beta p • V_point + Region1_gamma p • (sigma V_point) := by
  unfold Region1_alpha Region1_beta Region1_gamma; ext i; fin_cases i <;> norm_num <;> ring_nf;
  · unfold L_OV Region1_denom O_point V_point sigma; norm_num; ring_nf;
    grind;
  · unfold L_OV Region1_denom O_point V_point sigma; norm_num ; ring_nf;
    norm_num [ mul_assoc, mul_comm, mul_left_comm ]

/-
Non-negativity of beta coordinate for Region1.
-/
lemma Region1_beta_nonneg (p : Point) (h : L_OV (sigma p) ≥ 0) : Region1_beta p ≥ 0 := by
  unfold Region1_beta; exact div_nonneg h ( by linarith [ Region1_denom_pos ] ) ;

/-
Non-negativity of gamma coordinate for Region1.
-/
lemma Region1_gamma_nonneg (p : Point) (h : L_OV p ≥ 0) : Region1_gamma p ≥ 0 := by
  exact div_nonneg h ( le_of_lt ( by exact Region1_denom_pos ) )

/-
Sum of beta and gamma coordinates for Region1.
-/
lemma Region1_beta_add_gamma (p : Point) : Region1_beta p + Region1_gamma p = (p 0 + p 1) / (V_point 0 + V_point 1) := by
  convert congr_arg ( fun x : ℝ => x / Region1_denom ) ( show L_OV ( sigma p ) + L_OV p = ( p 0 + p 1 ) * ( V_point 0 - V_point 1 ) by
                                                          unfold L_OV sigma; ring_nf;
                                                          ring! ) using 1;
  · unfold Region1_beta Region1_gamma; ring;
  · rw [ show Region1_denom = ( V_point 0 - V_point 1 ) * ( V_point 0 + V_point 1 ) by unfold Region1_denom; ring ] ; rw [ div_eq_div_iff ] <;> ring_nf <;> norm_num [ V_point ];
    · ring_nf ; norm_num;
    · ring_nf; norm_num

/-
Non-negativity of alpha coordinate for Region1.
-/
lemma Region1_alpha_nonneg (p : Point) (hL1 : L1 p ≤ 0) : Region1_alpha p ≥ 0 := by
  -- Since $p 0 + p 1 \leq V_point 0 + V_point 1$ and $V_point 0 + V_point 1 > 0$, we have $(p 0 + p 1) / (V_point 0 + V_point 1) \leq 1$.
  have h_frac_le_one : (p 0 + p 1) / (V_point 0 + V_point 1) ≤ 1 := by
    unfold L1 at hL1; rw [ div_le_iff₀ ] <;> linarith [ V_bounds ] ;
  exact sub_nonneg_of_le ( by linarith [ show Region1_beta p + Region1_gamma p = ( p 0 + p 1 ) / ( V_point 0 + V_point 1 ) from by
                                          convert Region1_beta_add_gamma p using 1 ] )

/-
If a point satisfies the inequalities for Region1, it is in Region1.
-/
lemma Region1_of_ineq (p : Point) (hp : p ∈ Region_Square) (hL1 : L1 p ≤ 0) (hOV : L_OV p ≥ 0) (hOVsigma : L_OV (sigma p) ≥ 0) : p ∈ Region1 := by
  -- Let's choose any point $p$ in the region defined by $L1 p \leq 0$, $L_OV p \geq 0$, and $L_OV (sigma p) \geq 0$.
  apply convexHull_sub_Region1_of_pos;
  · -- By definition of Region1, we know that p is a convex combination of O, V, and sigma V.
    have h_convex : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • O_point + b • V_point + c • sigma V_point := by
      use Region1_alpha p, Region1_beta p, Region1_gamma p;
      exact ⟨ Region1_alpha_nonneg p hL1, Region1_beta_nonneg p hOVsigma, Region1_gamma_nonneg p hOV, by unfold Region1_alpha; ring, Region1_decomp p ⟩;
    rcases h_convex with ⟨ a, b, c, ha, hb, hc, habc, rfl ⟩ ; rw [ convexHull_eq ] ; norm_num [ ha, hb, hc, habc ] ;
    refine ⟨ Fin 3, { 0, 1, 2 }, fun i => if i = 0 then a else if i = 1 then b else c, ?_, ?_, fun i => if i = 0 then O_point else if i = 1 then V_point else sigma V_point, ?_, ?_ ⟩ <;> simp +decide [ *, Finset.centerMass ];
    · linarith;
    · norm_num [ ← add_assoc, habc ];
  · assumption

/-
The y-coordinate of V is less than the x-coordinate of V.
-/
lemma V_point_1_lt_V_point_0 : V_point 1 < V_point 0 := by
  exact div_lt_div_iff_of_pos_right ( by norm_num ) |>.2 ( by nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ] )

/-
Point p can be decomposed into a convex combination of V, sigma V, and Y using the lambda coordinates.
-/
lemma Region6a_decomp (p : Point) : p = lambda_V p • V_point + lambda_sigma_V p • (sigma V_point) + lambda_Y p • Y_point := by
  have hsep : sep V_point ≠ 0 := ne_of_lt sep_V_neg
  have hL2 : L2 (sigma V_point) ≠ 0 := ne_of_lt L2_sigma_V_neg
  have hL1 : L1 Y_point ≠ 0 := ne_of_gt L1_Y_pos
  have hrel : y1 * (V_point 0 - x1) - V_point 1 * (1 - x1) = 0 := by
    rw [y1_relation]
    ring
  ext i <;> fin_cases i
  · unfold lambda_V lambda_sigma_V lambda_Y sep L2 L1 sigma Y_point at *
    norm_num at *
    field_simp [hsep, hL2, hL1]
    ring_nf at hrel ⊢
    first
    | linear_combination
        (V_point 1 * (-V_point 0 - V_point 1 + y1 + 1) *
          (-V_point 0 * p 0 + V_point 0 + V_point 1 * p 1 - V_point 1 * y1 +
            p 0 * y1 - p 1)) * hrel
    | linear_combination
        -(V_point 1 * (-V_point 0 - V_point 1 + y1 + 1) *
          (-V_point 0 * p 0 + V_point 0 + V_point 1 * p 1 - V_point 1 * y1 +
            p 0 * y1 - p 1)) * hrel
  · unfold lambda_V lambda_sigma_V lambda_Y sep L2 L1 sigma Y_point at *
    norm_num at *
    field_simp [hsep, hL2, hL1]
    ring_nf at hrel ⊢
    first
    | linear_combination
        (V_point 0 * (-V_point 0 - V_point 1 + y1 + 1) *
          (-V_point 0 * p 0 + V_point 0 + V_point 1 * p 1 - V_point 1 * y1 +
            p 0 * y1 - p 1)) * hrel
    | linear_combination
        -(V_point 0 * (-V_point 0 - V_point 1 + y1 + 1) *
          (-V_point 0 * p 0 + V_point 0 + V_point 1 * p 1 - V_point 1 * y1 +
            p 0 * y1 - p 1)) * hrel

/-
The coefficient of p0 in the sum of mu coordinates is 0.
-/
lemma mu_sum_p0_coeff_eq_zero_proof :
  1 / L4 (sigma V_point) + (x1 - 1) / L3 Y_point - (y1 - V_point 0) / sep (sigma Y_point) = 0 := by
    -- Apply the lemma that states the equation holds.
    apply mu_sum_p0_coeff_eq_zero

/-
The coefficient of p1 in the sum of mu coordinates is 0.
-/
lemma mu_sum_p1_coeff_eq_zero_proof :
  1 / L4 (sigma V_point) + y1 / L3 Y_point + (1 - V_point 1) / sep (sigma Y_point) = 0 := by
    convert mu_sum_p1_coeff_eq_zero using 1

/-
The sum of the barycentric coordinates for Region6b is 1 for any point p.
-/
lemma mu_sum_eq_one (p : Point) : mu_sigmaV p + mu_Y p + mu_sigmaY p = 1 := by
  have h_sum_const : ∀ p q : Point, (mu_sigmaV p + mu_Y p + mu_sigmaY p) - (mu_sigmaV q + mu_Y q + mu_sigmaY q) = (p 0 - q 0) * (1 / L4 (sigma V_point) + (x1 - 1) / L3 Y_point - (y1 - V_point 0) / sep (sigma Y_point)) + (p 1 - q 1) * (1 / L4 (sigma V_point) + y1 / L3 Y_point + (1 - V_point 1) / sep (sigma Y_point)) := by
    intros p q
    simp [mu_sigmaV, mu_Y, mu_sigmaY];
    unfold L4 L3 sep; ring;
  have h_sum_const : ∀ p q : Point, (mu_sigmaV p + mu_Y p + mu_sigmaY p) = (mu_sigmaV q + mu_Y q + mu_sigmaY q) := by
    intros p q; specialize h_sum_const p q; rw [ mu_sum_p0_coeff_eq_zero_proof, mu_sum_p1_coeff_eq_zero_proof ] at h_sum_const; linarith;
  convert h_sum_const p ( sigma V_point ) using 1 ; norm_num [ mu_values ]

/-
Algebraic identity for the coefficient of p0 in the x-coordinate of Region6b decomposition.
-/
lemma Region6b_coeff_p0_x_identity : (y1 + 1 - x1) * (V_point 0 - 1) + (1 - x1) * (y1 - V_point 0 - V_point 1 + 1) = 0 := by
  have hrel : y1 * (V_point 0 - x1) = V_point 1 * (1 - x1) := y1_relation
  nlinarith

/-
Algebraic identity for the coefficient of p1 in the x-coordinate of Region6b decomposition.
-/
lemma Region6b_coeff_p1_x_identity : (y1 + 1 - x1) * (V_point 1 - y1) + y1 * (y1 - V_point 0 - V_point 1 + 1) = 0 := by
  have := y1_relation;
  nlinarith

/-
The coefficient of p0 in the x-coordinate of the barycentric decomposition for Region6b is 1.
-/
lemma Region6b_coeff_p0_x : (1 / L4 (sigma V_point)) * (sigma V_point 0) + (-(1 - x1) / L3 Y_point) * Y_point 0 + (-(y1 - V_point 0) / sep (sigma Y_point)) * (sigma Y_point 0) = 1 := by
  have hroot : y1 - (V_point 0 + V_point 1 - 1) ≠ 0 := by
    linarith [root1_lt_y1]
  have hy : 1 - y1 ≠ 0 := by
    linarith [y1_bounds.2]
  have hden : y1 + 1 - x1 ≠ 0 := by
    linarith [y1_bounds.1, x1_prop.2.1]
  rw [L4_sigma_V_eq_neg_root_diff, L3_Y_eq_neg_factored,
    sep_sigma_Y_eq_factored]
  change
    (1 / (-(y1 - (V_point 0 + V_point 1 - 1)))) * V_point 1 +
        (-(1 - x1) / (-(1 - y1) * (y1 + 1 - x1))) * 1 +
          (-(y1 - V_point 0) /
              ((y1 - (V_point 0 + V_point 1 - 1)) * (1 - y1))) * y1 =
      1
  field_simp [hroot, hy, hden]
  have hnum := Region6b_coeff_p0_x_identity
  ring_nf at hnum ⊢
  linear_combination hnum

/-
Points in the square with L2 >= 0 are in UnionRegions.
-/
lemma Cover_Part1 : ∀ p ∈ Region_Square, L2 p ≥ 0 → p ∈ UnionRegions := by
  intro p hp hL2
  have hRegion4 : p ∈ Region4 := by
    -- Apply the lemma that states if L2 p ≥ 0, then p is in Region4.
    apply Region4_contains_L2_ge_0 p hp hL2
  have hUnion : p ∈ UnionRegions := by
    simp [UnionRegions, hRegion4]
  exact hUnion

/-
Points in the square with L3 >= 0 are in UnionRegions.
-/
lemma Cover_Part2 : ∀ p ∈ Region_Square, L3 p ≥ 0 → p ∈ UnionRegions := by
  intros p hp hL3
  have hRegion5 : p ∈ Region5 := by
    apply Region5_contains_L3_ge_0 p hp hL3
    skip -- This should not be reachable, as the proof should be complete. p hp hL3
  exact (by
  unfold UnionRegions; aesop;)
  skip

/-
Points in the square with L4 >= 0 are in UnionRegions.
-/
lemma Cover_Part3 : ∀ p ∈ Region_Square, L4 p ≥ 0 → p ∈ UnionRegions := by
  intros p hp hL4;
  -- Apply the lemma that states if L4 p ≥ 0, then p is in Region_Corner.
  have h_region : p ∈ Region_Corner := by
    apply Region_Corner_contains_L4_ge_0 p hp hL4;
  exact Or.inr h_region

/-
Points in the square with L2 < 0, L3 < 0, L1 <= 0 are in UnionRegions.
-/
lemma Cover_Part4a : ∀ p ∈ Region_Square, L2 p < 0 → L3 p < 0 → L1 p ≤ 0 → p ∈ UnionRegions := by
  intros p hp hL2 hL3 hL1
  by_cases hL3 : L3 p < 0 ∧ L_OV p ≤ 0 ∨ L2 p < 0 ∧ L_OV (sigma p) ≤ 0 ∨ L1 p ≤ 0 ∧ L_OV p ≥ 0 ∧ L_OV (sigma p) ≥ 0
  focus
    generalize_proofs at *
  · cases' hL3 with hL3 hL3 <;> simp_all +decide [ UnionRegions ];
    · exact Or.inl <| Or.inl <| Or.inl <| Or.inl <| Or.inl <| Or.inl <| Or.inr <| Region2_of_ineq p hp hL2 hL3.2;
    · cases' hL3 with hL3 hL3 <;> simp_all +decide [ Region2_of_ineq, Region3_of_ineq, Region1_of_ineq ];
  · grind

/-
Points satisfying the inequalities for Region6a are in Region6a.
-/
lemma Cover_Part4b_Region6a : ∀ p ∈ Region_Square, L2 p < 0 → L3 p < 0 → L4 p < 0 → L1 p ≥ 0 → sep p ≤ 0 → p ∈ Region6a := by
  intros p hp_mem hpL2 hpL3 hpL4 hpL1 hpsep
  have hp_coeffs : 0 ≤ lambda_V p ∧ 0 ≤ lambda_sigma_V p ∧ 0 ≤ lambda_Y p ∧ lambda_V p + lambda_sigma_V p + lambda_Y p = 1 := by
    refine ⟨ ?_, ?_, ?_, ?_ ⟩
    all_goals generalize_proofs at *;
    · exact div_nonneg_of_nonpos hpsep ( by linarith [ sep_V_neg ] );
    · exact div_nonneg_of_nonpos ( by linarith ) ( by linarith [ L2_sigma_V_neg ] );
    · exact div_nonneg hpL1 ( by linarith [ L1_Y_pos ] );
    · exact lambda_sum_eq_one p;
  rw [ show p = lambda_V p • V_point + lambda_sigma_V p • ( sigma V_point ) + lambda_Y p • Y_point from ?_ ];
  · rw [ show Region6a = convexHull ℝ { V_point, sigma V_point, Y_point } from ?_ ];
    · rw [ convexHull_eq ];
      refine ⟨ Fin 3, { 0, 1, 2 }, fun i => if i = 0 then lambda_V p else if i = 1 then lambda_sigma_V p else lambda_Y p, fun i => if i = 0 then V_point else if i = 1 then sigma V_point else Y_point, ?_, ?_, ?_, ?_ ⟩ <;> simp +decide [ *, Fin.sum_univ_three, Finset.centerMass ];
      · linarith;
      · norm_num [ ← add_assoc, hp_coeffs.2.2.2 ];
    · exact rfl;
  · convert Region6a_decomp p using 1

/-
The value of sep at sigma Y is related to the value of L4 at sigma V by a factor of -(1-y1).
-/
lemma relation_sep_L4 : sep (sigma Y_point) = -L4 (sigma V_point) * (1 - y1) := by
  rw [ sep_sigma_Y_eq_factored, L4_sigma_V_eq_neg_root_diff ] ; ring

/-
The sum of the first and third terms in the p1 coefficient expression simplifies to a single fraction.
-/
lemma Region6b_p1_term13_simp : (1 / L4 (sigma V_point)) * (sigma V_point 0) + ((1 - V_point 1) / sep (sigma Y_point)) * (sigma Y_point 0) = (V_point 1 - y1) / (L4 (sigma V_point) * (1 - y1)) := by
  -- Substitute the known values of sigma V_point 0 and sigma Y_point 0 into the first two terms.
  have h_sub : 1 / L4 (sigma V_point) * sigma V_point 0 + (1 - V_point 1) / sep (sigma Y_point) * sigma Y_point 0 = 1 / L4 (sigma V_point) * V_point 1 + (1 - V_point 1) / sep (sigma Y_point) * y1 := by
    rfl;
  -- Substitute the known value of sep (sigma Y_point) into the expression.
  have h_sep : sep (sigma Y_point) = -L4 (sigma V_point) * (1 - y1) := by
    convert relation_sep_L4 using 1;
  by_cases h : L4 ( sigma V_point ) = 0 <;> by_cases h' : 1 - y1 = 0 <;> simp_all +decide [ division_def, mul_assoc, mul_comm, mul_left_comm ];
  · exact absurd h' ( by linarith [ show y1 < 1 from by linarith [ y1_bounds.1, y1_bounds.2 ] ] );
  · field_simp [h, h']
    ring

/-
A simplified algebraic identity involving V_point, y1, and x1 holds.
-/
lemma Region6b_coeff_p1_x_simplified : (V_point 1 - y1) / (y1 - (V_point 0 + V_point 1 - 1)) + y1 / (y1 + 1 - x1) = 0 := by
  convert congr_arg ( fun x : ℝ => x / ( ( y1 - ( V_point 0 + V_point 1 - 1 ) ) * ( y1 + 1 - x1 ) ) ) ( Region6b_coeff_p1_x_identity ) using 1;
  · rw [ div_add_div ]
    focus
      ring_nf
    all_goals nlinarith [ y1_bounds, root1_lt_y1, x1_prop ];
  · ring

/-
The core expression for the p1 coefficient is zero.
-/
lemma Region6b_coeff_p1_x_core : (V_point 1 - y1) / (L4 (sigma V_point) * (1 - y1)) + y1 / L3 Y_point = 0 := by
  have hroot : y1 - (V_point 0 + V_point 1 - 1) ≠ 0 := by
    linarith [root1_lt_y1]
  have hy : 1 - y1 ≠ 0 := by
    linarith [y1_bounds.2]
  have hden : y1 + 1 - x1 ≠ 0 := by
    linarith [y1_bounds.1, x1_prop.2.1]
  rw [L4_sigma_V_eq_neg_root_diff, L3_Y_eq_neg_factored]
  change
    (V_point 1 - y1) / (-(y1 - (V_point 0 + V_point 1 - 1)) * (1 - y1)) +
        y1 / (-(1 - y1) * (y1 + 1 - x1)) =
      0
  have hsimp := Region6b_coeff_p1_x_simplified
  field_simp [hroot, hy, hden] at hsimp ⊢
  ring_nf at hsimp ⊢
  linarith

/-
The coefficient of p1 in the x-coordinate decomposition for Region6b is zero.
-/
lemma Region6b_coeff_p1_x : (1 / L4 (sigma V_point)) * (sigma V_point 0) + (y1 / L3 Y_point) * Y_point 0 + ((1 - V_point 1) / sep (sigma Y_point)) * (sigma Y_point 0) = 0 := by
  convert Region6b_coeff_p1_x_core using 1;
  rw [ ← Region6b_p1_term13_simp ] ; ring_nf;
  unfold Y_point; norm_num;

/-
The sum of the first and third terms in the constant coefficient expression simplifies to a single fraction.
-/
lemma Region6b_const_term13_simp : (-(1 + y1) / L4 (sigma V_point)) * (sigma V_point 0) + ((-(1 - V_point 1) * V_point 0 + (y1 - V_point 0) * V_point 1) / sep (sigma Y_point)) * (sigma Y_point 0) = (V_point 1 - y1 * V_point 0) / (-L4 (sigma V_point) * (1 - y1)) := by
  -- Substitute `sigma V_point 0 = V_point 1` and `sigma Y_point 0 = y1`.
  have h_subst : sigma V_point 0 = V_point 1 ∧ sigma Y_point 0 = y1 := by
    exact ⟨ rfl, rfl ⟩;
  rw [ show sep ( sigma Y_point ) = -L4 ( sigma V_point ) * ( 1 - y1 ) by
        exact relation_sep_L4 ] ; ring_nf;
  rw [ show L4 ( sigma V_point ) = - ( y1 - ( V_point 0 + V_point 1 - 1 ) ) by
        exact L4_sigma_V_eq_neg_root_diff ] ; ring_nf;
  rw [ show ( -1 - y1 + V_point 0 + V_point 1 ) = ( 1 + y1 * V_point 0 + ( y1 * V_point 1 - y1 ^ 2 ) + ( -V_point 0 - V_point 1 ) ) / ( - ( 1 - y1 ) ) by rw [ eq_div_iff ] <;> nlinarith [ y1_bounds, V_bounds ] ] ; norm_num ; ring_nf;
  rw [ h_subst.1, h_subst.2 ] ; ring;

/-
An algebraic identity involving V_point, y1, and x1 holds.
-/
lemma Region6b_coeff_const_x_identity : (y1 + 1 - x1) * (V_point 1 - y1 * V_point 0) + y1 * x1 * (y1 - (V_point 0 + V_point 1 - 1)) = 0 := by
  convert algebraic_identity_for_const_coeff using 1

/-
A simplified algebraic identity involving V_point, y1, and x1 holds.
-/
lemma Region6b_coeff_const_x_simplified : (V_point 1 - y1 * V_point 0) / (y1 - (V_point 0 + V_point 1 - 1)) + y1 * x1 / (y1 + 1 - x1) = 0 := by
  convert congr_arg ( fun x : ℝ => x / ( ( y1 - ( V_point 0 + V_point 1 - 1 ) ) * ( y1 + 1 - x1 ) ) ) ( Region6b_coeff_const_x_identity ) using 1;
  · rw [ div_add_div ];
    · ring;
    · exact sub_ne_zero_of_ne ( by linarith [ root1_lt_y1 ] );
    · linarith [ y1_bounds.1, y1_bounds.2, x1_prop.1, x1_prop.2.1 ];
  · ring

/-
The constant term in the x-coordinate decomposition for Region6b is zero.
-/
lemma Region6b_coeff_const_x : (-(1 + y1) / L4 (sigma V_point)) * (sigma V_point 0) + (-y1 * x1 / L3 Y_point) * Y_point 0 + ((-(1 - V_point 1) * V_point 0 + (y1 - V_point 0) * V_point 1) / sep (sigma Y_point)) * (sigma Y_point 0) = 0 := by
  -- Substitute the known values of the coefficients into the expression.
  have h_subst : (V_point 1 - y1 * V_point 0) / (-L4 (sigma V_point) * (1 - y1)) + (-y1 * x1) / (-(1 - y1) * (y1 + 1 - x1)) = 0 := by
    have hy1_ne : 1 - y1 ≠ 0 := by linarith [y1_bounds.2]
    have hroot_ne : y1 - (V_point 0 + V_point 1 - 1) ≠ 0 := by linarith [root1_lt_y1]
    have hx1_lt_one : x1 < 1 := by linarith [x1_prop.2.1]
    have hden_ne : y1 + 1 - x1 ≠ 0 := by linarith [y1_bounds.1, hx1_lt_one]
    calc
      (V_point 1 - y1 * V_point 0) / (-L4 (sigma V_point) * (1 - y1)) + (-y1 * x1) / (-(1 - y1) * (y1 + 1 - x1))
          = ((V_point 1 - y1 * V_point 0) / (y1 - (V_point 0 + V_point 1 - 1)) + y1 * x1 / (y1 + 1 - x1)) / (1 - y1) := by
            rw [L4_sigma_V_eq_neg_root_diff]
            field_simp [hy1_ne, hroot_ne, hden_ne]
      _ = 0 := by
            rw [Region6b_coeff_const_x_simplified]
            ring
  rw [ ← h_subst, L3_Y_eq_neg_factored ];
  convert congr_arg ( fun x : ℝ => x + -y1 * x1 / ( - ( 1 - y1 ) * ( y1 + 1 - x1 ) ) ) ( Region6b_const_term13_simp ) using 1 ; ring_nf!;
  norm_num [ Y_point ]

/-
The x-coordinate of p can be decomposed into the weighted sum of the x-coordinates of the vertices sigma V, Y, sigma Y.
-/
lemma Region6b_decomp_x (p : Point) : p 0 = mu_sigmaV p * (sigma V_point) 0 + mu_Y p * Y_point 0 + mu_sigmaY p * (sigma Y_point) 0 := by
  have h_coeff_p0 : (1 / L4 (sigma V_point)) * (sigma V_point 0) + (-(1 - x1) / L3 Y_point) * Y_point 0 + (-(y1 - V_point 0) / sep (sigma Y_point)) * (sigma Y_point 0) = 1 := by
    convert Region6b_coeff_p0_x using 1;
  have h_coeff_p1 : (1 / L4 (sigma V_point)) * (sigma V_point 0) + (y1 / L3 Y_point) * Y_point 0 + ((1 - V_point 1) / sep (sigma Y_point)) * (sigma Y_point 0) = 0 := by
    convert Region6b_coeff_p1_x using 1;
  have h_coeff_const : (-(1 + y1) / L4 (sigma V_point)) * (sigma V_point 0) + (-y1 * x1 / L3 Y_point) * Y_point 0 + ((-(1 - V_point 1) * V_point 0 + (y1 - V_point 0) * V_point 1) / sep (sigma Y_point)) * (sigma Y_point 0) = 0 := by
    convert Region6b_coeff_const_x using 1;
  unfold mu_sigmaV mu_Y mu_sigmaY at *;
  unfold L4 L3 sep at *;
  linear_combination -h_coeff_const - h_coeff_p1 * p 1 - h_coeff_p0 * p 0

/-
The coefficient of p0 in the y-coordinate decomposition for Region6b is zero.
-/
lemma Region6b_coeff_p0_y : (1 / L4 (sigma V_point)) * (sigma V_point 1) + (-(1 - x1) / L3 Y_point) * Y_point 1 + (-(y1 - V_point 0) / sep (sigma Y_point)) * (sigma Y_point 1) = 0 := by
  -- Substitute the definitions of `L4`, `L3`, and `sep` into the coefficients.
  have h_sub : (1 / L4 (sigma V_point)) + (-(1 - x1) / L3 Y_point) + (-(y1 - V_point 0) / sep (sigma Y_point)) = 0 := by
    convert mu_sum_p0_coeff_eq_zero using 1;
    ring;
  convert congr_arg ( · * y1 ) h_sub using 1 <;> ring_nf;
  rw [ show sigma V_point 1 = V_point 0 from rfl, show Y_point 1 = y1 from rfl, show sigma Y_point 1 = 1 from rfl ] ; ring_nf;
  rw [ show sep ( sigma Y_point ) = -L4 ( sigma V_point ) * ( 1 - y1 ) from ?_ ]
  focus
    ring_nf
  · rw [ show -L4 ( sigma V_point ) + L4 ( sigma V_point ) * y1 = L4 ( sigma V_point ) * ( -1 + y1 ) by ring ] ; norm_num ; ring_nf;
    nlinarith [ inv_mul_cancel_left₀ ( show -1 + y1 ≠ 0 by linarith [ y1_bounds ] ) ( ( L4 ( sigma V_point ) ) ⁻¹ * y1 ), inv_mul_cancel_left₀ ( show -1 + y1 ≠ 0 by linarith [ y1_bounds ] ) ( ( L4 ( sigma V_point ) ) ⁻¹ * V_point 0 ) ];
  · field_simp;
    rw [ relation_sep_L4 ] ; ring

/-
The sum of the first and third terms in the p1 coefficient expression for y simplifies to a single fraction.
-/
lemma Region6b_p1_y_term13_simp : (1 / L4 (sigma V_point)) * V_point 0 + ((1 - V_point 1) / sep (sigma Y_point)) * 1 = (V_point 0 * (1 - y1) - (1 - V_point 1)) / (L4 (sigma V_point) * (1 - y1)) := by
  field_simp;
  rw [ div_add_div ];
  · rw [ show sep ( sigma Y_point ) = -L4 ( sigma V_point ) * ( 1 - y1 ) by exact relation_sep_L4 ] ; ring_nf;
    rw [ show -L4 ( sigma V_point ) ^ 2 + L4 ( sigma V_point ) ^ 2 * y1 = L4 ( sigma V_point ) * ( L4 ( sigma V_point ) - L4 ( sigma V_point ) * y1 ) * -1 by ring ] ; norm_num ; ring_nf;
    by_cases h : L4 ( sigma V_point ) = 0 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
  · exact L4_sigma_V_ne_zero;
  · linarith [ sep_sigma_Y_pos ]

/-
A simplified algebraic identity involving V_point, y1, and x1 holds.
-/
lemma Region6b_coeff_p1_y_simplified : (V_point 0 * (1 - y1) - (1 - V_point 1)) / (y1 - (V_point 0 + V_point 1 - 1)) + y1^2 / (y1 + 1 - x1) - (y1 - 1) = 0 := by
  have hroot : y1 - (V_point 0 + V_point 1 - 1) ≠ 0 := by
    linarith [root1_lt_y1]
  have hden : y1 + 1 - x1 ≠ 0 := by
    linarith [y1_bounds.1, x1_prop.2.1]
  have hrel : y1 * (V_point 0 - x1) - V_point 1 * (1 - x1) = 0 := by
    rw [y1_relation]
    ring
  field_simp [hroot, hden]
  ring_nf at hrel ⊢
  linear_combination -y1 * hrel

/-
The core expression for the p1 coefficient in y is 1.
-/
lemma Region6b_coeff_p1_y_core : (V_point 0 * (1 - y1) - (1 - V_point 1)) / (L4 (sigma V_point) * (1 - y1)) + y1^2 / L3 Y_point = 1 := by
  have h_sub : (V_point 0 * (1 - y1) - (1 - V_point 1)) / (-(y1 - (V_point 0 + V_point 1 - 1)) * (1 - y1)) + y1^2 / (-(1 - y1) * (y1 + 1 - x1)) = 1 := by
    have h_simp : (V_point 0 * (1 - y1) - (1 - V_point 1)) / (y1 - (V_point 0 + V_point 1 - 1)) + y1^2 / (y1 + 1 - x1) = y1 - 1 := by
      have h_simp : (V_point 0 * (1 - y1) - (1 - V_point 1)) / (y1 - (V_point 0 + V_point 1 - 1)) + y1^2 / (y1 + 1 - x1) - (y1 - 1) = 0 := by
        convert Region6b_coeff_p1_y_simplified using 1;
      exact eq_of_sub_eq_zero h_simp ▸ rfl;
    have hy_ne : 1 - y1 ≠ 0 := by linarith [y1_bounds]
    convert congr_arg ( fun x : ℝ => x * (-1 / (1 - y1)) ) h_simp using 1 <;> field_simp [hy_ne] <;> ring
  convert h_sub using 2 <;> norm_num [ L4_sigma_V_eq_neg_root_diff, L3_Y_eq_neg_factored ]

/-
The coefficient of p1 in the y-coordinate decomposition for Region6b is 1.
-/
lemma Region6b_coeff_p1_y : (1 / L4 (sigma V_point)) * (sigma V_point 1) + (y1 / L3 Y_point) * Y_point 1 + ((1 - V_point 1) / sep (sigma Y_point)) * (sigma Y_point 1) = 1 := by
  -- Apply the lemma's result directly to conclude the proof.
  convert Region6b_coeff_p1_y_core using 1;
  rw [ ← Region6b_p1_y_term13_simp ];
  unfold sigma; norm_num; ring_nf;
  unfold Y_point; norm_num; ring;

/-
The sum of the first and third terms in the constant coefficient expression for y simplifies to a single fraction.
-/
lemma Region6b_const_y_term13_simp : (-(1 + y1) / L4 (sigma V_point)) * V_point 0 + ((-(1 - V_point 1) * V_point 0 + (y1 - V_point 0) * V_point 1) / sep (sigma Y_point)) * 1 = y1 * (V_point 1 - y1 * V_point 0) / (-L4 (sigma V_point) * (1 - y1)) := by
  rw [relation_sep_L4]
  have hL4 : L4 (sigma V_point) ≠ 0 := L4_sigma_V_ne_zero
  have hy : 1 - y1 ≠ 0 := by
    linarith [y1_bounds.2]
  field_simp [hL4, hy]
  ring

/-
The constant term in the y-coordinate decomposition for Region6b is zero.
-/
lemma Region6b_coeff_const_y : (-(1 + y1) / L4 (sigma V_point)) * (sigma V_point 1) + (-y1 * x1 / L3 Y_point) * Y_point 1 + ((-(1 - V_point 1) * V_point 0 + (y1 - V_point 0) * V_point 1) / sep (sigma Y_point)) * (sigma Y_point 1) = 0 := by
  have h_common_denom : y1 * (V_point 1 - y1 * V_point 0) / (-L4 (sigma V_point) * (1 - y1)) + (-y1 * x1 / L3 Y_point) * y1 = 0 := by
    have hy1_ne : 1 - y1 ≠ 0 := by linarith [y1_bounds.2]
    have hroot_ne : y1 - (V_point 0 + V_point 1 - 1) ≠ 0 := by linarith [root1_lt_y1]
    have hx1_lt_one : x1 < 1 := by linarith [x1_prop.2.1]
    have hden_ne : y1 + 1 - x1 ≠ 0 := by linarith [y1_bounds.1, hx1_lt_one]
    calc
      y1 * (V_point 1 - y1 * V_point 0) / (-L4 (sigma V_point) * (1 - y1)) + (-y1 * x1 / L3 Y_point) * y1
          = ((V_point 1 - y1 * V_point 0) / (y1 - (V_point 0 + V_point 1 - 1)) + y1 * x1 / (y1 + 1 - x1)) * y1 / (1 - y1) := by
            rw [L4_sigma_V_eq_neg_root_diff, L3_Y_eq_neg_factored]
            field_simp [hy1_ne, hroot_ne, hden_ne]
      _ = 0 := by
            rw [Region6b_coeff_const_x_simplified]
            ring
  rw [ ← h_common_denom ];
  rw [ ← Region6b_const_y_term13_simp ] ; ring_nf!;
  erw [ show sigma Y_point 1 = 1 from rfl ] ; ring!;

/-
If a point in the square satisfies L2 < 0, L3 < 0, L4 < 0, and sep >= 0, it is in Region6b.
-/
lemma Cover_Part4b_Region6b : ∀ p ∈ Region_Square, L2 p < 0 → L3 p < 0 → L4 p < 0 → sep p ≥ 0 → p ∈ Region6b := by
  -- By definition of $p$ being in $Region6b$, we need to show that $p$ can be written as a convex combination of $\sigma V$, $Y$, and $\sigma Y$ with non-negative weights.
  intro p hp hL2 hL3 hL4 hsep
  have h_convex : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • sigma V_point + b • Y_point + c • sigma Y_point := by
    use mu_sigmaV p, mu_Y p, mu_sigmaY p;
    have h_mu_nonneg : 0 ≤ mu_sigmaV p ∧ 0 ≤ mu_Y p ∧ 0 ≤ mu_sigmaY p := by
      have h_L4_sigma_V_neg : L4 (sigma V_point) < 0 := by
        convert L4_sigma_V_neg
      have h_L3_Y_neg : L3 Y_point < 0 := by
        convert L3_Y_neg using 1
      have h_sep_sigma_Y_pos : sep (sigma Y_point) > 0 := by
        exact sep_sigma_Y_pos;
      exact ⟨ div_nonneg_of_nonpos hL4.le h_L4_sigma_V_neg.le, div_nonneg_of_nonpos hL3.le h_L3_Y_neg.le, div_nonneg hsep h_sep_sigma_Y_pos.le ⟩;
    have h_mu_sum : mu_sigmaV p + mu_Y p + mu_sigmaY p = 1 := by
      exact mu_sum_eq_one p;
    have h_mu_decomp : p 0 = mu_sigmaV p * (sigma V_point 0) + mu_Y p * Y_point 0 + mu_sigmaY p * (sigma Y_point 0) ∧ p 1 = mu_sigmaV p * (sigma V_point 1) + mu_Y p * Y_point 1 + mu_sigmaY p * (sigma Y_point 1) := by
      apply And.intro;
      · apply Region6b_decomp_x;
      · have h_mu_decomp_y : p 1 = mu_sigmaV p * (sigma V_point 1) + mu_Y p * Y_point 1 + mu_sigmaY p * (sigma Y_point 1) := by
          have h_coeff_p0 := Region6b_coeff_p0_y
          have h_coeff_p1 := Region6b_coeff_p1_y
          have h_coeff_const := Region6b_coeff_const_y
          unfold mu_sigmaV mu_Y mu_sigmaY at *;
          unfold L4 L3 sep at *;
          linear_combination -h_coeff_const - h_coeff_p1 * p 1 - h_coeff_p0 * p 0
        exact h_mu_decomp_y;
    exact ⟨ h_mu_nonneg.1, h_mu_nonneg.2.1, h_mu_nonneg.2.2, h_mu_sum, by ext i; fin_cases i <;> tauto ⟩;
  obtain ⟨ a, b, c, ha, hb, hc, habc, rfl ⟩ := h_convex; ( rw [ show Region6b = convexHull ℝ { sigma V_point, Y_point, sigma Y_point } from rfl ] ; );
  rw [ convexHull_eq ];
  refine ⟨ ?_, { 0, 1, 2 }, fun i => if i = 0 then a else if i = 1 then b else c, fun i => if i = 0 then sigma V_point else if i = 1 then Y_point else sigma Y_point, ?_, ?_, ?_, ?_ ⟩ <;> simp +decide [ *, Finset.centerMass ];
  · linarith;
  · norm_num [ ← add_assoc, habc ]

/-
If a point in the square satisfies L2 < 0, L3 < 0, and L4 < 0, it is in UnionRegions.
-/
lemma Cover_Part4_Combined : ∀ p ∈ Region_Square, L2 p < 0 → L3 p < 0 → L4 p < 0 → p ∈ UnionRegions := by
  -- Let p be in Region_Square with L2 p < 0, L3 p < 0, L4 p < 0.
  intros p hp hL2 hL3 hL4
  by_cases hL1 : L1 p ≤ 0;
  · exact Cover_Part4a p hp hL2 hL3 hL1;
  · by_cases hsep : sep p ≤ 0 <;> simp_all +decide [ UnionRegions ];
    · exact Or.inl <| Or.inl <| Or.inr <| Cover_Part4b_Region6a p hp hL2 hL3 hL4 hL1.le hsep;
    · exact Or.inl <| Or.inr <| Cover_Part4b_Region6b p hp hL2 hL3 hL4 hsep.le

/-
The open unit square is contained in the union of the defined regions.
-/
lemma Region_Square_subset_UnionRegions : Region_Square ⊆ UnionRegions := by
  -- By definition of UnionRegions, we know that every point in the square is in one of the regions.
  intros p hp
  apply Classical.byContradiction
  intro h_not_in_union;
  -- By definition of UnionRegions, we know that every point in the square is in one of the regions. Hence, we can apply the disjunction elimination rule.
  apply Classical.byContradiction
  intro h_not_in_union;
  rename_i h_not_in_union'; exact h_not_in_union' <| if h : L2 p ≥ 0 then Cover_Part1 p hp h else if h' : L3 p ≥ 0 then Cover_Part2 p hp h' else if h'' : L4 p ≥ 0 then Cover_Part3 p hp h'' else Cover_Part4_Combined p hp ( lt_of_not_ge h ) ( lt_of_not_ge h' ) ( lt_of_not_ge h'' ) ;

/-
The intersection of Region1 and Region2 is the segment connecting O and V.
-/
lemma Region1_inter_Region2 : Region1 ∩ Region2 = segment ℝ O_point V_point := by
  -- To prove equality of sets �,� we show each � set� is a subset of the other.
  apply Set.ext
  intro p
  simp [Region1, Region2, segment];
  constructor <;> intro h;
  · -- By definition of convex hull, since $p$ is in the convex hull of $\{O, V, \sigma V\}$, there exist coefficients $a, b, c$ such that $a + b + c = 1$ and $p = aO + bV + c\sigma V$.
    obtain ⟨a, b, c, ha, hb, hc, habc⟩ : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • O_point + b • V_point + c • sigma V_point := by
      have h_convex_comb : p ∈ convexHull ℝ {O_point, V_point, sigma V_point} := by
        exact h.1;
      rw [ convexHull_insert ] at h_convex_comb;
      · norm_num [ segment_eq_image ] at h_convex_comb ⊢;
        rcases h_convex_comb with ⟨ i, hi, x, hx, rfl ⟩ ; exact ⟨ 1 - x, by linarith, x * ( 1 - i ), by nlinarith, x * i, by nlinarith, by ring, by ext ; simpa using by ring ⟩ ;
      · norm_num +zetaDelta at *;
    -- Since $p$ is in the convex hull of $\{O, V, X\}$, we have $L_OV p \leq 0$.
    have h_LOV_p_le_0 : L_OV p ≤ 0 := by
      have h_LOV_p_le_0 : ∀ p ∈ convexHull ℝ {O_point, V_point, X_point}, L_OV p ≤ 0 := by
        exact fun p a ↦ Region2_sub_H_neg p a
      generalize_proofs at *; exact h_LOV_p_le_0 p h.2;
    generalize_proofs at *; simp_all +decide [ L_OV ] ; (
    -- Since $c \geq 0$ and $L_OV(\sigma(V)) > 0$, we have $c = 0$.
    have hc_zero : c = 0 := by
      have h_LOV_sigma_V_pos : L_OV (sigma V_point) > 0 := by
        exact L_OV_sigmaV_pos
      generalize_proofs at *; simp_all +decide [ L_OV ] ; (
      unfold O_point V_point sigma at * ; norm_num at * ; nlinarith;)
    generalize_proofs at *; simp_all +decide [ L_OV ] ; (
    exact ⟨ a, ha, b, hb, habc.1, rfl ⟩));
  · rw [ @convexHull_insert ] <;> norm_num [ convexHull_insert ];
    rcases h with ⟨ a, ha, b, hb, hab, rfl ⟩ ; simp_all +decide [ segment_eq_image ] ;
    refine ⟨ ⟨ 0, ⟨ by norm_num, by norm_num ⟩, b, ⟨ hb, by linarith ⟩, ?_ ⟩, ⟨ 0, ⟨ by norm_num, by norm_num ⟩, b, ⟨ hb, by linarith ⟩, ?_ ⟩ ⟩ <;> ext i <;> fin_cases i <;> norm_num [ O_point, V_point, X_point ]

/-
The union of Region1 and Region2 is the convex hull of {O, V, sigma V, X}.
-/
lemma Region12_eq_convexHull : Region1 ∪ Region2 = convexHull ℝ {O_point, V_point, sigma V_point, X_point} := by
  ext p
  constructor;
  · unfold Region1 Region2; intro hp; rcases hp with ( hp | hp ) <;> simp_all +decide [ convexHull_insert ] ;
    · obtain ⟨ q, hq, hpq ⟩ := hp; use sigma V_point; simp_all +decide [ segment_symm ] ;
      exact ⟨ right_mem_segment _ _ _, q, hq, hpq ⟩;
    · rcases hp with ⟨ q, hq, hp ⟩;
      exact ⟨ X_point, right_mem_segment _ _ _, q, hq, hp ⟩;
  · have h_convex_hull : convexHull ℝ {O_point, V_point, sigma V_point, X_point} ⊆ Region2 ∪ Region1 := by
      -- By definition of Region2 and Region1, we know that every point in the convex hull of {O, V, sigma V, X} is in either Region2 or Region1.
      have h_convex_hull : ∀ p ∈ convexHull ℝ {O_point, V_point, sigma V_point, X_point}, L_OV p ≥ 0 → p ∈ Region1 := by
        exact fun p a a_1 ↦ convexHull_sub_Region1_of_pos p a a_1;
      have h_convex_hull : ∀ p ∈ convexHull ℝ {O_point, V_point, sigma V_point, X_point}, L_OV p ≤ 0 → p ∈ Region2 := by
        exact fun p a a_1 ↦ convexHull_sub_Region2_of_neg p a a_1;
      exact fun p hp => if h : L_OV p ≤ 0 then Or.inl ( h_convex_hull p hp h ) else Or.inr ( by solve_by_elim [ le_of_not_ge h ] );
    exact fun h => by simpa only [ Set.union_comm ] using h_convex_hull h;

/-
The first quadrant is a convex set.
-/
def FirstQuadrant : Set Point := {p | 0 ≤ p 0 ∧ 0 ≤ p 1}

lemma FirstQuadrant_convex : Convex ℝ FirstQuadrant := by
  -- To prove convexity, take any two points $x, y \in \mathbb{R}^2_\geq$ and show that the line segment connecting them is also in $\mathbb{R}^2_\geq$.
  intro x hx y hy a b ha hb hab
  simp [FirstQuadrant] at hx hy ⊢;
  constructor <;> nlinarith

/-
The set of points {O, V, sigma V, X} is contained in the first quadrant.
-/
lemma Generators12_in_FirstQuadrant : {O_point, V_point, sigma V_point, X_point} ⊆ FirstQuadrant := by
  simp [FirstQuadrant, Set.subset_def];
  unfold O_point V_point sigma X_point; norm_num [ x1, y1 ] ;
  refine ⟨ ⟨ by positivity, by exact div_nonneg ( sub_nonneg.2 <| Real.sqrt_le_sqrt <| by norm_num ) <| by positivity ⟩, ⟨ by exact div_nonneg ( sub_nonneg.2 <| Real.sqrt_le_sqrt <| by norm_num ) <| by positivity, by positivity ⟩, ?_ ⟩
  generalize_proofs at *;
  linarith [ Classical.choose_spec ‹∃ x : ℝ, 19 / 20 < x ∧ x < 24 / 25 ∧ poly_X x = 0› ]

/-
All points in Region1 ∪ Region2 have non-negative coordinates.
-/
lemma Region12_subset_FirstQuadrant : ∀ p ∈ Region1 ∪ Region2, 0 ≤ p 0 ∧ 0 ≤ p 1 := by
  intro p hp
  have h_convex_hull : p ∈ convexHull ℝ {O_point, V_point, sigma V_point, X_point} := by
    exact Region12_eq_convexHull ▸ hp;
  have h_convex_hull_subset : convexHull ℝ {O_point, V_point, sigma V_point, X_point} ⊆ FirstQuadrant := by
    apply convexHull_min;
    · exact Generators12_in_FirstQuadrant;
    · exact FirstQuadrant_convex;
  exact h_convex_hull_subset h_convex_hull

/-
The point O is an extreme point of Region1 ∪ Region2 and cannot lie in the interior of any unit segment contained in the region.
-/
lemma O_extreme_Region12 : ∀ L, IsUnitSegment L → L ⊆ Region1 ∪ Region2 → O_point ∉ L := by
  intro L hL hL_sub hL_O
  obtain ⟨a, b, hab⟩ := hL;
  -- By Region12_subset_FirstQuadrant, a and b are in FirstQuadrant, so a.0 >= 0, a.1 >= 0, b.0 >= 0, b.1 >= 0.
  have h_a_b_nonneg : 0 ≤ a 0 ∧ 0 ≤ a 1 ∧ 0 ≤ b 0 ∧ 0 ≤ b 1 := by
    have h_a_b_nonneg : ∀ p ∈ openSegment ℝ a b, 0 ≤ p 0 ∧ 0 ≤ p 1 := by
      exact fun p hp => Region12_subset_FirstQuadrant p <| hL_sub <| hab.2 ▸ hp;
    have h_a_b_nonneg : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ (1 - t) * a 0 + t * b 0 ∧ 0 ≤ (1 - t) * a 1 + t * b 1 := by
      intro t ht; specialize h_a_b_nonneg ( ( 1 - t ) • a + t • b ) ; simp_all +decide [ openSegment_eq_image ] ;
      exact h_a_b_nonneg t ht.1 ht.2 rfl;
    have h_a_b_nonneg : Filter.Tendsto (fun t : ℝ => (1 - t) * a 0 + t * b 0) (nhdsWithin 0 (Set.Ioi 0)) (nhds (a 0)) ∧ Filter.Tendsto (fun t : ℝ => (1 - t) * a 1 + t * b 1) (nhdsWithin 0 (Set.Ioi 0)) (nhds (a 1)) := by
      exact ⟨ tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num ), tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num ) ⟩;
    have h_a_b_nonneg : 0 ≤ a 0 ∧ 0 ≤ a 1 := by
      exact ⟨ le_of_tendsto_of_tendsto tendsto_const_nhds h_a_b_nonneg.1 ( Filter.eventually_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ by norm_num, by norm_num ⟩ ) fun t ht => ‹∀ t ∈ Ioo 0 1, 0 ≤ ( 1 - t ) * a 0 + t * b 0 ∧ 0 ≤ ( 1 - t ) * a 1 + t * b 1› t ht |>.1 ), le_of_tendsto_of_tendsto tendsto_const_nhds h_a_b_nonneg.2 ( Filter.eventually_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ by norm_num, by norm_num ⟩ ) fun t ht => ‹∀ t ∈ Ioo 0 1, 0 ≤ ( 1 - t ) * a 0 + t * b 0 ∧ 0 ≤ ( 1 - t ) * a 1 + t * b 1› t ht |>.2 ) ⟩;
    have h_a_b_nonneg : Filter.Tendsto (fun t : ℝ => (1 - t) * a 0 + t * b 0) (nhdsWithin 1 (Set.Iio 1)) (nhds (b 0)) ∧ Filter.Tendsto (fun t : ℝ => (1 - t) * a 1 + t * b 1) (nhdsWithin 1 (Set.Iio 1)) (nhds (b 1)) := by
      exact ⟨ tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num ), tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num ) ⟩;
    exact ⟨ by linarith, by linarith, by exact le_of_tendsto_of_tendsto tendsto_const_nhds h_a_b_nonneg.1 ( Filter.eventually_of_mem ( Ioo_mem_nhdsLT zero_lt_one ) fun t ht => by aesop ), by exact le_of_tendsto_of_tendsto tendsto_const_nhds h_a_b_nonneg.2 ( Filter.eventually_of_mem ( Ioo_mem_nhdsLT zero_lt_one ) fun t ht => by aesop ) ⟩;
  -- Since O = (0,0), we have (1-t)a.0 + tb.0 = 0. Since terms are non-negative and weights are positive, a.0 = 0 and b.0 = 0.
  have h_a_b_zero : a 0 = 0 ∧ b 0 = 0 ∧ a 1 = 0 ∧ b 1 = 0 := by
    -- Since O is in L, there exists a t in (0,1) such that O = (1-t)a + tb.
    obtain ⟨t, ht⟩ : ∃ t ∈ Set.Ioo (0 : ℝ) 1, O_point = (1 - t) • a + t • b := by
      rw [ hab.2 ] at hL_O; rw [ openSegment_eq_image ] at hL_O; aesop;
    have h_a_b_zero : (1 - t) * a 0 + t * b 0 = 0 ∧ (1 - t) * a 1 + t * b 1 = 0 := by
      exact ⟨ by simpa [O_point] using congrArg (fun p : Point => p 0) ht.2.symm,
        by simpa [O_point] using congrArg (fun p : Point => p 1) ht.2.symm ⟩;
    exact ⟨ by nlinarith [ ht.1.1, ht.1.2 ], by nlinarith [ ht.1.1, ht.1.2 ], by nlinarith [ ht.1.1, ht.1.2 ], by nlinarith [ ht.1.1, ht.1.2 ] ⟩;
  simp_all +decide [ show a = 0 from by ext i; fin_cases i <;> tauto, show b = 0 from by ext i; fin_cases i <;> tauto ]

/-
The sum of coordinates for any point in Region1 ∪ Region2 is at most the sum of coordinates of V.
-/
lemma Region12_sum_le_V_sum : ∀ p ∈ Region1 ∪ Region2, p 0 + p 1 ≤ V_point 0 + V_point 1 := by
  intro p hp
  have h_convex_hull : p ∈ convexHull ℝ {O_point, V_point, sigma V_point, X_point} := by
    exact Region12_eq_convexHull ▸ hp;
  -- By definition of convex hull, there exist weights $w_0, w_1, w_2, w_3$ such that $p = w_0 • O_point + w_1 • V_point + w_2 • sigma V_point + w_3 • X_point$ and $w_0 + w_1 + w_2 + w_3 = 1$.
  obtain ⟨w, hw⟩ : ∃ w : Fin 4 → ℝ, (∑ i, w i = 1) ∧ (0 ≤ w 0 ∧ 0 ≤ w 1 ∧ 0 ≤ w 2 ∧ 0 ≤ w 3) ∧ p = w 0 • O_point + w 1 • V_point + w 2 • sigma V_point + w 3 • X_point := by
    rw [ convexHull_insert ] at h_convex_hull;
    · norm_num [ segment_eq_image ] at h_convex_hull ⊢;
      rcases h_convex_hull with ⟨ i, hi, x, hx, rfl ⟩;
      rw [ convexHull_insert ] at hi <;> norm_num at *;
      rcases hi with ⟨ j, hj, hi ⟩ ; rw [ segment_eq_image ] at hj hi; norm_num at hj hi ⊢;
      rcases hj with ⟨ y, hy, rfl ⟩ ; rcases hi with ⟨ z, hz, rfl ⟩ ; use fun i => if i = 0 then 1 - x else if i = 1 then x * ( 1 - z ) else if i = 2 then x * z * ( 1 - y ) else x * z * y; simp +decide [ Fin.sum_univ_four ] ; ring_nf; norm_num [ hx, hy, hz ] ;
      exact ⟨ ⟨ by nlinarith, by nlinarith [ mul_nonneg hx.1 hz.1 ], by exact mul_nonneg ( mul_nonneg hx.1 hz.1 ) hy.1 ⟩, by ext i; fin_cases i <;> norm_num <;> ring ⟩;
    · norm_num;
  norm_num [ hw.2.2, Fin.sum_univ_four ] at *;
  norm_num [ O_point, V_point, sigma, X_point ] at *;
  unfold x1 at *;
  have := Classical.choose_spec exists_root_x1;
  nlinarith [ show 0 ≤ w 1 * Real.sqrt 6 by exact mul_nonneg hw.2.2.1 ( Real.sqrt_nonneg _ ), show 0 ≤ w 2 * Real.sqrt 6 by exact mul_nonneg hw.2.2.2.1 ( Real.sqrt_nonneg _ ), show 0 ≤ w 3 * Real.sqrt 6 by exact mul_nonneg hw.2.2.2.2 ( Real.sqrt_nonneg _ ), Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ) ]

/-
If the origin is in the open segment between two points in the first quadrant, then both points must be the origin.
-/
lemma origin_in_openSegment_FirstQuadrant_implies_endpoints_zero : ∀ a b : Point, a ∈ FirstQuadrant → b ∈ FirstQuadrant → O_point ∈ openSegment ℝ a b → a = O_point ∧ b = O_point := by
  -- By definition of open segment, there exists some $t \in (0, 1)$ such that $O_point = (1 - t) • a + t • b$.
  intro a b ha hb h_open_segment
  obtain ⟨t, ht₀, ht₁⟩ : ∃ t ∈ Set.Ioo (0 : ℝ) 1, O_point = (1 - t) • a + t • b := by
    rw [ openSegment_eq_image ] at h_open_segment ; aesop;
  -- By definition of open segment, we have $0 = (1 - t) * a 0 + t * b 0$ and $0 = (1 - t) * a 1 + t * b 1$.
  have h_eq0 : 0 = (1 - t) * a 0 + t * b 0 := by
    simpa [O_point] using congrArg (fun p : Point => p 0) ht₁
  have h_eq1 : 0 = (1 - t) * a 1 + t * b 1 := by
    simpa [O_point] using congrArg (fun p : Point => p 1) ht₁;
  -- Since $a$ and $b$ are in the first quadrant, their coordinates are non-negative. Therefore, the only way for the equations $0 = (1 - t) * a 0 + t * b 0$ and $0 = (1 - t) * a 1 + t * b 1$ to hold is if $a 0 = 0$ and $b 0 = 0$, and similarly for $a 1$ and $b 1$.
  have h_a0_b0 : a 0 = 0 ∧ b 0 = 0 := by
    constructor <;> nlinarith [ ha.1, ha.2, hb.1, hb.2, ht₀.1, ht₀.2 ]
  have h_a1_b1 : a 1 = 0 ∧ b 1 = 0 := by
    constructor <;> nlinarith [ ht₀.1, ht₀.2, ha.2, hb.2 ];
  exact ⟨ by ext i; fin_cases i <;> tauto, by ext i; fin_cases i <;> tauto ⟩

/-
The sum of the coordinates of V is positive.
-/
lemma sum_V_pos : V_point 0 + V_point 1 > 0 := by
  exact add_pos ( by rw [ show V_point 0 = ( Real.sqrt 6 + Real.sqrt 2 ) / 4 by rfl ] ; positivity ) ( by rw [ show V_point 1 = ( Real.sqrt 6 - Real.sqrt 2 ) / 4 by rfl ] ; exact div_pos ( sub_pos.mpr ( Real.lt_sqrt_of_sq_lt ( by norm_num ) ) ) ( by norm_num ) ) ;

/-
The sum of the coordinates of V is strictly greater than x1.
-/
lemma sum_V_gt_x1 : V_point 0 + V_point 1 > x1 := by
  unfold V_point x1;
  have := Classical.choose_spec exists_root_x1;
  norm_num [ poly_X ] at * ; nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ) ]

/-
If a point in Region1 ∪ Region2 has the maximum possible coordinate sum, it must lie on the segment connecting V and sigma V.
-/
lemma Region12_max_sum_implies_segment : ∀ p ∈ Region1 ∪ Region2, p 0 + p 1 = V_point 0 + V_point 1 → p ∈ segment ℝ V_point (sigma V_point) := by
  -- By definition of Region1 ∪ Region2, if p is in this union, then p can be written as a convex combination of O, V, sigma V, and X.
  intro p hp hsum
  obtain ⟨w_O, w_V, w_SV, w_X, hwO, hwV, hwSV, hwX, hw_sum, hp_eq⟩ : ∃ w_O w_V w_SV w_X : ℝ, 0 ≤ w_O ∧ 0 ≤ w_V ∧ 0 ≤ w_SV ∧ 0 ≤ w_X ∧ w_O + w_V + w_SV + w_X = 1 ∧ p = w_O • O_point + w_V • V_point + w_SV • sigma V_point + w_X • X_point := by
    have h_convex : p ∈ convexHull ℝ {O_point, V_point, sigma V_point, X_point} := by
      exact Region12_eq_convexHull ▸ hp;
    rw [ convexHull_insert ] at h_convex;
    · norm_num [ segment_eq_image ] at h_convex;
      rcases h_convex with ⟨ q, hq, x, hx, rfl ⟩;
      rw [ convexHull_insert ] at hq;
      · norm_num [ segment_eq_image ] at hq;
        rcases hq with ⟨ i, hi, j, hj, rfl ⟩;
        exact ⟨ 1 - x, x * ( 1 - j ), x * j * ( 1 - i ), x * j * i, by linarith, by nlinarith, by nlinarith [ mul_nonneg hx.1 hj.1 ], by nlinarith [ mul_nonneg hx.1 hj.1 ], by linarith, by ext ; norm_num ; ring ⟩;
      · norm_num +zetaDelta at *;
    · norm_num +zetaDelta at *;
  -- Since S(V) > 0 and S(V) - x1 > 0, we have -w_O * S(V) - w_X * (S(V) - x1) = 0 implies w_O = 0 and w_X = 0.
  have h_weights_zero : w_O = 0 ∧ w_X = 0 := by
    have h_S_V_pos : V_point 0 + V_point 1 > 0 := by
      exact sum_V_pos
    have h_S_V_gt_x1' : V_point 0 + V_point 1 > x1 := by
      exact sum_V_gt_x1
    have h_S_V_gt_x1 : V_point 0 + V_point 1 - x1 > 0 := by
      linarith
    have hsum_weights :
        (w_V + w_SV) * (V_point 0 + V_point 1) + w_X * x1 =
          V_point 0 + V_point 1 := by
      simpa [hp_eq, O_point, X_point, sigma, add_assoc, add_comm, add_left_comm, mul_add, add_mul] using hsum
    have h_eq : -w_O * (V_point 0 + V_point 1) - w_X * (V_point 0 + V_point 1 - x1) = 0 := by
      nlinarith [hsum_weights, hw_sum]
    constructor <;> nlinarith [hwO, hwX, h_S_V_pos, h_S_V_gt_x1, h_eq]
  rw [ segment_eq_image ]
  refine ⟨ w_SV, ⟨ hwSV, by nlinarith [ hw_sum, h_weights_zero.1, h_weights_zero.2 ] ⟩, ?_ ⟩
  rw [ hp_eq, h_weights_zero.1, h_weights_zero.2 ]
  simp only [ zero_smul, zero_add, add_zero ]
  have hwV_eq : 1 - w_SV = w_V := by nlinarith [ hw_sum, h_weights_zero.1, h_weights_zero.2 ]
  rw [ hwV_eq ]

/-
The point V is an extreme point of Region1 ∪ Region2 and cannot lie in the interior of any unit segment contained in the region.
-/
lemma V_extreme_Region12 : ∀ L, IsUnitSegment L → L ⊆ Region1 ∪ Region2 → V_point ∉ L := by
  intro L hL hL'V;
  -- By Lemma 1, if L is a unit segment in Region1 ∪ Region2 and V ∈ L, then L must be the open segment between V and sigma V.
  obtain ⟨a, b, hab⟩ : ∃ a b : Point, a ∈ Region1 ∪ Region2 ∧ b ∈ Region1 ∪ Region2 ∧ L = openSegment ℝ a b ∧ dist a b = 1 := by
    obtain ⟨a, b, hab⟩ : ∃ a b : Point, L = openSegment ℝ a b ∧ dist a b = 1 := by
      cases hL ; tauto;
    refine ⟨a, b, ?_, ?_, hab.1, hab.2⟩
    · have h_a : Filter.Tendsto (fun t : ℝ => (1 - t) • a + t • b) (nhdsWithin 0 (Set.Ioi 0)) (nhds a) := by
        exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ ( by norm_num ) );
      have h_a : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), (1 - t) • a + t • b ∈ Region1 ∪ Region2 := by
        filter_upwards [ Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, zero_lt_one ⟩ ] with t ht using hL'V <| by rw [ hab.1, openSegment_eq_image ] ; exact ⟨ t, ⟨ by linarith [ ht.1 ], by linarith [ ht.2 ] ⟩, by ext i; fin_cases i <;> norm_num ⟩ ;
      have h_a : IsClosed (Region1 ∪ Region2) := by
        have h_closed : IsClosed (convexHull ℝ {O_point, V_point, sigma V_point, X_point}) := by
          have h_closed : IsCompact (convexHull ℝ {O_point, V_point, sigma V_point, X_point}) := by
            have h_finite : Set.Finite {O_point, V_point, sigma V_point, X_point} := by
              exact Set.toFinite _
            exact h_finite.isCompact_convexHull ℝ;
          exact h_closed.isClosed;
        convert h_closed using 1;
        exact Region12_eq_convexHull;
      exact h_a.mem_of_tendsto ‹_› ‹_›
    · have h_b : Filter.Tendsto (fun t : ℝ => (1 - t) • a + t • b) (nhdsWithin 1 (Set.Iio 1)) (nhds b) := by
        exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num );
      have h_b : ∀ᶠ t : ℝ in nhdsWithin 1 (Set.Iio 1), (1 - t) • a + t • b ∈ Region1 ∪ Region2 := by
        filter_upwards [ Ioo_mem_nhdsLT zero_lt_one ] with t ht using hL'V <| by rw [ hab.1, openSegment_eq_image ] ; exact ⟨ t, ⟨ by linarith [ ht.1 ], by linarith [ ht.2 ] ⟩, by ext i; fin_cases i <;> simp +decide [ ht.1.le, ht.2.le ] ⟩ ;
      have h_b : IsClosed (Region1 ∪ Region2) := by
        have h_closed : IsClosed (convexHull ℝ {O_point, V_point, sigma V_point, X_point}) := by
          have h_closed : IsCompact (convexHull ℝ {O_point, V_point, sigma V_point, X_point}) := by
            have h_finite : Set.Finite {O_point, V_point, sigma V_point, X_point} := by
              exact Set.toFinite _;
            exact h_finite.isCompact_convexHull ℝ;
          exact h_closed.isClosed;
        convert h_closed using 1;
        exact Region12_eq_convexHull;
      exact h_b.mem_of_tendsto ‹_› ‹_›
  -- By Lemma 2, if V ∈ L, then f(a) = f(V) and f(b) = f(V), where f(p) = p 0 + p 1.
  by_cases hV : V_point ∈ L
  · have hfa : a 0 + a 1 = V_point 0 + V_point 1 := by
      have hfa : a 0 + a 1 ≤ V_point 0 + V_point 1 ∧ b 0 + b 1 ≤ V_point 0 + V_point 1 := by
        exact ⟨ Region12_sum_le_V_sum a hab.1, Region12_sum_le_V_sum b hab.2.1 ⟩;
      -- Since V is in L, we can write V as a convex combination of a and b. That is, there exists some t in (0,1) such that V = (1-t)a + tb.
      obtain ⟨t, ht⟩ : ∃ t ∈ Set.Ioo (0 : ℝ) 1, V_point = (1 - t) • a + t • b := by
        rw [ hab.2.2.1 ] at hV;
        rw [ openSegment_eq_image ] at hV;
        simpa [ eq_comm ] using hV;
      norm_num [ ht.2 ] at *;
      nlinarith
    have hfb : b 0 + b 1 = V_point 0 + V_point 1 := by
      obtain ⟨t, ht⟩ : ∃ t ∈ Set.Ioo (0 : ℝ) 1, V_point = (1 - t) • a + t • b := by
        rw [ hab.2.2.1, openSegment_eq_image ] at hV;
        simpa [ eq_comm ] using hV;
      have h0 := congrArg (fun p : Point => p 0) ht.2
      have h1 := congrArg (fun p : Point => p 1) ht.2
      norm_num at h0 h1
      norm_num at *
      nlinarith [ ht.1.1, ht.1.2 ]
    -- By Lemma 3, if f(a) = f(V) and f(b) = f(V), then a and b are in the segment between V and sigma V.
    have ha_sigmaV : a ∈ segment ℝ V_point (sigma V_point) := by
      apply Region12_max_sum_implies_segment a hab.left hfa
    have hb_sigmaV : b ∈ segment ℝ V_point (sigma V_point) := by
      exact Region12_max_sum_implies_segment b hab.2.1 hfb;
    -- Since dist a b = 1 and dist V (sigma V) = 1, {a, b} = {V, sigma V}.
    have h_eq : a = V_point ∧ b = sigma V_point ∨ a = sigma V_point ∧ b = V_point := by
      have h_eq : dist a b = dist V_point (sigma V_point) := by
        have h_eq : dist V_point (sigma V_point) = 1 := by
          exact dist_V_sigma_V;
        linarith;
      rw [ segment_eq_image ] at *;
      rcases ha_sigmaV with ⟨ θ₁, ⟨ hθ₁₀, hθ₁₁ ⟩, rfl ⟩ ; rcases hb_sigmaV with ⟨ θ₂, ⟨ hθ₂₀, hθ₂₁ ⟩, rfl ⟩ ; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] at *;
      -- Since the square roots are equal, the expressions inside must be equal. So, the sum of the squares of the differences must be equal to the sum of the squares of the differences between V_point and sigma V_point.
      have h_eq_squares : (θ₁ - θ₂)^2 * ((V_point 0 - sigma V_point 0)^2 + (V_point 1 - sigma V_point 1)^2) = (V_point 0 - sigma V_point 0)^2 + (V_point 1 - sigma V_point 1)^2 := by
        rw [ Real.sqrt_inj ( by positivity ) ( by positivity ) ] at h_eq ; linarith;
      -- Since the sum of squares is non-zero, we can divide both sides by it, leading to (θ₁ - θ₂)^2 = 1.
      have h_diff_squares : (θ₁ - θ₂)^2 = 1 := by
        have h_nonzero : (V_point 0 - sigma V_point 0)^2 + (V_point 1 - sigma V_point 1)^2 ≠ 0 := by
          unfold sigma; norm_num [ V_point ] ;
          ring_nf; norm_num;
        exact mul_left_cancel₀ h_nonzero <| by linear_combination' h_eq_squares;
      cases eq_or_eq_neg_of_sq_eq_sq ( θ₁ - θ₂ ) 1 ( by linarith ) <;> simp_all +decide [ sub_eq_iff_eq_add ];
      · norm_num [ show θ₂ = 0 by linarith ] at *;
        norm_num [ ← h_eq ] at *;
      · norm_num [ show θ₂ = 1 by linarith ] at *;
        norm_num [ ← h_eq ] at *;
    rcases h_eq with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ )
    · rw [hab.2.2.1] at hV
      change ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a + b = 1 ∧ a • V_point + b • sigma V_point = V_point at hV
      obtain ⟨ a, b, ha, hb, hab, h ⟩ := hV;
      have h0 := congrArg (fun p : Point => p 0) h
      have h1 := congrArg (fun p : Point => p 1) h
      have h0' : a * V_point 0 + b * V_point 1 = V_point 0 := by
        simpa [sigma] using h0
      have h1' : a * V_point 1 + b * V_point 0 = V_point 1 := by
        simpa [sigma] using h1
      nlinarith [ha, hb, hab, h0', h1', V_point_1_lt_V_point_0]
    · rw [hab.2.2.1] at hV
      change ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a + b = 1 ∧ a • sigma V_point + b • V_point = V_point at hV
      obtain ⟨ a, b, ha, hb, hab, h ⟩ := hV;
      have h0 := congrArg (fun p : Point => p 0) h
      have h1 := congrArg (fun p : Point => p 1) h
      have h0' : a * V_point 1 + b * V_point 0 = V_point 0 := by
        simpa [sigma] using h0
      have h1' : a * V_point 0 + b * V_point 1 = V_point 1 := by
        simpa [sigma] using h1
      nlinarith [ha, hb, hab, h0', h1', V_point_1_lt_V_point_0]
  · exact hV

/-
The union of Region1 and Region2 is blocked by S_finite.
-/
lemma Region12_blocking : IsBlocking S_finite (Region1 ∪ Region2) := by
  -- Apply the blocking_union_lemma with the given conditions.
  have h_blocking_union : IsBlocking S_finite (Region1 ∪ Region2) := by
    have h_closed : IsClosed Region1 ∧ IsClosed Region2 := by
      -- The convex hull of a finite set of points in a finite-dimensional space is closed.
      have h_convex_hull_closed : ∀ (s : Set Point), s.Finite → IsClosed (convexHull ℝ s) := by
        intro s hs_finite
        have h_convex_hull_compact : IsCompact (convexHull ℝ s) := by
          exact hs_finite.isCompact_convexHull ℝ;
        exact h_convex_hull_compact.isClosed;
      exact ⟨ h_convex_hull_closed _ <| Set.toFinite _, h_convex_hull_closed _ <| Set.toFinite _ ⟩
    have h_blocked : IsBlocking S_finite Region1 ∧ IsBlocking S_finite Region2 := by
      exact ⟨ by exact Region1_blocking;, by exact Region2_blocking; ⟩
    have h_inter : Region1 ∩ Region2 = segment ℝ O_point V_point := by
      exact Region1_inter_Region2
    apply blocking_union_lemma;
    · exact h_closed.1;
    · exact h_closed.2;
    · exact h_blocked.1;
    · exact h_blocked.2;
    · intro x hx
      rw [h_inter] at hx
      obtain ⟨hx_segment, hx_extreme⟩ : x ∈ segment ℝ O_point V_point ∧ (x = O_point ∨ x = V_point ∨ x ∈ openSegment ℝ O_point V_point) := by
        rw [ segment_eq_image ] at hx ⊢;
        rcases hx with ⟨ θ, ⟨ hθ₀, hθ₁ ⟩, rfl ⟩ ; by_cases hθ : θ = 0 <;> by_cases hθ' : θ = 1 <;> simp_all +decide [ openSegment_eq_image ] ;
        · exact ⟨ 0, by norm_num ⟩;
        · exact ⟨ 1, by norm_num ⟩;
        · exact ⟨ ⟨ θ, ⟨ hθ₀, hθ₁ ⟩, rfl ⟩, Or.inr <| Or.inr <| ⟨ θ, ⟨ lt_of_le_of_ne hθ₀ <| Ne.symm hθ, lt_of_le_of_ne hθ₁ hθ' ⟩, rfl ⟩ ⟩;
      rcases hx_extreme with ( rfl | rfl | hx_extreme ) <;> norm_num [ segment_eq_image ] at hx_segment ⊢;
      · exact Or.inr fun L hL hL' hL'' => by have := O_extreme_Region12 L hL hL' hL''; contradiction;
      · exact Or.inr fun L hL hL' hL'' => by have := V_extreme_Region12 L hL hL' hL''; contradiction;
      · exact Or.inl ⟨ segment1, by unfold S_finite; norm_num, hx_extreme ⟩;
  exact h_blocking_union

/-
Region12 is Region1 union Region2. Region123 is Region12 union Region3.
-/
def Region12 : Set Point := Region1 ∪ Region2

def Region123 : Set Point := Region12 ∪ Region3

/-
Define L_sep and prove its signs at the vertices O, V, sigma V, X, sigma X.
-/
noncomputable def L_sep (p : Point) : ℝ := V_point 0 * p 0 - V_point 1 * p 1

lemma L_sep_O : L_sep O_point = 0 := by
  exact show V_point 0 * 0 - V_point 1 * 0 = 0 by ring;

lemma L_sep_V_pos : L_sep V_point > 0 := by
  unfold L_sep V_point; ring_nf;
  simp +zetaDelta at *;
  nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ) ]

lemma L_sep_sigma_V : L_sep (sigma V_point) = 0 := by
  unfold L_sep sigma V_point
  skip;
  ring!

lemma L_sep_X_pos : L_sep X_point > 0 := by
  unfold L_sep;
  unfold V_point X_point;
  unfold x1;
  have := Classical.choose_spec exists_root_x1;
  norm_num [ poly_X ] at *;
  exact mul_pos ( by positivity ) ( by linarith )

lemma L_sep_sigma_X_neg : L_sep (sigma X_point) < 0 := by
  -- By definition of $L_{\text{sep}}$, we have $L_{\text{sep}}(\sigma X) = V_x \cdot 0 - V_y \cdot x_1$.
  have h_sep_sigma_X_def : L_sep (sigma X_point) = V_point 0 * 0 - V_point 1 * x1 := by
    exact rfl;
  -- Since $V_point 1$ and $x1$ are both positive, their product $V_point 1 * x1$ is also positive.
  have h_pos : 0 < V_point 1 * x1 := by
    have h_pos : 0 < V_point 1 ∧ 0 < x1 := by
      have h_V1_pos : 0 < V_point 1 := by
        exact div_pos ( sub_pos.mpr ( Real.lt_sqrt_of_sq_lt ( by norm_num ) ) ) ( by norm_num )
      have h_x1_pos : 0 < x1 := by
        exact mul_pos ( sub_pos.mpr x1_prop.1 ) ( sub_pos.mpr x1_prop.2.1 ) |> fun h => by nlinarith [ pow_pos ( sub_pos.mpr x1_prop.1 ) 3, pow_pos ( sub_pos.mpr x1_prop.2.1 ) 3 ] ;
      exact ⟨h_V1_pos, h_x1_pos⟩;
    exact mul_pos h_pos.left h_pos.right;
  linarith [ h_pos ]

/-
L_sep is non-negative on Region1.
-/
lemma Region1_sub_L_sep_ge_0 : ∀ p ∈ Region1, L_sep p ≥ 0 := by
  -- Since $L_{\text{sep}}$ is affine and its values at the vertices $O$, $V$, and $\sigma V$ are non-negative, it is non-negative on their convex hull.
  have h_affine : ∀ p ∈ convexHull ℝ {O_point, V_point, sigma V_point}, L_sep p ≥ 0 := by
    intro p hp
    have h_convex_comb : ∃ (a b c : ℝ), a + b + c = 1 ∧ 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ p = a • O_point + b • V_point + c • sigma V_point := by
      rw [ convexHull_insert ] at hp;
      · norm_num [ segment_eq_image ] at hp;
        rcases hp with ⟨ i, ⟨ hi₀, hi₁ ⟩, x, ⟨ hx₀, hx₁ ⟩, rfl ⟩ ; exact ⟨ 1 - x, x * ( 1 - i ), x * i, by ring, by nlinarith, by nlinarith, by nlinarith, by ext ; simpa using by ring ⟩ ;
      · norm_num +zetaDelta at *
    obtain ⟨ a, b, c, h₁, h₂, h₃, h₄, rfl ⟩ := h_convex_comb; unfold L_sep; norm_num [ Fin.sum_univ_two ] ;
    unfold O_point V_point sigma; norm_num; ring_nf;
    norm_num [ ← Real.sqrt_mul ] ; nlinarith [ Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ), Real.sq_sqrt ( show 0 ≤ 2 by norm_num ) ] ;
  intro p hp
  exact h_affine p (by simpa [Region1] using hp)

/-
L_sep is non-negative on Region2.
-/
lemma Region2_sub_L_sep_ge_0 : ∀ p ∈ Region2, L_sep p ≥ 0 := by
  intro p hp
  have h_convex : p ∈ convexHull ℝ {O_point, V_point, X_point} := by
    simpa [Region2] using hp
  rw [ mem_convexHull_iff ] at h_convex;
  specialize h_convex { q | 0 ≤ L_sep q } ?_ ?_ <;> norm_num at *;
  · norm_num [ Set.insert_subset_iff, L_sep_O, L_sep_V_pos, L_sep_X_pos ];
    exact ⟨ le_of_lt ( L_sep_V_pos ), le_of_lt ( L_sep_X_pos ) ⟩;
  · intro x hx y hy a b ha hb hab;
    unfold L_sep at *; simp_all +decide [ Fin.sum_univ_two ] ;
    nlinarith;
  · exact h_convex

/-
L_sep is non-positive on Region3.
-/
lemma Region3_sub_L_sep_le_0 : ∀ p ∈ Region3, L_sep p ≤ 0 := by
  intro p hp
  obtain ⟨a, b, c, ha, hb, hc, habc, hp_eq⟩ : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • O_point + b • sigma V_point + c • sigma X_point := by
    obtain ⟨a, b, c, ha, hb, hc, habc, hp_eq⟩ : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • O_point + b • sigma V_point + c • sigma X_point := by
      have h_convex : p ∈ convexHull ℝ {O_point, sigma V_point, sigma X_point} := hp
      rw [ convexHull_insert ] at h_convex
      focus
        generalize_proofs at *
      · norm_num [ segment_eq_image ] at h_convex ⊢
        generalize_proofs at *;
        rcases h_convex with ⟨ i, hi, x, hx, rfl ⟩ ; exact ⟨ 1 - x, by linarith, x * ( 1 - i ), by nlinarith, x * i, by nlinarith, by ring, by ext ; simpa using by ring ⟩ ;
      · norm_num +zetaDelta at *
    generalize_proofs at *;
    use a, b, c;
  -- Substitute the expression for p into L_sep and use the known values of L_sep at the vertices.
  have hL_sep_p : L_sep p = a * L_sep O_point + b * L_sep (sigma V_point) + c * L_sep (sigma X_point) := by
    unfold L_sep; norm_num [ hp_eq ] ; ring;
  exact hL_sep_p.symm ▸ by nlinarith [ L_sep_O, L_sep_sigma_V, L_sep_sigma_X_neg ] ;

/-
L_sep is non-negative on Region12.
-/
lemma Region12_sub_L_sep_ge_0 : ∀ p ∈ Region12, L_sep p ≥ 0 := by
  have h_L_sep_nonneg : ∀ p ∈ Region1, L_sep p ≥ 0 := by
    apply Region1_sub_L_sep_ge_0
    skip
  have h_L_sep_nonneg2 : ∀ p ∈ Region2, L_sep p ≥ 0 := by
    exact fun p a ↦ Region2_sub_L_sep_ge_0 p a
  intro p hp
  obtain hp1 | hp2 := hp
  · exact h_L_sep_nonneg p hp1
  · exact h_L_sep_nonneg2 p hp2

/-
The intersection of Region3 and the line L_sep=0 is contained in the segment [O, sigma V].
-/
lemma Region3_inter_L_sep_zero : Region3 ∩ {p | L_sep p = 0} ⊆ segment ℝ O_point (sigma V_point) := by
  -- Let p be a point in the intersection. Then p can be written as a convex combination of O, sigma V, and sigma X.
  intro p hp
  obtain ⟨a, b, c, ha, hb, hc, habc, hp_eq⟩ : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • O_point + b • (sigma V_point) + c • (sigma X_point) := by
    -- By definition of convex hull, since p is in the convex hull of {O, sigma V, sigma X}, there exist non-negative weights a, b, c such that a + b + c = 1 and p = a • O + b • sigma V + c • sigma X.
    have h_convex : p ∈ convexHull ℝ ({O_point, sigma V_point, sigma X_point} : Set Point) := by
      exact mem_of_mem_inter_left hp;
    rw [ convexHull_insert ] at h_convex;
    · norm_num [ segment_eq_image ] at h_convex;
      rcases h_convex with ⟨ i, hi, x, hx, rfl ⟩ ; exact ⟨ 1 - x, x * ( 1 - i ), x * i, by linarith, by nlinarith, by nlinarith, by linarith, by ext ; simpa using by ring ⟩ ;
    · exact ⟨ _, Set.mem_insert _ _ ⟩;
  -- Since $L_{\text{sep}}(p) = 0$, we have $c * L_{\text{sep}}(\sigma X) = 0$. Given that $L_{\text{sep}}(\sigma X) < 0$, it follows that $c = 0$.
  have hc_zero : c = 0 := by
    have hc_zero : c * L_sep (sigma X_point) = 0 := by
      have hc_zero : L_sep p = a * L_sep O_point + b * L_sep (sigma V_point) + c * L_sep (sigma X_point) := by
        rw [hp_eq]; ring_nf;
        unfold L_sep; norm_num; ring;
      simp_all +decide [ L_sep_O, L_sep_sigma_V ];
    exact mul_left_cancel₀ ( show L_sep ( sigma X_point ) ≠ 0 from ne_of_lt ( by exact
      L_sep_sigma_X_neg ) ) ( by linarith );
  simp_all +decide [ segment_eq_image ];
  exact ⟨ b, ⟨ hb, by linarith ⟩, by rw [ ← eq_sub_iff_add_eq' ] at habc; aesop ⟩

/-
The intersection of Region12 and Region3 is contained in segment O (sigma V).
-/
lemma Region12_inter_Region3_subset_segment : Region12 ∩ Region3 ⊆ segment ℝ O_point (sigma V_point) := by
  -- By definition of Region12 and Region3, if p is in both, then L_sep p = 0.
  intros p hp
  have hL_sep : L_sep p = 0 := by
    exact le_antisymm ( le_of_not_gt fun h => by linarith [ hp.2, Region3_sub_L_sep_le_0 p hp.2 ] ) ( le_of_not_gt fun h => by linarith [ hp.1, Region12_sub_L_sep_ge_0 p hp.1 ] );
  exact Region3_inter_L_sep_zero ⟨ hp.2, hL_sep ⟩

/-
Region12 is blocked by S_finite.
-/
lemma Region12_blocking_thm : IsBlocking S_finite Region12 := by
  -- Apply the lemma that states the union of Region1 and Region2 is blocked by S_finite.
  apply Region12_blocking

/-
Region3 is contained in the first quadrant.
-/
lemma Region3_subset_FirstQuadrant : Region3 ⊆ FirstQuadrant := by
  refine convexHull_min ?_ ?_;
  · rintro p ( rfl | rfl | rfl ) <;> unfold FirstQuadrant <;> norm_num [ O_point, sigma, V_point, X_point ];
    · constructor <;> nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ) ];
    · linarith [ x1_prop.1 ];
  · exact FirstQuadrant_convex

/-
Region123 is contained in the first quadrant.
-/
lemma Region123_subset_FirstQuadrant : Region123 ⊆ FirstQuadrant := by
  -- The union of two subsets is a subset.
  apply Set.union_subset
  · exact Region12_subset_FirstQuadrant
  · exact Region3_subset_FirstQuadrant

/-
L1 is non-positive on Region123.
-/
lemma Region123_sub_L1_le_0 : ∀ p ∈ Region123, L1 p ≤ 0 := by
  -- By definition of Region123, p is either in Region12 or in Region3.
  intro p hp
  cases' hp with hp12 hp3;
  · -- Since p is in Region12, we know that p's coordinates are non-negative and their sum is at most V_point 0 + V_point 1.
    have h_coords : 0 ≤ p 0 ∧ 0 ≤ p 1 ∧ p 0 + p 1 ≤ V_point 0 + V_point 1 := by
      exact ⟨ Region12_subset_FirstQuadrant _ hp12 |>.1, Region12_subset_FirstQuadrant _ hp12 |>.2, Region12_sum_le_V_sum _ hp12 ⟩;
    exact sub_nonpos_of_le ( by linarith [ show V_point 0 + V_point 1 > 0 from sum_V_pos ] );
  · -- By definition of Region3, we know that p can be written as a convex combination of O, sigma V, and sigma X.
    obtain ⟨a, b, c, ha, hb, hc, habc, hp⟩ : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • O_point + b • (sigma V_point) + c • (sigma X_point) := by
      obtain ⟨a, b, c, ha, hb, hc, habc, hp⟩ : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • O_point + b • sigma V_point + c • sigma X_point := by
        have h_convex : p ∈ convexHull ℝ {O_point, sigma V_point, sigma X_point} := by
          exact hp3
        rw [ convexHull_insert ] at h_convex;
        · norm_num [ segment_eq_image ] at h_convex;
          rcases h_convex with ⟨ i, hi, x, hx, rfl ⟩ ; exact ⟨ 1 - x, x * ( 1 - i ), x * i, by linarith, by nlinarith, by nlinarith, by linarith, by ext ; simpa using by ring ⟩ ;
        · exact ⟨ _, Set.mem_insert _ _ ⟩;
      use a, b, c;
    -- Substitute the values of L1 at O, sigma V, and sigma X into the equation.
    have hL1_values : L1 O_point = -(V_point 0 + V_point 1) ∧ L1 (sigma V_point) = 0 ∧ L1 (sigma X_point) = x1 - (V_point 0 + V_point 1) := by
      unfold L1; norm_num [ O_point, X_point, sigma ] ; ring;
    -- Substitute the values of L1 at O, sigma V, and sigma X into the equation and simplify.
    have hL1_simplified : L1 p = a * (-(V_point 0 + V_point 1)) + b * 0 + c * (x1 - (V_point 0 + V_point 1)) := by
      rw [ hp, ← hL1_values.1, ← hL1_values.2.1, ← hL1_values.2.2 ];
      unfold L1; norm_num [ add_assoc ] ; ring_nf;
      grind;
    nlinarith [ show V_point 0 + V_point 1 > 0 from sum_V_pos, show x1 < V_point 0 + V_point 1 from by linarith [ show V_point 0 + V_point 1 > x1 from sum_V_gt_x1 ] ]

/-
L1 is negative at O.
-/
lemma L1_O_neg : L1 O_point < 0 := by
  convert neg_lt_zero.mpr ( sum_V_pos ) using 1;
  unfold L1 O_point; ring_nf;
  erw [ Matrix.cons_val_succ' ] ; norm_num

/-
L1 is negative at X.
-/
lemma L1_X_neg : L1 X_point < 0 := by
  -- By definition of $L1$, we know that $L1 X_point = x1 - (V_point 0 + V_point 1)$.
  have hL1_X : L1 X_point = x1 - (V_point 0 + V_point 1) := by
    unfold L1
    simp [X_point];
  exact hL1_X ▸ sub_neg_of_lt ( by linarith [ sum_V_gt_x1 ] )

/-
L1 is negative at sigma X.
-/
lemma L1_sigma_X_neg : L1 (sigma X_point) < 0 := by
  -- Substitute the values of sigma X_point into L1 and simplify.
  have hL1_sigma_X : L1 (sigma X_point) = x1 - (V_point 0 + V_point 1) := by
    unfold sigma L1; norm_num;
    exact show 0 + x1 = x1 from by ring;
  exact hL1_sigma_X ▸ sub_neg_of_lt ( by linarith [ sum_V_gt_x1 ] )

/-
The intersection of Region12 and the line L1=0 is the segment V-sigma(V).
-/
lemma Region12_inter_L1_zero : Region12 ∩ {p | L1 p = 0} = segment ℝ V_point (sigma V_point) := by
  apply Set.eq_of_subset_of_subset;
  · intro p hp
    obtain ⟨hp12, hpL1⟩ := hp
    have hL1_zero : L1 p = 0 := hpL1
    have hL1_zero_segment : p ∈ segment ℝ V_point (sigma V_point) := by
      apply Region12_max_sum_implies_segment p hp12; exact (by
      unfold L1 at hL1_zero; linarith!;);
    exact hL1_zero_segment;
  · intro p hp;
    -- Since $p$ is in the segment between $V_point$ and $sigma V_point$, it is in $Region1$.
    have hp_region1 : p ∈ Region1 := by
      rw [Region1]
      exact (convex_convexHull ℝ {O_point, V_point, sigma V_point}).segment_subset
        (subset_convexHull ℝ {O_point, V_point, sigma V_point} (by simp))
        (subset_convexHull ℝ {O_point, V_point, sigma V_point} (by simp)) hp
    refine ⟨ Or.inl hp_region1, ?_ ⟩;
    obtain ⟨ a, b, ha, hb, hab, rfl ⟩ := hp;
    unfold L1; norm_num [ ← eq_sub_iff_add_eq' ] at *; ring_nf;
    unfold V_point sigma; norm_num; ring_nf;
    rw [ hab ] ; ring

/-
The intersection of Region3 and the line L1=0 is the singleton {sigma V}.
-/
lemma Region3_inter_L1_zero : Region3 ∩ {p | L1 p = 0} = {sigma V_point} := by
  apply Set.eq_singleton_iff_unique_mem.mpr;
  refine ⟨ ⟨ ?_, ?_ ⟩, ?_ ⟩;
  · exact subset_convexHull ℝ {O_point, sigma V_point, sigma X_point} (by simp);
  · -- Since sigma V_point is (V_point 1, V_point 0), we can substitute these values into L1.
    simp [L1, sigma];
    ring;
  · intro p hp;
    -- Since $p \in \text{Region3}$ and $L1(p) = 0$, we can use the fact that $L1$ is affine to show that $p$ must be $\sigma(V)$.
    have h_affine : ∃ a b c : ℝ, a + b + c = 1 ∧ a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ p = a • O_point + b • sigma V_point + c • sigma X_point := by
      have h_convex : p ∈ convexHull ℝ {O_point, sigma V_point, sigma X_point} := by
        exact hp.1;
      rw [ convexHull_insert ] at h_convex;
      · norm_num [ segment_eq_image ] at h_convex;
        obtain ⟨ i, hi, x, hx, rfl ⟩ := h_convex; exact ⟨ 1 - x, x * ( 1 - i ), x * i, by ring, by nlinarith, by nlinarith, by nlinarith, by ext; simpa using by ring ⟩ ;
      · exact ⟨ _, Set.mem_insert _ _ ⟩;
    obtain ⟨ a, b, c, h₁, h₂, h₃, h₄, rfl ⟩ := h_affine; simp_all +decide [ funext_iff, Fin.forall_fin_two ] ;
    -- Since $L1(O) < 0$, $L1(\sigma(X)) < 0$, and $L1(\sigma(V)) = 0$, the only way for $a * L1(O) + b * L1(\sigma(V)) + c * L1(\sigma(X)) = 0$ to hold is if $a = 0$ and $c = 0$.
    have h_ac_zero : a = 0 ∧ c = 0 := by
      have h_ac_zero : a * L1 O_point + c * L1 (sigma X_point) = 0 := by
        convert hp.2 using 1 ; norm_num [ L1 ] ; ring_nf;
        rw [ show b = 1 - a - c by linarith ] ; unfold sigma ; norm_num ; ring;
      constructor <;> nlinarith [ L1_O_neg, L1_sigma_X_neg ];
    aesop

/-
The intersection of Region123 and the line L1=0 is the segment V-sigma(V).
-/
lemma Region123_inter_L1_zero : Region123 ∩ {p | L1 p = 0} = segment ℝ V_point (sigma V_point) := by
  -- The intersection of Region12 with {L1=0} is the segment V-sigma V.
  have h_region12_inter_L1 : Region12 ∩ {p | L1 p = 0} = segment ℝ V_point (sigma V_point) := by
    -- Apply the lemma Region12_inter_L1_zero to conclude the proof.
    apply Region12_inter_L1_zero;
  -- The intersection of Region3 with {L1=0} is the singleton {sigma V}.
  have h_region3_inter_L1 : Region3 ∩ {p | L1 p = 0} = {sigma V_point} := by
    -- The intersection of Region3 and the line L1=0 is the singleton {sigma V} by definition.
    apply Region3_inter_L1_zero;
  -- The intersection of Region123 with {L1=0} is the union of the intersections of Region12 and Region3 with {L1=0}.
  have h_union_inter_L1 : (Region12 ∪ Region3) ∩ {p | L1 p = 0} = (Region12 ∩ {p | L1 p = 0}) ∪ (Region3 ∩ {p | L1 p = 0}) := by
    rw [ Set.union_inter_distrib_right ];
  rw [Region123, h_union_inter_L1, h_region12_inter_L1, h_region3_inter_L1]
  ext x
  simp +decide [segment_eq_image]
  ring_nf
  aesop;

/-
The origin cannot be in a unit segment contained in the first quadrant.
-/
lemma O_not_in_unit_segment_FirstQuadrant (L : Set Point) (hL : IsUnitSegment L) (hL_sub : L ⊆ FirstQuadrant) : O_point ∉ L := by
  -- Apply the lemma that states if the origin is in a unit segment in the first quadrant, then the endpoints must be the origin.
  have h_endpoints : ∀ a b : Point, a ∈ FirstQuadrant → b ∈ FirstQuadrant → O_point ∈ openSegment ℝ a b → a = O_point ∧ b = O_point := by
    intros a b ha hb hO
    apply origin_in_openSegment_FirstQuadrant_implies_endpoints_zero a b ha hb hO;
  obtain ⟨a, b, hab⟩ : ∃ a b : Point, L = openSegment ℝ a b ∧ dist a b = 1 := by
    cases hL ; tauto;
  contrapose! h_endpoints;
  use a, b;
  have h_closure : closure L ⊆ FirstQuadrant := by
    have hFirstQuadrant_closed : IsClosed FirstQuadrant := by
      have h0 : IsClosed ((fun p : Point => p 0) ⁻¹' Set.Ici (0 : ℝ)) := by
        simpa using isClosed_Ici.preimage
          ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).continuous)
      have h1 : IsClosed ((fun p : Point => p 1) ⁻¹' Set.Ici (0 : ℝ)) := by
        simpa using isClosed_Ici.preimage
          ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).continuous)
      simpa [FirstQuadrant, Set.preimage, Set.mem_setOf_eq, Set.inter_def] using h0.inter h1
    exact closure_minimal hL_sub hFirstQuadrant_closed
  simp_all +decide [ Set.subset_def ];
  exact ⟨ h_closure a ( left_mem_segment _ _ _ ), h_closure b ( right_mem_segment _ _ _ ), by rintro rfl rfl; norm_num [ dist_eq_norm ] at hab ⟩

/-
L1 preserves affine combinations.
-/
lemma L1_convex_comb (x y : Point) (a b : ℝ) (h : a + b = 1) : L1 (a • x + b • y) = a * L1 x + b * L1 y := by
  -- Expand L1 (a • x + b • y) using the definition of L1.
  simp [L1];
  grind

/-
The intersection of Region12 and Region3 is covered by S_finite or satisfies the blocking condition.
-/
lemma Region12_inter_Region3_cover : ∀ x ∈ Region12 ∩ Region3, (∃ s ∈ S_finite, x ∈ s) ∨ (∀ L, IsUnitSegment L → L ⊆ Region12 ∪ Region3 → x ∈ L → L ⊆ Region12 ∨ L ⊆ Region3) := by
  intro x hx
  have h_cases : x ∈ segment ℝ O_point (sigma V_point) := by
    exact Region12_inter_Region3_subset_segment hx;
  by_cases hx_sigma_V : x = sigma V_point;
  · exact Or.inl ⟨ segment5, by unfold S_finite; tauto, hx_sigma_V ▸ sigma_V_on_segment5 ⟩;
  · by_cases hx_O : x = O_point;
    · right;
      intro L hL hL_sub hxL
      have hL_first_quadrant : L ⊆ FirstQuadrant := by
        exact fun p hp => Region123_subset_FirstQuadrant <| hL_sub hp;
      exact False.elim <| O_not_in_unit_segment_FirstQuadrant L hL hL_first_quadrant <| hx_O ▸ hxL;
    · -- Since x is in the open segment between O and sigma V, and x is not O or sigma V, it must be in segment2.
      have hx_segment2 : x ∈ openSegment ℝ O_point (sigma V_point) := by
        exact
          mem_openSegment_of_ne_left_right (fun a ↦ hx_O (id (Eq.symm a)))
            (fun a ↦ hx_sigma_V (id (Eq.symm a))) h_cases;
      exact Or.inl ⟨ segment2, by unfold S_finite; tauto, hx_segment2 ⟩

/-
Region123 is blocked by S_finite.
-/
def Region1234 : Set Point := Region123 ∪ Region4

def Region12345 : Set Point := Region1234 ∪ Region5

lemma Region123_blocking : IsBlocking S_finite Region123 := by
  have hR12 : IsClosed Region12 := by
    simpa [Region12] using
      (Region12_eq_convexHull.symm ▸
        (Set.toFinite ({O_point, V_point, sigma V_point, X_point} : Set Point)).isClosed_convexHull ℝ)
  have hR3 : IsClosed Region3 := by
    simpa [Region3] using
      (Set.toFinite ({O_point, sigma V_point, sigma X_point} : Set Point)).isClosed_convexHull ℝ
  change IsBlocking S_finite (Region12 ∪ Region3)
  exact blocking_union_lemma hR12 hR3 Region12_blocking_thm Region3_blocking
    Region12_inter_Region3_cover

/-
If S blocks R1 and R2, and the intersection of R1 and R2 within U is covered by S, then S blocks the union of R1 and R2 within U.
-/
lemma blocking_union_restricted {S : Set (Set Point)} {R1 R2 U : Set Point}
    (h_closed1 : IsClosed R1) (h_closed2 : IsClosed R2)
    (h_open : IsOpen U)
    (h_block1 : IsBlocking S R1)
    (h_block2 : IsBlocking S R2)
    (h_cover : ∀ x ∈ R1 ∩ R2 ∩ U, ∃ s ∈ S, x ∈ s) :
    ∀ L, IsUnitSegment L → L ⊆ U → L ⊆ R1 ∪ R2 → ∃ s ∈ S, ¬Disjoint s L := by
      intro L hL hL' hL'';
      by_cases hL1 : L ⊆ R1 <;> by_cases hL2 : L ⊆ R2;
      · exact Exists.imp ( by simp +contextual [ Set.disjoint_left ] ) ( h_block1 L hL hL1 );
      · exact h_block1 L hL hL1;
      · exact h_block2 L hL hL2;
      · -- Since L is not contained in R1 and not contained in R2, it must intersect both R1 \ R2 and R2 \ R1.
        obtain ⟨x1, hx1⟩ : ∃ x1 ∈ L, x1 ∈ R1 \ R2 := by
          rcases not_subset.mp hL2 with ⟨x1, hx1L, hx1R2⟩
          have hx1R1 : x1 ∈ R1 := by
            cases hL'' hx1L with
            | inl hx => exact hx
            | inr hx => exact False.elim (hx1R2 hx)
          exact ⟨x1, hx1L, hx1R1, hx1R2⟩
        obtain ⟨x2, hx2⟩ : ∃ x2 ∈ L, x2 ∈ R2 \ R1 := by
          rcases not_subset.mp hL1 with ⟨x2, hx2L, hx2R1⟩
          have hx2R2 : x2 ∈ R2 := by
            cases hL'' hx2L with
            | inl hx => exact False.elim (hx2R1 hx)
            | inr hx => exact hx
          exact ⟨x2, hx2L, hx2R2, hx2R1⟩
        -- Since L is connected and R1, R2 are closed, L must intersect R1 ∩ R2.
        obtain ⟨x, hx⟩ : ∃ x ∈ L, x ∈ R1 ∩ R2 := by
          have h_connected : IsConnected L := by
            rcases hL with ⟨ A, B, hAB, rfl ⟩;
            rw [ openSegment_eq_image ];
            exact ⟨ Set.Nonempty.image _ ⟨ 1 / 2, by norm_num ⟩, isPreconnected_Ioo.image _ <| Continuous.continuousOn <| by continuity ⟩;
          have h_inter : IsPreconnected L := by
            exact h_connected.isPreconnected;
          contrapose! h_inter;
          norm_num [ IsPreconnected ];
          refine ⟨ Set.univ \ R2, isOpen_univ.sdiff h_closed2, Set.univ \ R1, isOpen_univ.sdiff h_closed1, ?_, ?_, ?_, ?_ ⟩
          · intro y hyL
            by_cases hyR2 : y ∈ R2
            · right
              exact ⟨trivial, fun hyR1 => h_inter y hyL ⟨hyR1, hyR2⟩⟩
            · exact Or.inl ⟨trivial, hyR2⟩
          · refine ⟨x1, ?_⟩
            exact ⟨hx1.1, trivial, hx1.2.2⟩
          · refine ⟨x2, ?_⟩
            exact ⟨hx2.1, trivial, hx2.2.2⟩
          · rintro ⟨y, hy⟩
            rcases hy with ⟨hyL, hyU, hyV⟩
            exact (hL'' hyL).elim hyV.2 hyU.2
        exact Exists.elim ( h_cover x ⟨ hx.2, hL' hx.1 ⟩ ) fun s hs => ⟨ s, hs.1, Set.not_disjoint_iff_nonempty_inter.mpr ⟨ x, hs.2, hx.1 ⟩ ⟩

/-
Region123 is a closed set.
-/
lemma Region123_isClosed : IsClosed Region123 := by
  unfold Region123 Region12 Region1 Region2 Region3
  exact IsClosed.union
    (IsClosed.union
      ((Set.toFinite ({O_point, V_point, sigma V_point} : Set Point)).isClosed_convexHull ℝ)
      ((Set.toFinite ({O_point, V_point, X_point} : Set Point)).isClosed_convexHull ℝ))
    ((Set.toFinite ({O_point, sigma V_point, sigma X_point} : Set Point)).isClosed_convexHull ℝ)

/-
Region4 is closed.
-/
lemma Region4_isClosed : IsClosed Region4 := by
  simpa [Region4] using
    (Set.toFinite ({X_point, A_0, Y_point} : Set Point)).isClosed_convexHull ℝ

/-
Region5 is closed.
-/
lemma Region5_isClosed : IsClosed Region5 := by
  simpa [Region5] using
    (Set.toFinite ({sigma X_point, sigma A_0, sigma Y_point} : Set Point)).isClosed_convexHull ℝ

/-
Region6_Total is closed.
-/
lemma Region6_Total_isClosed : IsClosed Region6_Total := by
  apply Set.Finite.isClosed_convexHull;
  exact Set.toFinite _

/-
Region_Square is an open set.
-/
lemma Region_Square_isOpen : IsOpen Region_Square := by
  have h0 : IsOpen ((fun p : Point => p 0) ⁻¹' Set.Ioo (0 : ℝ) 1) :=
    (isOpen_Ioo (a := (0 : ℝ)) (b := 1)).preimage
      (show Continuous (fun p : Point => p 0) from
        PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 0)
  have h1 : IsOpen ((fun p : Point => p 1) ⁻¹' Set.Ioo (0 : ℝ) 1) :=
    (isOpen_Ioo (a := (0 : ℝ)) (b := 1)).preimage
      (show Continuous (fun p : Point => p 1) from
        PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 1)
  have h : IsOpen (((fun p : Point => p 0) ⁻¹' Set.Ioo (0 : ℝ) 1) ∩
      ((fun p : Point => p 1) ⁻¹' Set.Ioo (0 : ℝ) 1)) := h0.inter h1
  have hset : Region_Square =
      (((fun p : Point => p 0) ⁻¹' Set.Ioo (0 : ℝ) 1) ∩
        ((fun p : Point => p 1) ⁻¹' Set.Ioo (0 : ℝ) 1)) := by
    ext p
    simp [Region_Square, Set.mem_Ioo, and_assoc]
  rw [hset]
  exact h

/-
L2 is non-positive at sigma X.
-/
lemma L2_sigma_X_le_0 : L2 (sigma X_point) ≤ 0 := by
  unfold L2 sigma X_point ; norm_num [ y1_bounds ];
  -- Since $x1 > 0$, we can divide both sides of the inequality by $x1$.
  have h_div : -(y1) ≤ 1 - x1 := by
    linarith [ y1_bounds, show x1 < 1 by
                            exact x1_prop.2.1.trans_le ( by norm_num ) ];
  nlinarith [ show 0 < x1 from by exact ( show 0 < x1 from by exact ( by obtain ⟨ hx_pos, hx_lt_one, hx_poly ⟩ := x1_prop; linarith ) ) ]

/-
L2 is an affine function.
-/
lemma L2_affine : ∀ (x y : Point) (a b : ℝ), a + b = 1 → L2 (a • x + b • y) = a * L2 x + b * L2 y := by
  unfold L2
  intro x y a b hab
  simp [hab]
  ring_nf
  skip;
  rw [ ← eq_sub_iff_add_eq' ] at hab ; subst_vars ; ring

/-
If L2 is non-positive on a set s, it is non-positive on the convex hull of s.
-/
lemma L2_convex_hull_le_0 (s : Set Point) (hs : ∀ p ∈ s, L2 p ≤ 0) : ∀ p ∈ convexHull ℝ s, L2 p ≤ 0 := by
  have h_convex : Convex ℝ {p : Point | L2 p ≤ 0} := by
    intro p hp q hq a b ha hb hab
    rw [Set.mem_setOf_eq] at hp hq ⊢
    rw [L2_affine p q a b hab]
    nlinarith
  exact fun p hp => h_convex.convexHull_subset_iff.mpr hs hp

/-
L2 is non-positive on Region1.
-/
lemma Region1_sub_L2_le_0 : ∀ p ∈ Region1, L2 p ≤ 0 := by
  apply L2_convex_hull_le_0;
  -- By definition of $L2$, we know that $L2(O_point) < 0$, $L2(V_point) = 0$, and $L2(sigma V_point) \leq 0$.
  simp [L2_O_neg, L2_V, L2_sigma_V_le_0];
  exact le_of_lt ( L2_O_neg )

/-
L2 is non-positive on Region3.
-/
lemma Region3_sub_L2_le_0 : ∀ p ∈ Region3, L2 p ≤ 0 := by
  apply L2_convex_hull_le_0;
  rintro p ( rfl | rfl | rfl ) <;> [ exact le_of_lt L2_O_neg; exact L2_sigma_V_le_0; exact L2_sigma_X_le_0 ]

/-
L2 is non-positive on Region123.
-/
lemma Region123_sub_L2_le_0 : ∀ p ∈ Region123, L2 p ≤ 0 := by
  -- By definition of Region123, we know that every point in Region123 is in either Region1, Region2, or Region3.
  intros p hp
  cases' hp with hp1 hp2 hp3
  all_goals generalize_proofs at *;
  · cases' hp1 with hp1 hp2 hp3
    all_goals generalize_proofs at *;
    · exact Region1_sub_L2_le_0 p hp1;
    · exact Region2_sub_L2_le_0 p hp2;
  · exact Region3_sub_L2_le_0 p hp2

/-
The intersection of Region2 and the line L2=0 is the segment VX.
-/
lemma Region2_inter_L2_zero : Region2 ∩ {p | L2 p = 0} = segment ℝ V_point X_point := by
  unfold Region2;
  -- Let's choose any point $p$ in the convex hull of $\{O, V, X\}$ and show that it lies on the segment $VX$ if and only if $L2(p) = 0$.
  ext p
  apply Iff.intro;
  · intro hp
    obtain ⟨a, b, c, ha, hb, hc, habc, hp_eq⟩ : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • O_point + b • V_point + c • X_point := by
      norm_num [ convexHull_insert ] at hp;
      rcases hp.1 with ⟨ q, ⟨ a, b, ha, hb, hab, rfl ⟩, ⟨ c, d, hc, hd, hcd, rfl ⟩ ⟩ ; exact ⟨ c, a * d, b * d, hc, mul_nonneg ha hd, mul_nonneg hb hd, by nlinarith, by ext i; fin_cases i <;> simpa using by ring ⟩ ;
    -- Since $L2 p = 0$, we have $a * L2 O + b * L2 V + c * L2 X = 0$.
    have hL2_zero : a * L2 O_point + b * L2 V_point + c * L2 X_point = 0 := by
      have hL2_zero : L2 p = a * L2 O_point + b * L2 V_point + c * L2 X_point := by
        unfold L2; norm_num [ hp_eq ] ; ring_nf;
        rw [ ← eq_sub_iff_add_eq' ] at habc ; subst habc ; ring;
      exact hL2_zero ▸ hp.2;
    -- Since $L2 O < 0$, we must have $a = 0$.
    have ha_zero : a = 0 := by
      nlinarith [ L2_O_neg, L2_V, L2_X ];
    simp_all +decide [ segment_eq_image ];
    exact ⟨ c, ⟨ hc, by linarith ⟩, by rw [ ← eq_sub_iff_add_eq' ] at habc; subst habc; ring_nf ⟩;
  · rintro ⟨ a, b, ha, hb, hab, rfl ⟩;
    -- Since $a + b = 1$, the point $a • V_point + b • X_point$ is a convex combination of $V_point$ and $X_point$, which are both in the set $\{O_point, V_point, X_point\}$. Therefore, it is in the convex hull.
    have h_convex : a • V_point + b • X_point ∈ convexHull ℝ {O_point, V_point, X_point} := by
      rw [ convexHull_eq ];
      refine ⟨ Fin 2, { 0, 1 }, fun i => if i = 0 then a else b, fun i => if i = 0 then V_point else X_point, ?_, ?_, ?_, ?_ ⟩ <;> simp +decide [ *, Finset.centerMass ];
    refine ⟨ h_convex, ?_ ⟩;
    convert L2_affine V_point X_point a b hab using 1 ; norm_num [ L2_V, L2_X ]

/-
The intersection of Region1 and the line L2=0 is the singleton {V}.
-/
lemma Region1_inter_L2_zero : Region1 ∩ {p | L2 p = 0} = {V_point} := by
  ext p;
  constructor;
  · intro hp
    obtain ⟨a, b, c, ha, hb, hc, habc, hp_eq⟩ : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • O_point + b • V_point + c • sigma V_point := by
      have h_convex_comb : p ∈ convexHull ℝ {O_point, V_point, sigma V_point} := by
        exact hp.1;
      rw [ convexHull_insert ] at h_convex_comb;
      · norm_num [ segment_eq_image ] at h_convex_comb;
        obtain ⟨ i, hi, x, hx, rfl ⟩ := h_convex_comb; exact ⟨ 1 - x, x * ( 1 - i ), x * i, by linarith, by nlinarith, by nlinarith, by linarith, by ext ; simpa using by ring ⟩ ;
      · norm_num +zetaDelta at *;
    -- Since $L2 O < 0$ and $L2 sigma V < 0$, and $a, c \geq 0$, we have $a * L2 O + c * L2 sigma V = 0$ implies $a = 0$ and $c = 0$.
    have h_a_c_zero : a * L2 O_point + c * L2 (sigma V_point) = 0 → a = 0 ∧ c = 0 := by
      have h_a_c_zero : L2 O_point < 0 ∧ L2 (sigma V_point) < 0 := by
        exact ⟨ L2_O_neg, L2_sigma_V_neg ⟩;
      exact fun h => ⟨ by nlinarith, by nlinarith ⟩;
    have hL2_p : L2 p = a * L2 O_point + b * L2 V_point + c * L2 (sigma V_point) := by
      unfold L2; simp +decide [ hp_eq ] ; ring_nf;
      rw [ ← eq_sub_iff_add_eq' ] at habc ; subst habc ; ring;
    specialize h_a_c_zero ( by nlinarith [ hp.2.symm, show L2 V_point = 0 from L2_V ] ) ; aesop;
  · rintro rfl;
    exact ⟨ subset_convexHull ℝ _ <| Set.mem_insert_of_mem _ <| Set.mem_insert _ _, L2_V ⟩

/-
L2 is strictly negative at sigma X.
-/
lemma L2_sigma_X_neg : L2 (sigma X_point) < 0 := by
  unfold L2 sigma X_point; norm_num; nlinarith [ x1_prop.1, x1_prop.2.1, y1_bounds ] ;

/-
The intersection of Region3 and the line L2=0 is empty.
-/
lemma Region3_inter_L2_zero : Region3 ∩ {p | L2 p = 0} = ∅ := by
  -- By definition of $L2$, we know that $L2$ is strictly negative at $O$, $sigma V$, and $sigma X$.
  have hL2_neg : ∀ p ∈ ({O_point, sigma V_point, sigma X_point} : Set Point), L2 p < 0 := by
    exact fun p hp => by rcases hp with ( rfl | rfl | rfl ) <;> [ exact L2_O_neg; exact L2_sigma_V_neg; exact L2_sigma_X_neg ] ;
  -- By definition of $L2$, we know that $L2$ is strictly affine and negative at $O$, $sigma V$, and $sigma X$.
  have hL2_strict_neg : ∀ p ∈ convexHull ℝ {O_point, sigma V_point, sigma X_point}, L2 p < 0 := by
    intro p hp
    have h_convex_comb : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • O_point + b • sigma V_point + c • sigma X_point := by
      rw [ convexHull_insert ] at hp;
      · norm_num [ segment_eq_image ] at hp;
        rcases hp with ⟨ i, hi, x, hx, rfl ⟩ ; exact ⟨ 1 - x, x * ( 1 - i ), x * i, by linarith, by nlinarith, by nlinarith, by linarith, by ext ; simpa using by ring ⟩ ;
      · exact ⟨ _, Set.mem_insert _ _ ⟩;
    obtain ⟨ a, b, c, ha, hb, hc, habc, rfl ⟩ := h_convex_comb;
    have hL2_strict_neg : L2 (a • O_point + b • sigma V_point + c • sigma X_point) = a * L2 O_point + b * L2 (sigma V_point) + c * L2 (sigma X_point) := by
      unfold L2; norm_num; ring_nf;
      rw [ ← eq_sub_iff_add_eq' ] at habc ; subst habc ; ring;
    cases lt_or_eq_of_le ha <;> cases lt_or_eq_of_le hb <;> cases lt_or_eq_of_le hc <;> first | nlinarith [ hL2_neg O_point ( by norm_num ), hL2_neg ( sigma V_point ) ( by norm_num ), hL2_neg ( sigma X_point ) ( by norm_num ) ] | skip;
  exact Set.eq_empty_of_forall_notMem fun p hp => hp.2.not_lt <| hL2_strict_neg p hp.1

/-
The intersection of Region123 and the line L2=0 is the segment VX.
-/
lemma Region123_inter_L2_zero : Region123 ∩ {p | L2 p = 0} = segment ℝ V_point X_point := by
  -- The intersection of Region123 and the line L2=0 is the union of the intersections of each region with the line.
  have h_union_intersections : Region123 ∩ {p | L2 p = 0} = (Region1 ∩ {p | L2 p = 0}) ∪ (Region2 ∩ {p | L2 p = 0}) ∪ (Region3 ∩ {p | L2 p = 0}) := by
    unfold Region123 Region12; ext; aesop;
  rw [ h_union_intersections, Region1_inter_L2_zero, Region2_inter_L2_zero, Region3_inter_L2_zero ] ; norm_num [ segment_eq_image ];
  exact ⟨ 0, by norm_num ⟩

/-
The intersection of Region123 and Region4 is contained in the segment XV.
-/
lemma Region123_inter_Region4_subset_segment_XV : Region123 ∩ Region4 ⊆ segment ℝ X_point V_point := by
  -- If $p$ is in both $Region123$ and $Region4$, then $p$ is in the segment $VX$ because $L2 p = 0$.
  intro p hp
  have hL2_zero : L2 p = 0 := by
    exact le_antisymm ( Region123_sub_L2_le_0 p hp.1 ) ( Region4_sub_L2_ge_0 p hp.2 ) ▸ rfl;
  have h_segment_VX : p ∈ segment ℝ V_point X_point := by
    exact Region123_inter_L2_zero.subset ⟨ hp.1, hL2_zero ⟩;
  rw [ segment_symm ] at h_segment_VX ; tauto

/-
Region4 is blocked by S_finite.
-/
lemma Region4_blocking_thm : IsBlocking S_finite Region4 := by
  -- By definition of $Region4$, any unit segment in $Region4$ must be one of the open sides of the triangle $XAY$.
  intro L hL hL_sub
  have h_segment : L = openSegment ℝ X_point A_0 ∨ L = openSegment ℝ A_0 Y_point ∨ L = openSegment ℝ Y_point X_point := by
    apply_rules [ triangle_diameter_lemma ];
    · exact le_of_lt dist_X_A0_lt_1;
    · exact le_of_lt ( dist_A0_Y_lt_1 );
    · rw [ dist_comm ] ; exact dist_X_Y.le;
  rcases h_segment with ( rfl | rfl | rfl ) <;> simp_all +decide [ Set.disjoint_left ];
  · contrapose! hL;
    convert not_isUnitSegment_of_dist_lt_1 _ using 1_1;
    convert dist_X_A0_lt_1 using 1;
  · exact absurd hL ( not_isUnitSegment_of_dist_lt_1 dist_A0_Y_lt_1 );
  · use segment4;
    simp [S_finite, segment4];
    exists ( 1 / 2 : ℝ ) • X_point + ( 1 / 2 : ℝ ) • Y_point;
    constructor <;> norm_num [ openSegment_eq_image ];
    · exact ⟨ 1 / 2, by norm_num ⟩;
    · exact ⟨ 1 / 2, by norm_num, by ext i; fin_cases i <;> norm_num [ Y_point, X_point ] ; ring ⟩

/-
The intersection of segment XV and Region_Square is covered by S_finite.
-/
lemma segment_XV_covered_by_S_finite : ∀ x ∈ segment ℝ X_point V_point, x ∈ Region_Square → ∃ s ∈ S_finite, x ∈ s := by
  intro x hx hx'
  by_cases hxV : x = V_point;
  · exact ⟨ segment4, by simp +decide [ S_finite ], hxV.symm ▸ V_on_segment4 ⟩;
  · -- Since $x$ is in $(X, V)$, we have $x \in \text{openSegment} \, \mathbb{R} \, X \, V$.
    have hx_openSegment : x ∈ openSegment ℝ X_point V_point := by
      rw [ segment_eq_image ] at hx;
      rcases hx with ⟨ θ, ⟨ hθ₀, hθ₁ ⟩, rfl ⟩ ; cases lt_or_eq_of_le hθ₀ <;> cases lt_or_eq_of_le hθ₁ <;> simp_all +decide [ openSegment_eq_image ] ;
      · exact ⟨ θ, ⟨ by linarith, by linarith ⟩, rfl ⟩;
      · subst_vars; exact absurd hx' ( by unfold Region_Square; norm_num [ X_point, V_point ] ) ;
    -- Since $V$ is in $\text{openSegment} \, \mathbb{R} \, X \, Y$, we have $x \in \text{openSegment} \, \mathbb{R} \, X \, Y$.
    have hx_openSegment_Y : x ∈ openSegment ℝ X_point Y_point := by
      -- Since $V$ is in $(X, Y)$, we have $V \in \text{openSegment} \, \mathbb{R} \, X_point \, Y_point$.
      have hV_openSegment : V_point ∈ openSegment ℝ X_point Y_point := by
        simpa [segment4] using V_on_segment4
      obtain ⟨ a, b, ha, hb, hab, rfl ⟩ := hx_openSegment;
      obtain ⟨ c, d, hc, hd, hcd, h ⟩ := hV_openSegment;
      refine ⟨ a + b * c, b * d, ?_, ?_, ?_, ?_ ⟩ <;> try nlinarith;
      rw [ ← h ] ; ext i ; norm_num ; ring;
    exact ⟨ _, Set.mem_insert_of_mem _ ( Set.mem_insert_of_mem _ ( Set.mem_insert_of_mem _ ( Set.mem_insert _ _ ) ) ), hx_openSegment_Y ⟩

/-
Region1234 is blocked by S_finite in Region_Square.
-/
lemma Region1234_blocking_in_Square : ∀ L, IsUnitSegment L → L ⊆ Region_Square → L ⊆ Region123 ∪ Region4 → ∃ s ∈ S_finite, ¬Disjoint s L := by
  apply blocking_union_restricted;
  · exact Region123_isClosed
  · exact Region4_isClosed
  · exact Region_Square_isOpen
  · exact Region123_blocking
  · exact Region4_blocking_thm
  · intros x hx
    obtain ⟨hx1, hx2⟩ := hx;
    have := segment_XV_covered_by_S_finite x (Region123_inter_Region4_subset_segment_XV hx1) hx2;
    exact this

/-
Region123 ∪ Region4 is blocked by S_finite in Region_Square.
-/
lemma Region1234_blocking_in_Square_v2 : ∀ L, IsUnitSegment L → L ⊆ Region_Square → L ⊆ Region123 ∪ Region4 → ∃ s ∈ S_finite, ¬Disjoint s L := by
  intros L hL hL_sub hL_union
  apply Region1234_blocking_in_Square L hL hL_sub hL_union
  skip

/-
L3 is negative at X.
-/
lemma L3_X_neg : L3 X_point < 0 := by
  exact show y1 * ( 0 - x1 ) - x1 * ( 1 - x1 ) < 0 from by nlinarith [ x1_prop.1, x1_prop.2.1, y1_bounds.1, y1_bounds.2 ] ;

/-
If L3 is non-positive on a set s, it is non-positive on the convex hull of s.
-/
lemma L3_convex_hull_le_0 (s : Set Point) (hs : ∀ p ∈ s, L3 p ≤ 0) : ∀ p ∈ convexHull ℝ s, L3 p ≤ 0 := by
  rw [ convexHull_eq ];
  simp +contextual [ L3, Set.mem_setOf_eq ];
  intro p x s w hw hs' f hf hp; rw [ ← hp ] ; simp +decide [ *, Finset.centerMass ] ;
  have := Finset.sum_le_sum fun i ( hi : i ∈ s ) => mul_le_mul_of_nonneg_left ( hs ( f i ) ( hf i hi ) ) ( hw i hi ) ; simp_all +decide [ mul_sub, sub_mul, mul_comm, Finset.mul_sum _ _ _, Finset.sum_mul ] ;
  simp_all +decide [ L3, Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, sub_mul, mul_sub, mul_assoc, mul_comm, mul_left_comm ];
  simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ]

/-
L3 is negative at A0.
-/
lemma L3_A0_neg : L3 A_0 < 0 := by
  unfold L3 A_0; norm_num [ x1_prop ] ; ring_nf ;
  nlinarith [ y1_bounds.1, y1_bounds.2, x1_prop.1, x1_prop.2.1 ]

/-
L3 is non-positive on Region1.
-/
lemma Region1_sub_L3_le_0 : ∀ p ∈ Region1, L3 p ≤ 0 := by
  apply L3_convex_hull_le_0;
  simp +zetaDelta at *;
  exact ⟨ by linarith [ L3_O_neg ], by linarith [ L3_V_neg ], by linarith [ L3_sigma_V ] ⟩

/-
L3 is non-positive on Region2.
-/
lemma Region2_sub_L3_le_0 : ∀ p ∈ Region2, L3 p ≤ 0 := by
  exact fun p hp => L3_convex_hull_le_0 { O_point, V_point, X_point } ( by rintro p ( rfl | rfl | rfl ) <;> [ exact L3_O_neg.le; exact L3_V_neg.le; exact L3_X_neg.le ] ) p hp

/-
L3 is non-positive on Region123.
-/
lemma Region123_sub_L3_le_0 : ∀ p ∈ Region123, L3 p ≤ 0 := by
  exact fun p hp => by rcases hp with ( hp | hp ) <;> [ exact ( by rcases hp with ( hp | hp ) <;> [ exact Region1_sub_L3_le_0 p hp; exact Region2_sub_L3_le_0 p hp ] ) ; exact Region3_sub_L3_le_0 p hp ] ;

/-
L3 is non-positive on Region4.
-/
lemma Region4_sub_L3_le_0 : ∀ p ∈ Region4, L3 p ≤ 0 := by
  apply L3_convex_hull_le_0;
  norm_num [ L3_X_neg, L3_A0_neg, L3_Y_neg ];
  exact ⟨ le_of_lt ( L3_X_neg ), le_of_lt ( L3_A0_neg ), le_of_lt ( L3_Y_neg ) ⟩

/-
L3 is non-positive on Region1234.
-/
lemma Region1234_sub_L3_le_0 : ∀ p ∈ Region1234, L3 p ≤ 0 := by
  exact fun p hp => by rcases hp with ( hp | hp ) <;> [ exact Region123_sub_L3_le_0 p hp; exact Region4_sub_L3_le_0 p hp ] ;

/-
The intersection of Region5 and the line L3=0 is the segment [sigma X, sigma Y].
-/
lemma Region5_inter_L3_zero : Region5 ∩ {p | L3 p = 0} = segment ℝ (sigma X_point) (sigma Y_point) := by
  apply Set.ext
  intro p
  simp [Region5, segment];
  constructor;
  · intro hp
    obtain ⟨hp_convex, hp_L3⟩ := hp
    have hp_comb : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • sigma X_point + b • sigma A_0 + c • sigma Y_point := by
      rw [ convexHull_insert ] at hp_convex;
      · norm_num [ segment_eq_image ] at hp_convex;
        rcases hp_convex with ⟨ i, hi, x, hx, rfl ⟩ ; exact ⟨ 1 - x, x * ( 1 - i ), x * i, by linarith, by nlinarith, by nlinarith, by linarith, by ext ; simpa using by ring ⟩ ;
      · exact ⟨ _, Set.mem_insert _ _ ⟩;
    obtain ⟨ a, b, c, ha, hb, hc, habc, rfl ⟩ := hp_comb;
    -- Since $L3(sigma A_0) > 0$, we have $b = 0$.
    have hb_zero : b = 0 := by
      have hb_zero : b * L3 (sigma A_0) = 0 := by
        have hb_zero : L3 (a • sigma X_point + b • sigma A_0 + c • sigma Y_point) = a * L3 (sigma X_point) + b * L3 (sigma A_0) + c * L3 (sigma Y_point) := by
          unfold L3; norm_num; ring_nf;
          rw [ ← eq_sub_iff_add_eq' ] at habc ; subst habc ; ring;
        rw [ show L3 ( sigma X_point ) = 0 by exact L3_sigma_X ] at hb_zero ; rw [ show L3 ( sigma Y_point ) = 0 by exact L3_sigma_Y ] at hb_zero ; linarith;
      exact Or.resolve_right ( mul_eq_zero.mp hb_zero ) ( ne_of_gt ( L3_sigma_A0_pos ) );
    exact ⟨ a, ha, c, hc, by linarith, by simpa [ hb_zero ] ⟩;
  · rintro ⟨ a, ha, b, hb, hab, rfl ⟩;
    refine ⟨ ?_, ?_ ⟩;
    · rw [ convexHull_eq ];
      refine ⟨ Fin 2, { 0, 1 }, fun i => if i = 0 then a else b, fun i => if i = 0 then sigma X_point else sigma Y_point, ?_, ?_, ?_, ?_ ⟩ <;> simp +decide [ *, Finset.centerMass ];
    · unfold L3; norm_num [ show a = 1 - b by linarith ] ; ring_nf;
      unfold sigma; norm_num [ X_point, Y_point ] ; ring;

/-
L2 is negative at sigma Y.
-/
lemma L2_sigma_Y_neg : L2 (sigma Y_point) < 0 := by
  unfold L2 sigma Y_point; norm_num;
  have hy1_bounds : 0 < y1 ∧ y1 < 1 := by
    exact ⟨ by have := y1_bounds; norm_num at this; linarith, by have := y1_bounds; norm_num at this; linarith ⟩
  have hx1_bounds : 0.95 < x1 ∧ x1 < 0.96 := by
    exact ⟨ by linear_combination x1_prop.1, by linear_combination x1_prop.2.1 ⟩
  norm_num at *;
  nlinarith

/-
The intersection of Region1234 and Region5 is contained in the segment [sigma X, sigma Y].
-/
lemma Region1234_inter_Region5_subset_segment_sigmaX_sigmaY : Region1234 ∩ Region5 ⊆ segment ℝ (sigma X_point) (sigma Y_point) := by
  intro p hp
  obtain ⟨hp1234, hp5⟩ := hp
  have hL3_zero : L3 p = 0 := by
    exact le_antisymm ( Region1234_sub_L3_le_0 p hp1234 ) ( Region5_sub_L3_ge_0 p hp5 ) |> Eq.trans <| by norm_num;
  exact (by
  exact Region5_inter_L3_zero.subset ⟨ hp5, hL3_zero ⟩)

/-
Region1234 is closed.
-/
lemma Region1234_isClosed : IsClosed Region1234 := by
  simpa [Region1234] using IsClosed.union ( Region123_isClosed ) ( Region4_isClosed )

/-
Region12345 is blocked by S_finite in Region_Square.
-/
lemma Region12345_blocking_in_Square : ∀ L, IsUnitSegment L → L ⊆ Region_Square → L ⊆ Region12345 → ∃ s ∈ S_finite, ¬Disjoint s L := by
  have h_union : ∀ L, IsUnitSegment L → L ⊆ Region_Square → L ⊆ Region1234 ∪ Region5 → ∃ s ∈ S_finite, ¬Disjoint s L := by
    intros L hL hL_sub hL_union
    by_cases hL_subset_Region1234 : L ⊆ Region1234
    · exact Region1234_blocking_in_Square_v2 L hL hL_sub hL_subset_Region1234
    · by_cases hL_subset_Region5 : L ⊆ Region5;
      · exact Region5_blocking L hL hL_subset_Region5 |> fun ⟨ s, hs₁, hs₂ ⟩ => ⟨ s, hs₁, hs₂ ⟩;
      · -- Let x be a point in L that is not in Region1234.
        obtain ⟨x, hxL, hx_not_in_Region1234⟩ : ∃ x ∈ L, x ∉ Region1234 := by
          exact Set.not_subset.mp hL_subset_Region1234 |> Exists.imp fun x hx => by tauto;
        -- Let y be a point in L that is not in Region5.
        obtain ⟨y, hyL, hy_not_in_Region5⟩ : ∃ y ∈ L, y ∉ Region5 := by
          exact Set.not_subset.mp hL_subset_Region5;
        -- Since L is a unit segment, it is connected. Therefore, there must be a point z in L that is in both Region1234 and Region5.
        obtain ⟨z, hzL, hz_both⟩ : ∃ z ∈ L, z ∈ Region1234 ∧ z ∈ Region5 := by
          have h_connected : IsConnected L := by
            obtain ⟨ A, B, hAB, rfl ⟩ := hL;
            rw [ openSegment_eq_image ];
            exact ⟨ Set.Nonempty.image _ ⟨ 1 / 2, by norm_num ⟩, isPreconnected_Ioo.image _ <| Continuous.continuousOn <| by continuity ⟩;
          have h_connected : IsPreconnected L := by
            exact h_connected.isPreconnected;
          contrapose! h_connected;
          norm_num [ IsPreconnected ];
          refine ⟨ Region1234ᶜ, ?_, Region5ᶜ, ?_, ?_, ?_, ?_ ⟩;
          · exact isOpen_compl_iff.mpr ( show IsClosed Region1234 from by exact Region1234_isClosed );
          · exact isOpen_compl_iff.mpr ( show IsClosed Region5 from by exact Region5_isClosed );
          · exact fun z hz => by specialize hL_union hz; aesop;;
          · exact ⟨ x, hxL, hx_not_in_Region1234 ⟩;
          · exact ⟨ ⟨ y, hyL, hy_not_in_Region5 ⟩, fun ⟨ z, hzL, hz_not_in_Region1234, hz_not_in_Region5 ⟩ => by have := hL_union hzL; aesop ⟩;
        -- Since $z$ is in both $Region1234$ and $Region5$, and $Region1234 \cap Region5 \subseteq segment5$, we have $z \in segment5$.
        have hz_segment5 : z ∈ segment5 := by
          have hz_segment5 : z ∈ segment ℝ (sigma X_point) (sigma Y_point) := by
            exact Region1234_inter_Region5_subset_segment_sigmaX_sigmaY ⟨ hz_both.1, hz_both.2 ⟩;
          have hz_not_endpoints : z ≠ sigma X_point ∧ z ≠ sigma Y_point := by
            constructor <;> intro h <;> simp_all +decide [ Region_Square ];
            · exact absurd ( hL_sub hzL ) ( by norm_num [ sigma, X_point ] );
            · have := hL_sub hzL; norm_num [ sigma, Y_point ] at this;
          rw [ segment_eq_image ] at *;
          obtain ⟨ θ, hθ, rfl ⟩ := hz_segment5; simp_all +decide [ segment5 ] ;
          rw [ openSegment_eq_image ];
          exact ⟨ θ, ⟨ lt_of_le_of_ne hθ.1 ( Ne.symm <| by aesop ), lt_of_le_of_ne hθ.2 ( by aesop ) ⟩, rfl ⟩;
        exact ⟨ segment5, by unfold S_finite; aesop, Set.not_disjoint_iff_nonempty_inter.mpr ⟨ z, hz_segment5, hzL ⟩ ⟩;
  intro L hL hL_sub hL12345
  exact h_union L hL hL_sub (by simpa [Region12345] using hL12345)

/-
sigma Y is not in the open unit square.
-/
lemma sigma_Y_not_in_Region_Square : sigma Y_point ∉ Region_Square := by
  exact fun h => by have := h.2.2.2; norm_num [ sigma, Y_point ] at this;

/-
y1 is greater than 0.5.
-/
lemma y1_gt_half : y1 > 0.5 := by
  unfold y1;
  -- Substitute the approximate values of V_point 0 and V_point 1.
  have h_approx : V_point 0 > 0.96 ∧ V_point 0 < 0.97 ∧ V_point 1 > 0.25 ∧ V_point 1 < 0.26 := by
    exact V_bounds;
  -- Substitute the approximate values of x1.
  have h_x1_approx : 0.95 < x1 ∧ x1 < 0.96 := by
    exact ⟨ by exact x1_prop.1, by exact x1_prop.2.1 ⟩;
  norm_num at * ; nlinarith [ mul_div_cancel₀ ( V_point 1 * ( 1 - x1 ) ) ( by linarith : ( V_point 0 - x1 ) ≠ 0 ) ] ;

/-
L2 is non-positive on Region6_Total.
-/
lemma Region6_Total_sub_L2_le_0 : ∀ p ∈ Region6_Total, L2 p ≤ 0 := by
  apply L2_convex_hull_le_0;
  simp [L2_V, L2_sigma_V_neg, L2_Y, L2_sigma_Y_neg, y1_bounds];
  exact ⟨ le_of_lt L2_sigma_V_neg, le_of_lt L2_sigma_Y_neg, by unfold L2; norm_num; nlinarith [ x1_prop.1, x1_prop.2.1, y1_bounds.1, y1_bounds.2 ] ⟩

/-
L1 is an affine function.
-/
lemma L1_affine : ∀ (x y : Point) (a b : ℝ), a + b = 1 → L1 (a • x + b • y) = a * L1 x + b * L1 y := by
  -- By definition of L1, we have L1 (a • x + b • y) = (a • x + b • y) 0 + (a • x + b • y) 1 - (V_point 0 + V_point 1).
  intro x y a b hab
  simp [L1];
  linear_combination' hab * ( V_point 0 + V_point 1 )

/-
If L1 is non-negative on a set s, it is non-negative on the convex hull of s.
-/
lemma L1_convex_hull_ge_0 (s : Set Point) (hs : ∀ p ∈ s, L1 p ≥ 0) : ∀ p ∈ convexHull ℝ s, L1 p ≥ 0 := by
  -- Since L1 is affine, the set {p | L1 p ≥ 0} is convex.
  have h_convex : Convex ℝ {p | L1 p ≥ 0} := by
    intro x hx y hy a b ha hb hab; rw [ Set.mem_setOf_eq ] at *; rw [ show L1 ( a • x + b • y ) = a * L1 x + b * L1 y by exact L1_convex_comb x y a b hab ] ; nlinarith;
  exact fun p hp => h_convex.convexHull_subset_iff.mpr hs hp

/-
L1 is positive at sigma Y.
-/
lemma L1_sigma_Y_pos : L1 (sigma Y_point) > 0 := by
  unfold L1 sigma Y_point;
  have h_sum_V : V_point 0 + V_point 1 = Real.sqrt 6 / 2 := by
    unfold V_point; ring_nf; norm_num;
    ring;
  have h_y1_gt_half : y1 > 0.5 := by
    exact y1_gt_half
  norm_num [ y1 ] at *;
  nlinarith [ Real.sqrt_nonneg 6, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ) ]

/-
L1 is positive at (1,1).
-/
lemma L1_Corner_pos : L1 !₂[1, 1] > 0 := by
  -- Substitute the values of V_point 0 and V_point 1 into the expression for L1(1,1).
  have hL1_val : L1 !₂[1, 1] = 1 + 1 - ((Real.sqrt 6 + Real.sqrt 2) / 4 + (Real.sqrt 6 - Real.sqrt 2) / 4) := by
    exact rfl;
  nlinarith [ Real.sqrt_nonneg 6, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ) ]

/-
L1 is non-negative on Region6_Total.
-/
lemma Region6_Total_sub_L1_ge_0 : ∀ p ∈ Region6_Total, L1 p ≥ 0 := by
  apply L1_convex_hull_ge_0;
  simp +zetaDelta at *;
  exact ⟨ by rw [ show L1 V_point = 0 by exact L1_V ], by rw [ show L1 ( sigma V_point ) = 0 by exact L1_sigma_V ], by exact le_of_lt ( L1_Y_pos ), by exact le_of_lt ( L1_sigma_Y_pos ), by exact le_of_lt ( L1_Corner_pos ) ⟩

/-
If S blocks R1 within U and blocks R2 globally, and the intersection in U is covered, then S blocks R1 ∪ R2 within U.
-/
lemma blocking_union_restricted_v2 {S : Set (Set Point)} {R1 R2 U : Set Point}
    (h_closed1 : IsClosed R1) (h_closed2 : IsClosed R2)
    (h_open : IsOpen U)
    (h_block1 : ∀ L, IsUnitSegment L → L ⊆ U → L ⊆ R1 → ∃ s ∈ S, ¬Disjoint s L)
    (h_block2 : IsBlocking S R2)
    (h_cover : ∀ x ∈ R1 ∩ R2 ∩ U, ∃ s ∈ S, x ∈ s) :
    ∀ L, IsUnitSegment L → L ⊆ U → L ⊆ R1 ∪ R2 → ∃ s ∈ S, ¬Disjoint s L := by
      intros L hL hL_sub_U hL_sub_R1R2
      by_cases hL_sub_R1 : L ⊆ R1;
      · exact h_block1 L hL hL_sub_U hL_sub_R1;
      · by_cases hL_sub_R2 : L ⊆ R2;
        · exact h_block2 L hL hL_sub_R2;
        · -- Since L is not contained in R1 and not contained in R2, it must intersect both R1 \ R2 and R2 \ R1.
          obtain ⟨x, hx⟩ : ∃ x ∈ L, x ∈ R1 ∧ x ∉ R2 := by
            rcases Set.not_subset.mp hL_sub_R2 with ⟨x, hxL, hx_not_R2⟩
            have hxR1 : x ∈ R1 := by
              cases hL_sub_R1R2 hxL with
              | inl hxR1 => exact hxR1
              | inr hxR2 => exact False.elim (hx_not_R2 hxR2)
            exact ⟨x, hxL, hxR1, hx_not_R2⟩
          obtain ⟨y, hy⟩ : ∃ y ∈ L, y ∈ R2 ∧ y ∉ R1 := by
            rcases Set.not_subset.mp hL_sub_R1 with ⟨y, hyL, hy_not_R1⟩
            have hyR2 : y ∈ R2 := by
              cases hL_sub_R1R2 hyL with
              | inl hyR1 => exact False.elim (hy_not_R1 hyR1)
              | inr hyR2 => exact hyR2
            exact ⟨y, hyL, hyR2, hy_not_R1⟩
          -- Since L is connected and R1, R2 are closed, L must intersect R1 ∩ R2.
          obtain ⟨z, hz⟩ : ∃ z ∈ L, z ∈ R1 ∩ R2 := by
            have h_connected : IsConnected L := by
              obtain ⟨ a, b, hab ⟩ := hL;
              rw [ hab.2 ];
              rw [ openSegment_eq_image ];
              exact ⟨ Set.Nonempty.image _ ⟨ 1 / 2, by norm_num ⟩, isPreconnected_Ioo.image _ <| Continuous.continuousOn <| by continuity ⟩;
            have h_inter : IsPreconnected L := by
              exact h_connected.isPreconnected;
            contrapose! h_inter;
            norm_num [ IsPreconnected ];
            use Set.univ \ R2, isOpen_univ.sdiff h_closed2, Set.univ \ R1, isOpen_univ.sdiff h_closed1;
            simp_all +decide [ Set.Nonempty ];
            exact ⟨ fun z hz => by cases hL_sub_R1R2 hz <;> aesop, ⟨ x, hx.1, hx.2.2 ⟩, ⟨ y, hy.1, hy.2.2 ⟩, fun z hz hz' => by cases hL_sub_R1R2 hz <;> aesop ⟩;
          exact Exists.elim ( h_cover z ⟨ hz.2, hL_sub_U hz.1 ⟩ ) fun s hs => ⟨ s, hs.1, Set.not_disjoint_iff_nonempty_inter.mpr ⟨ z, hs.2, hz.1 ⟩ ⟩

/-
The union of all defined regions is contained in the union of Region12345 and Region6_Total.
-/
lemma UnionRegions_subset_Region12345_union_Region6_Total : UnionRegions ⊆ Region12345 ∪ Region6_Total := by
  unfold UnionRegions Region12345 Region6_Total;
  unfold Region6a Region6b Region_Corner Region1234; norm_num [ Set.subset_def ] ;
  intro x hx; rcases hx with ( ( ( ( ( ( hx | hx ) | hx ) | hx ) | hx ) | hx ) | hx ) <;> simp_all +decide [ Region123 ] ;
  · unfold Region12; aesop;
  · exact Or.inr ( convexHull_mono ( by aesop_cat ) hx );
  · refine Or.inr <| convexHull_mono ?_ hx;
    grind;
  · exact Or.inr ( convexHull_mono ( by norm_num [ Set.insert_subset_iff ] ) hx )

/-
The intersection of Region1 and Region6_Total is contained in the segment connecting V and sigma V.
-/
lemma Region1_inter_Region6_Total_subset : Region1 ∩ Region6_Total ⊆ segment ℝ V_point (sigma V_point) := by
  -- By definition of $Region1 \cap Region6_Total$, we know that $Region1 \cap Region6_Total \subseteq Region123 \cap {p | L1 p = 0}$.
  have h1 : Region1 ∩ Region6_Total ⊆ Region123 ∩ {p | L1 p = 0} := by
    intro p hp_inter;
    have h1 : p ∈ Region123 ∩ {p | L1 p = 0} := by
      have h1 : p ∈ Region123 := by
        exact Or.inl <| Or.inl hp_inter.1
      have h2 : p ∈ {p | L1 p = 0} := by
        have h2 : L1 p ≤ 0 := by
          exact Region123_sub_L1_le_0 p h1
        have h3 : L1 p ≥ 0 := by
          exact Region6_Total_sub_L1_ge_0 p hp_inter.2 |> le_trans ( by norm_num ) |> le_trans <| le_rfl
        exact le_antisymm h2 h3
      exact ⟨h1, h2⟩;
    exact h1;
  exact h1.trans ( Region123_inter_L1_zero ▸ Set.Subset.refl _ )

/-
L1 is non-positive on Region2.
-/
lemma Region2_sub_L1_le_0 : ∀ p ∈ Region2, L1 p ≤ 0 := by
  have h_affine : ∀ (x y : Point) (a b : ℝ), a + b = 1 → L1 (a • x + b • y) = a * L1 x + b * L1 y := by
    -- Apply the lemma L1_affine with the given parameters.
    apply L1_affine;
  -- By definition of convex hull, any point in Region2 can be written as a convex combination of O, V, and X.
  intro p hp
  obtain ⟨a, b, c, ha, hb, hc, hsum, hp_eq⟩ : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • O_point + b • V_point + c • X_point := by
    -- By definition of convex hull, any point in the convex hull of {O, V, X} can be written as a convex combination of O, V, and X.
    have h_convex_comb : ∀ p ∈ convexHull ℝ {O_point, V_point, X_point}, ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • O_point + b • V_point + c • X_point := by
      intro p hp
      rw [convexHull_insert] at hp;
      · norm_num [ segment_eq_image ] at hp;
        rcases hp with ⟨ i, hi, x, hx, rfl ⟩ ; exact ⟨ 1 - x, x * ( 1 - i ), x * i, by linarith, by nlinarith, by nlinarith, by linarith, by ext j; fin_cases j <;> simpa using by ring ⟩ ;
      · norm_num +zetaDelta at *;
    exact h_convex_comb p hp;
  have hL1_O : L1 O_point < 0 := by
    exact L1_O_neg
  have hL1_V : L1 V_point = 0 := by
    unfold L1 V_point; norm_num;
  have hL1_X : L1 X_point < 0 := by
    exact L1_X_neg;
  have hL1_p : L1 p = a * L1 O_point + b * L1 V_point + c * L1 X_point := by
    rw [hp_eq]
    simp [L1, O_point, X_point]
    linear_combination' hsum * (V_point 0 + V_point 1)
  nlinarith

/-
The intersection of Region2 and the line L1=0 is the singleton {V}.
-/
lemma Region2_inter_L1_zero : Region2 ∩ {p | L1 p = 0} = {V_point} := by
  apply Set.eq_singleton_iff_unique_mem.mpr;
  apply And.intro (by
  exact ⟨ subset_convexHull ℝ _ ( by norm_num [ V_point ] ), by unfold L1; norm_num [ V_point ] ⟩) (by
  intro p hp
  obtain ⟨hp2, hp1⟩ := hp
  have h_convex : ∃ a b c : ℝ, a + b + c = 1 ∧ a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ p = a • O_point + b • V_point + c • X_point := by
    have h_convex : p ∈ convexHull ℝ {O_point, V_point, X_point} := by
      simpa [Region2] using hp2
    rw [ convexHull_insert ] at h_convex;
    · norm_num [ segment_eq_image ] at h_convex;
      rcases h_convex with ⟨ i, hi, x, hx, rfl ⟩ ; exact ⟨ 1 - x, x * ( 1 - i ), x * i, by ring, by nlinarith, by nlinarith, by nlinarith, by ext j; fin_cases j <;> norm_num <;> ring ⟩ ;
    · norm_num +zetaDelta at *;
  obtain ⟨ a, b, c, h₁, h₂, h₃, h₄, rfl ⟩ := h_convex; simp_all +decide [ funext_iff, Fin.forall_fin_two ] ;
  -- Since $L1(O) < 0$, $L1(V) = 0$, and $L1(X) < 0$, and $a, c \geq 0$, the equation $a*L1(O) + c*L1(X) = 0$ implies $a = 0$ and $c = 0$.
  have h_ac_zero : a = 0 ∧ c = 0 := by
    have h_ac_zero : a * L1 O_point + c * L1 X_point = 0 := by
      unfold L1 at *; norm_num [ Fin.sum_univ_succ ] at *;
      rw [ ← eq_sub_iff_add_eq' ] at h₁ ; subst_vars ; linarith!;
    have h_ac_zero : L1 O_point < 0 ∧ L1 X_point < 0 := by
      exact ⟨ L1_O_neg, L1_X_neg ⟩;
    constructor <;> nlinarith;
  aesop)

/-
The intersection of Region2 and Region6_Total is contained in the singleton {V}.
-/
lemma Region2_inter_Region6_Total_subset : Region2 ∩ Region6_Total ⊆ {V_point} := by
  intro p hp
  have hL1 : L1 p = 0 := by
    exact le_antisymm ( le_of_not_gt fun h => by linarith [ hp.1, hp.2, Region2_sub_L1_le_0 p hp.1, Region6_Total_sub_L1_ge_0 p hp.2 ] ) ( le_of_not_gt fun h => by linarith [ hp.1, hp.2, Region2_sub_L1_le_0 p hp.1, Region6_Total_sub_L1_ge_0 p hp.2 ] );
  exact Region2_inter_L1_zero.subset ⟨ hp.1, hL1 ⟩

/-
The intersection of Region3 and Region6_Total is contained in the singleton {sigma V}.
-/
lemma Region3_inter_Region6_Total_subset : Region3 ∩ Region6_Total ⊆ {sigma V_point} := by
  intro p hp
  have h_inter : p ∈ Region3 ∩ {p | L1 p = 0} := by
    have h_inter : p ∈ Region3 ∧ p ∈ Region6_Total ∧ L1 p ≤ 0 ∧ L1 p ≥ 0 := by
      exact ⟨ hp.1, hp.2, by linarith [ Region123_sub_L1_le_0 p ( Or.inr hp.1 ) ], by linarith [ Region6_Total_sub_L1_ge_0 p hp.2 ] ⟩;
    exact ⟨ h_inter.1, le_antisymm h_inter.2.2.1 h_inter.2.2.2 ⟩
  have h_sigma_V : p = sigma V_point := by
    exact Region3_inter_L1_zero.subset h_inter ▸ rfl
  exact h_sigma_V.symm ▸ Set.mem_singleton p
  skip

/-
The intersection of Region4 and the line L2=0 is the segment connecting X and Y.
-/
lemma Region4_inter_L2_zero : Region4 ∩ {p | L2 p = 0} = segment ℝ X_point Y_point := by
  apply Set.eq_of_subset_of_subset;
  · -- Any point p in Region4 ∩ {p | L2 p = 0} can be written as a convex combination of X_point, A_0, and Y_point.
    intro p hp
    obtain ⟨a, b, c, ha, hb, hc, habc, hp_eq⟩ : ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • X_point + b • A_0 + c • Y_point := by
      have h_convex : p ∈ convexHull ℝ {X_point, A_0, Y_point} := by
        exact hp.1;
      rw [ convexHull_insert ] at h_convex;
      · norm_num [ segment_eq_image ] at h_convex;
        obtain ⟨ i, hi, x, hx, rfl ⟩ := h_convex; exact ⟨ 1 - x, x * ( 1 - i ), x * i, by linarith, by nlinarith, by nlinarith, by linarith, by ext ; simpa using by ring ⟩ ;
      · norm_num +zetaDelta at *;
    -- Since $L2(p) = 0$, we have $b * L2(A0) = 0$. Given that $L2(A0) > 0$, it follows that $b = 0$.
    have hb_zero : b = 0 := by
      have hb_zero : b * L2 A_0 = 0 := by
        have hb_zero : L2 p = a * L2 X_point + b * L2 A_0 + c * L2 Y_point := by
          unfold L2; norm_num [ hp_eq ] ; ring_nf;
          rw [ ← eq_sub_iff_add_eq' ] at habc ; subst habc ; ring;
        have hL2_X : L2 X_point = 0 := by
          unfold L2 X_point; norm_num [ x1, y1 ] ;
        have hL2_Y : L2 Y_point = 0 := by
          unfold L2; norm_num [ Y_point ] ;
        simp_all +decide [ add_eq_zero_iff_eq_neg ];
      exact Or.resolve_right ( mul_eq_zero.mp hb_zero ) ( by linarith [ L2_A0_pos ] );
    exact ⟨ a, c, ha, hc, by linarith, by simp [ hb_zero, hp_eq ] ⟩;
  · intro p hp;
    -- Since $p$ is in the segment $X_point Y_point$, it is also in the convex hull of $\{X_point, A_0, Y_point\}$, which is $Region4$.
    have hp_region4 : p ∈ convexHull ℝ {X_point, A_0, Y_point} := by
      exact convexHull_mono ( by aesop_cat ) ( segment_subset_convexHull ( by aesop_cat ) ( by aesop_cat ) hp );
    refine ⟨ hp_region4, ?_ ⟩;
    rw [ segment_eq_image ] at hp;
    rcases hp with ⟨ θ, ⟨ hθ₀, hθ₁ ⟩, rfl ⟩ ; norm_num [ L2 ] ; ring_nf;
    unfold X_point Y_point; norm_num; ring;

/-
Define t_V as (1 - V_point 0) / (1 - x1).
-/
noncomputable def t_V : ℝ := (1 - V_point 0) / (1 - x1)

/-
t_V is between 0 and 1.
-/
lemma t_V_bounds : 0 ≤ t_V ∧ t_V ≤ 1 := by
  unfold t_V;
  unfold V_point x1; norm_num;
  constructor
  all_goals generalize_proofs at *;
  · exact div_nonneg ( sub_nonneg.2 <| by nlinarith [ sq_nonneg <| Real.sqrt 6 - Real.sqrt 2, Real.mul_self_sqrt ( show 6 ≥ 0 by norm_num ), Real.mul_self_sqrt ( show 2 ≥ 0 by norm_num ) ] ) ( sub_nonneg.2 <| by linarith [ Classical.choose_spec ‹∃ x : ℝ, 19 / 20 < x ∧ x < 24 / 25 ∧ poly_X x = 0› ] );
  · rw [ div_le_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 6 ≥ 0 by norm_num ), Real.sq_sqrt ( show 2 ≥ 0 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 6 > 0 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 2 > 0 by norm_num ) ), Classical.choose_spec ‹∃ x : ℝ, 19 / 20 < x ∧ x < 24 / 25 ∧ poly_X x = 0› ]

/-
1 - x1 is not zero.
-/
lemma one_sub_x1_ne_zero : 1 - x1 ≠ 0 := by
  -- Since $x1$ is between 0.95 and 0.96, we have $1 - x1 > 0$.
  have h_pos : 1 - x1 > 0 := by
    field_simp;
    rw [ sub_pos ];
    have := Classical.choose_spec exists_root_x1;
    exact this.2.1.trans_le <| by norm_num;
  exact ne_of_gt h_pos

/-
The x-coordinate of V satisfies the convex combination formula.
-/
lemma V_eq_convex_comb_x : V_point 0 = t_V * X_point 0 + (1 - t_V) * Y_point 0 := by
  unfold V_point t_V X_point Y_point;
  -- Substitute the values of V_point 0 and x1 into the equation.
  field_simp [V_point, x1]
  ring_nf;
  field_simp;
  rw [ eq_comm, div_add', div_eq_iff ] <;> ring_nf;
  · unfold V_point x1; norm_num ; ring;
  · exact one_sub_x1_ne_zero;
  · exact one_sub_x1_ne_zero

/-
The y-coordinate of V satisfies the convex combination formula.
-/
lemma V_eq_convex_comb_y : V_point 1 = t_V * X_point 1 + (1 - t_V) * Y_point 1 := by
  have hV0x1 : V_point 0 - x1 ≠ 0 := by
    have hsqrt6 : (61 : ℝ) / 25 < Real.sqrt 6 := by
      nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)]
    have hsqrt2 : (7 : ℝ) / 5 < Real.sqrt 2 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have hV0 : (24 : ℝ) / 25 < V_point 0 := by
      unfold V_point
      norm_num
      nlinarith
    have hx1 : x1 < (24 : ℝ) / 25 := by
      have hx1' := x1_prop.2.1
      norm_num at hx1' ⊢
      exact hx1'
    exact ne_of_gt (sub_pos.mpr (lt_trans hx1 hV0))
  unfold t_V X_point Y_point y1
  norm_num
  field_simp [one_sub_x1_ne_zero, hV0x1]
  ring

/-
V is a convex combination of X and Y with coefficient t_V for X.
-/
lemma V_eq_convex_comb : V_point = t_V • X_point + (1 - t_V) • Y_point := by
  ext i;
  fin_cases i <;> [ exact V_eq_convex_comb_x; exact V_eq_convex_comb_y ]

/-
The part of the segment XY where L1 is non-negative is contained in the segment VY.
-/
lemma L1_segment_XY_nonneg : ∀ p ∈ segment ℝ X_point Y_point, L1 p ≥ 0 → p ∈ segment ℝ V_point Y_point := by
  -- By definition of segment, we can write p as a convex combination of X and Y.
  intro p hp hL1
  obtain ⟨t, ht⟩ : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ p = t • X_point + (1 - t) • Y_point := by
    rw [ segment_eq_image ] at hp;
    rcases hp with ⟨ t, ⟨ ht₀, ht₁ ⟩, rfl ⟩ ; exact ⟨ 1 - t, by linarith, by linarith, by ext i; fin_cases i <;> norm_num ⟩ ;
  -- Since $L1 p \geq 0$, we have $t \leq t_V$.
  have ht_le_t_V : t ≤ t_V := by
    have ht_le_t_V : L1 p = t * L1 X_point + (1 - t) * L1 Y_point := by
      unfold L1; norm_num [ ht ] ; ring;
    have ht_le_t_V : L1 X_point < 0 ∧ L1 Y_point > 0 := by
      exact ⟨ L1_X_neg, L1_Y_pos ⟩;
    have ht_le_t_V : L1 V_point = 0 := by
      exact L1_V;
    have ht_le_t_V : L1 V_point = t_V * L1 X_point + (1 - t_V) * L1 Y_point := by
      have ht_le_t_V : V_point = t_V • X_point + (1 - t_V) • Y_point := by
        exact V_eq_convex_comb;
      rw [ht_le_t_V];
      convert L1_affine X_point Y_point t_V ( 1 - t_V ) ( by ring ) using 1;
    nlinarith;
  -- Since $t \leq t_V$, we can write $p$ as a convex combination of $V$ and $Y$.
  obtain ⟨s, hs⟩ : ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ p = s • V_point + (1 - s) • Y_point := by
    -- Substitute V_point from V_eq_convex_comb into the expression for p.
    have hp_sub : p = (t / t_V) • (t_V • X_point + (1 - t_V) • Y_point) + (1 - t / t_V) • Y_point := by
      by_cases h : t_V = 0 <;> simp_all +decide [ div_eq_inv_mul, mul_assoc, mul_left_comm, smul_smul ]
      focus
        ring_nf
      · norm_num [ show t = 0 by linarith ] at *;
      · ext i ; norm_num ; ring_nf;
        norm_num [ h ];
    exact ⟨ t / t_V, div_nonneg ht.1 ( t_V_bounds.1 ), div_le_one_of_le₀ ( by linarith ) ( t_V_bounds.1 ), hp_sub.trans ( by rw [ V_eq_convex_comb ] ) ⟩;
  exact hs.2.2 ▸ ⟨ s, 1 - s, by linarith, by linarith, by simp +decide [ hs.2.2 ] ⟩

/-
The intersection of Region4 and Region6_Total is contained in the segment connecting V and Y.
-/
lemma Region4_inter_Region6_Total_subset : Region4 ∩ Region6_Total ⊆ segment ℝ V_point Y_point := by
  intro p hp
  obtain ⟨hp4, hp6⟩ := hp
  have hL2 : L2 p = 0 := by
    -- Since $p$ is in both Region4 and Region6_Total, we have $L2 p \geq 0$ and $L2 p \leq 0$, which implies $L2 p = 0$.
    have hL2_nonneg : L2 p ≥ 0 := by
      exact Region4_sub_L2_ge_0 p hp4
    have hL2_nonpos : L2 p ≤ 0 := by
      exact Region6_Total_sub_L2_le_0 p hp6
    exact le_antisymm hL2_nonpos hL2_nonneg
  have hp_segment_XY : p ∈ segment ℝ X_point Y_point := by
    exact Region4_inter_L2_zero.subset ⟨ hp4, hL2 ⟩
  have hp_segment_VY : p ∈ segment ℝ V_point Y_point := by
    apply L1_segment_XY_nonneg p hp_segment_XY (Region6_Total_sub_L1_ge_0 p hp6)
  exact hp_segment_VY

/-
Define S_verts as the set {V, sigma V, Y, sigma Y, Corner}.
-/
def S_verts : Set Point := {V_point, sigma V_point, Y_point, sigma Y_point, Corner_point}

/-
Region6_Total is the convex hull of S_verts.
-/
lemma Region6_Total_eq_convexHull_S_verts : Region6_Total = convexHull ℝ S_verts := by
  exact rfl

/-
Region6_Total is symmetric under sigma.
-/
lemma Region6_Total_symmetric : ∀ p, p ∈ Region6_Total ↔ sigma p ∈ Region6_Total := by
  intro p;
  -- By definition of $Region6_Total$, we know that $p \in Region6_Total$ if and only if $p$ is in the convex hull of $S_verts$.
  simp [Region6_Total_eq_convexHull_S_verts];
  -- By definition of convex hull, we know that $p \in \text{conv}(S_verts)$ if and only if there exist points $x_1, x_2, \ldots, x_n \in S_verts$ and coefficients $a_1, a_2, \ldots, a_n \geq 0$ with $\sum_{i=1}^n a_i = 1$ such that $p = \sum_{i=1}^n a_i x_i$.
  simp [convexHull];
  constructor <;> intro h a ha ha' <;> have := h ( a.preimage ( fun x => sigma x ) ) ?_ ?_ <;> simp_all +decide [ Set.preimage ];
  · intro x hx
    have := ha hx
    rcases hx with ( rfl | rfl | rfl | rfl | rfl ) <;>
      simp_all +decide [ S_verts, Set.insert_subset_iff, sigma, V_point, Y_point, Corner_point ]
  · intro x hx y hy a b ha hb hab; simp_all +decide [ sigma ] ;
    convert ha' hx hy ha hb hab using 1 ; ext i ; fin_cases i <;> norm_num;
  · convert this using 1 ; ext i ; fin_cases i <;> rfl;
  · -- Since $S_verts$ is closed under $\sigma$, for any $x \in S_verts$, $\sigma(x) \in S_verts$.
    have h_sigma_S_verts : ∀ x ∈ S_verts, sigma x ∈ S_verts := by
      unfold S_verts; aesop;
    exact fun x hx => ha ( h_sigma_S_verts x hx );
  · intro x hx y hy a b ha hb hab; simp_all +decide [ sigma ] ;
    convert ha' hx hy ha hb hab using 1 ; ext i ; fin_cases i <;> norm_num

/-
The intersection of Region5 and Region6_Total is contained in the segment connecting sigma V and sigma Y.
-/
lemma Region5_inter_Region6_Total_subset : Region5 ∩ Region6_Total ⊆ segment ℝ (sigma V_point) (sigma Y_point) := by
  intro x hx;
  -- Since sigma x is in Region4 Region6_Total, by Region4_inter_Region6_Total_subset, sigma x is in the segment between V_point and Y_point.
  have h_sigma_x_segment : sigma x ∈ segment ℝ V_point Y_point := by
    -- Since $x \in \text{Region5}$, we have $\sigma(x) \in \text{Region4}$.
    have h_sigma_x_region4 : sigma x ∈ Region4 := by
      exact ( mem_Region5_iff_sigma_mem_Region4 x ).mp hx.1;
    apply Region4_inter_Region6_Total_subset;
    -- Since $x \in \text{Region6_Total}$, we have $\sigma(x) \in \text �{�Region6_Total}$ by the symmetry of $\text{Region6_Total}$.
    have h_sigma_x_region6_total : sigma x ∈ Region6_Total := by
      exact Region6_Total_symmetric x |>.1 hx.2;
    exact ⟨h_sigma_x_region4, h_sigma_x_region6_total⟩
  obtain ⟨ a, b, ha, hb, hab, h ⟩ := h_sigma_x_segment;
  use a, b;
  simp_all +decide [ ← eq_sub_iff_add_eq', funext_iff, Fin.forall_fin_two ];
  convert congr_arg sigma h using 1
  focus
    norm_num [ sigma ]
  focus
    ring_nf
  · ext i; fin_cases i <;> norm_num <;> ring;
  · ext i ; fin_cases i <;> norm_num [ sigma ] <;> ring!

/-
The segment connecting V and Y, excluding Y, is contained in segment4.
-/
lemma segment_V_Y_diff_Y_subset_segment4 : segment ℝ V_point Y_point \ {Y_point} ⊆ segment4 := by
  unfold segment4;
  -- Since $V$ is between $X$ and $Y$, any point on the segment from $V$ to $Y$ (excluding $Y$) is in the open segment from $X$ to $Y$.
  have hV_between_XY : V_point ∈ openSegment ℝ X_point Y_point := by
    simpa [segment4] using V_on_segment4
  obtain ⟨ a, b, ha, hb, hab, h ⟩ := hV_between_XY;
  intro x hx; obtain ⟨ u, v, hu, hv, huv, rfl ⟩ := hx.1; simp_all +decide [ ← eq_sub_iff_add_eq' ] ;
  refine ⟨ u * a, 1 - u * a, ?_, ?_, ?_ ⟩ <;> try nlinarith;
  · cases lt_or_eq_of_le hu <;> aesop;
  · exact ⟨ by linarith, by rw [ show V_point = a • X_point + ( 1 - a ) • Y_point by ext i; have := congrArg (fun p : Point => p i) h; norm_num at *; linarith ] ; ext i; norm_num; ring ⟩

/-
The segment connecting sigma V and sigma Y, excluding sigma Y, is contained in segment5.
-/
lemma segment_sigmaV_sigmaY_diff_sigmaY_subset_segment5 : segment ℝ (sigma V_point) (sigma Y_point) \ {sigma Y_point} ⊆ segment5 := by
  -- By definition of segment5, if x is in segment ℝ � (�sigma V_point) (sigma Y_point) and x ≠ sigma Y_point, then x must be in segment5.
  intros x hx
  obtain ⟨hx_segment, hx_ne⟩ := hx;
  -- By definition of segment, � there� exists t ∈ [0, 1] such that x = t • sigma V_point + (1 - t) • sigma Y_point.
  obtain ⟨t, ht₀, ht₁⟩ : ∃ t ∈ Set.Icc (0 : ℝ) 1, x = t • sigma V_point + (1 - t) • sigma Y_point := by
    rw [ segment_eq_image ] at hx_segment;
    rcases hx_segment with ⟨ t, ht, rfl ⟩ ; exact ⟨ 1 - t, ⟨ by linarith [ ht.1, ht.2 ], by linarith [ ht.1, ht.2 ] ⟩, by ring_nf ⟩ ;
  cases eq_or_lt_of_le ht₀.1 <;> cases eq_or_lt_of_le ht₀.2 <;> simp_all +decide [ segment_eq_image ];
  · aesop;
  · exact sigma_V_on_segment5;
  · have h_open_segment : sigma V_point ∈ openSegment ℝ (sigma X_point) (sigma Y_point) := by
      simpa [segment5] using sigma_V_on_segment5
    obtain ⟨ u, v, hu, hv, huv, h ⟩ := h_open_segment;
    exact ⟨ t * u, t * v + ( 1 - t ), by nlinarith, by nlinarith, by nlinarith, by ext i; have := congrArg (fun p : Point => p i) h; norm_num at *; nlinarith ⟩

/-
Y is not in the open unit square.
-/
lemma Y_notin_Region_Square : Y_point ∉ Region_Square := by
  -- Since $Y_point 0 = 1$, it is not in the open unit square.
  simp [Region_Square, Y_point]

/-
sigma Y is not in the open unit square.
-/
lemma sigma_Y_notin_Region_Square : sigma Y_point ∉ Region_Square := by
  exact sigma_Y_not_in_Region_Square

/-
The intersection of Region4, Region6_Total, and Region_Square is covered by S_finite.
-/
lemma Region4_inter_Region6_Total_inter_Square_covered :
  ∀ x ∈ Region4 ∩ Region6_Total ∩ Region_Square, ∃ s ∈ S_finite, x ∈ s := by
    intros x hx; exact ⟨ segment4, by simp [ S_finite ], by
      apply segment_V_Y_diff_Y_subset_segment4;
      have hx_segment : x ∈ segment ℝ V_point Y_point := by
        exact Region4_inter_Region6_Total_subset ⟨ hx.1.1, hx.1.2 ⟩ |> fun h => h |> fun h => by
          exact h;
      have hx_ne_Y : x ≠ Y_point := by
        exact fun h => hx.2 |> fun h' => by rw [ h ] at h'; exact Y_notin_Region_Square h';
      exact ⟨hx_segment, hx_ne_Y⟩ ⟩

/-
The intersection of Region5, Region6_Total, and Region_Square is covered by S_finite.
-/
lemma Region5_inter_Region6_Total_inter_Square_covered :
  ∀ x ∈ Region5 ∩ Region6_Total ∩ Region_Square, ∃ s ∈ S_finite, x ∈ s := by
    intros x hx; exact ⟨ segment5, by
      exact Or.inr <| by tauto;, by
      apply segment_sigmaV_sigmaY_diff_sigmaY_subset_segment5;
      exact ⟨ by exact Region5_inter_Region6_Total_subset ⟨ hx.1.1, hx.1.2 ⟩, by rintro rfl; exact sigma_Y_notin_Region_Square hx.2 ⟩ ⟩ ;

/-
The intersection of Region1, Region6_Total, and Region_Square is covered by S_finite.
-/
lemma Region1_inter_Region6_Total_inter_Square_covered :
  ∀ x ∈ Region1 ∩ Region6_Total ∩ Region_Square, ∃ s ∈ S_finite, x ∈ s := by
    intro x hx;
    have := Region1_inter_Region6_Total_subset ⟨ hx.1.1, hx.1.2 ⟩;
    -- The segment [V, sigma V] � is� the union of openSegment V (sigma V) (which is segment3) and the endpoints {V, sigma V}.
    have h_segment : x ∈ openSegment ℝ V_point (sigma V_point) ∨ x = V_point ∨ x = sigma V_point := by
      rw [ segment_eq_image ] at this;
      rcases this with ⟨ θ, hθ, rfl ⟩ ; cases eq_or_lt_of_le hθ.1 <;> cases eq_or_lt_of_le hθ.2 <;> simp_all +decide [ openSegment_eq_image ] ;
      · aesop;
      · grind;
    rcases h_segment with ( h | rfl | rfl );
    · exact ⟨ segment3, by unfold S_finite; norm_num, h ⟩;
    · -- Since V_point is in segment4, we can conclude that there exists a segment in S_finite containing V_point.
      use segment4
      simp [S_finite];
      exact V_on_segment4;
    · exact ⟨ segment5, by
        exact Set.mem_insert_of_mem _ ( Set.mem_insert_of_mem _ ( Set.mem_insert_of_mem _ ( Set.mem_insert_of_mem _ ( Set.mem_singleton _ ) ) ) ), by
        exact sigma_V_on_segment5 ⟩

/-
The intersection of Region2, Region6_Total, and Region_Square is covered by S_finite.
-/
lemma Region2_inter_Region6_Total_inter_Square_covered :
  ∀ x ∈ Region2 ∩ Region6_Total ∩ Region_Square, ∃ s ∈ S_finite, x ∈ s := by
    simp +zetaDelta at *;
    intro x hx1 hx2 hx3
    have hx4 : x = V_point := by
      exact Region2_inter_Region6_Total_subset ⟨ hx1, hx2 ⟩ |> fun h => by aesop;
    generalize_proofs at *;
    exact ⟨ segment4, Or.inr <| Or.inr <| Or.inr <| Or.inl rfl, by simpa [ hx4 ] using V_on_segment4 ⟩

/-
The intersection of Region3, Region6_Total, and Region_Square is covered by S_finite.
-/
lemma Region3_inter_Region6_Total_inter_Square_covered :
  ∀ x ∈ Region3 ∩ Region6_Total ∩ Region_Square, ∃ s ∈ S_finite, x ∈ s := by
    intros x hx; exact ⟨ segment5, by simp [ S_finite ], by
      -- Since $x$ is in $Region3 \cap Region6_Total$, we have $x = \sigma(V)$.
      have hx_sigma_V : x = sigma V_point := by
        exact Set.eq_of_mem_singleton ( Region3_inter_Region6_Total_subset hx.1 )
      rw [hx_sigma_V]
      exact sigma_V_on_segment5 ⟩

/-
The intersection of Region12345, Region6_Total, and Region_Square is covered by S_finite.
-/
lemma IntersectionSet_covered : ∀ x ∈ Region12345 ∩ Region6_Total ∩ Region_Square, ∃ s ∈ S_finite, x ∈ s := by
  have h_cover : ∀ x ∈ Region12345 ∩ Region6_Total ∩ Region_Square, x ∈ Region1 ∪ Region2 ∪ Region3 ∪ Region4 ∪ Region5 := by
    unfold Region12345 at *; aesop;
  intro x hx;
  rcases h_cover x hx with ( ( ( ( h | h ) | h ) | h ) | h ) <;> [ exact Region1_inter_Region6_Total_inter_Square_covered x ⟨ ⟨ h, hx.1.2 ⟩, hx.2 ⟩ ; exact Region2_inter_Region6_Total_inter_Square_covered x ⟨ ⟨ h, hx.1.2 ⟩, hx.2 ⟩ ; exact Region3_inter_Region6_Total_inter_Square_covered x ⟨ ⟨ h, hx.1.2 ⟩, hx.2 ⟩ ; exact Region4_inter_Region6_Total_inter_Square_covered x ⟨ ⟨ h, hx.1.2 ⟩, hx.2 ⟩ ; exact Region5_inter_Region6_Total_inter_Square_covered x ⟨ ⟨ h, hx.1.2 ⟩, hx.2 ⟩ ]

/-
Region12345 is a closed set.
-/
lemma Region12345_isClosed : IsClosed Region12345 := by
  -- The union of two closed sets is closed.
  apply IsClosed.union
  · exact Region1234_isClosed
  · exact Region5_isClosed

/-
S_finite blocks the open unit square.
-/
lemma S_finite_blocks_Region_Square : IsBlocking S_finite Region_Square := by
  -- Apply the blocking_union_restricted_v2 lemma with the conditions we have established.
  have h_apply : ∀ L, IsUnitSegment L → L ⊆ Region_Square → L ⊆ Region12345 ∪ Region6_Total → ∃ s ∈ S_finite, ¬Disjoint s L := by
    apply blocking_union_restricted_v2;
    · exact Region12345_isClosed
    · exact Region6_Total_isClosed
    · exact Region_Square_isOpen
    · exact fun L a a_1 a_2 ↦ Region12345_blocking_in_Square L a a_1 a_2
    · exact Region6_Total_blocking
    · exact fun x a ↦ IntersectionSet_covered x a
  -- Since `Region_Square UnionRegions` and `Union �Regions Region1234 �5 Region6_Total`, any unit segment in `Region_Square` is in `Region12345 ∪ Region6_Total`.
  have h_subset : Region_Square ⊆ Region12345 ∪ Region6_Total := by
    -- Since `Region_Square` is a subset of `UnionRegions`, and � `�UnionRegions` is a subset of `Region12345 ∪ Region6_Total`, we can conclude that `Region_Square` is a subset of `Region12345 ∪ Region6_Total`.
    have h_subset : Region_Square ⊆ UnionRegions := by
      exact Region_Square_subset_UnionRegions;
    exact h_subset.trans ( by exact UnionRegions_subset_Region12345_union_Region6_Total );
  exact fun L hL hL' => h_apply L hL hL' ( hL'.trans h_subset )

/-
The unit square is the union of the open square, the open sides, and the corners.
-/
def SquareCorners : Set Point := {!₂[0, 0], !₂[0, 1], !₂[1, 0], !₂[1, 1]}

lemma UnitSquare_decomposition (p : Point) (hp : p ∈ UnitSquare) :
  p ∈ Region_Square ∨ (∃ s ∈ S_sides, p ∈ s) ∨ p ∈ SquareCorners := by
  have hp0_nonneg : 0 ≤ p 0 := (hp 0).1
  have hp0_le_one : p 0 ≤ 1 := (hp 0).2
  have hp1_nonneg : 0 ≤ p 1 := (hp 1).1
  have hp1_le_one : p 1 ≤ 1 := (hp 1).2
  by_cases h0zero : p 0 = 0
  · by_cases h1zero : p 1 = 0
    · right
      right
      have hp_eq : p = !₂[0, 0] := by
        ext i <;> fin_cases i <;> simp [h0zero, h1zero]
      simpa [SquareCorners, hp_eq]
    · by_cases h1one : p 1 = 1
      · right
        right
        have hp_eq : p = !₂[0, 1] := by
          ext i <;> fin_cases i <;> simp [h0zero, h1one]
        simpa [SquareCorners, hp_eq]
      · right
        left
        have hp1pos : 0 < p 1 := lt_of_le_of_ne hp1_nonneg (Ne.symm h1zero)
        have hp1lt : p 1 < 1 := lt_of_le_of_ne hp1_le_one h1one
        have hp_side : p ∈ V_L := by
          unfold V_L
          rw [openSegment_eq_image]
          refine ⟨p 1, ⟨hp1pos, hp1lt⟩, ?_⟩
          ext i <;> fin_cases i <;> simp [h0zero]
        exact ⟨V_L, by simp [S_sides], hp_side⟩
  · by_cases h0one : p 0 = 1
    · by_cases h1zero : p 1 = 0
      · right
        right
        have hp_eq : p = !₂[1, 0] := by
          ext i <;> fin_cases i <;> simp [h0one, h1zero]
        simpa [SquareCorners, hp_eq]
      · by_cases h1one : p 1 = 1
        · right
          right
          have hp_eq : p = !₂[1, 1] := by
            ext i <;> fin_cases i <;> simp [h0one, h1one]
          simpa [SquareCorners, hp_eq]
        · right
          left
          have hp1pos : 0 < p 1 := lt_of_le_of_ne hp1_nonneg (Ne.symm h1zero)
          have hp1lt : p 1 < 1 := lt_of_le_of_ne hp1_le_one h1one
          have hp_side : p ∈ V_R := by
            unfold V_R
            rw [openSegment_eq_image]
            refine ⟨p 1, ⟨hp1pos, hp1lt⟩, ?_⟩
            ext i <;> fin_cases i <;> simp [h0one]
          exact ⟨V_R, by simp [S_sides], hp_side⟩
    · have hp0pos : 0 < p 0 := lt_of_le_of_ne hp0_nonneg (Ne.symm h0zero)
      have hp0lt : p 0 < 1 := lt_of_le_of_ne hp0_le_one h0one
      by_cases h1zero : p 1 = 0
      · right
        left
        have hp_side : p ∈ H_bot := by
          unfold H_bot
          rw [openSegment_eq_image]
          refine ⟨p 0, ⟨hp0pos, hp0lt⟩, ?_⟩
          ext i <;> fin_cases i <;> simp [h1zero]
        exact ⟨H_bot, by simp [S_sides], hp_side⟩
      · by_cases h1one : p 1 = 1
        · right
          left
          have hp_side : p ∈ H_top := by
            unfold H_top
            rw [openSegment_eq_image]
            refine ⟨p 0, ⟨hp0pos, hp0lt⟩, ?_⟩
            ext i <;> fin_cases i <;> simp [h1one]
          exact ⟨H_top, by simp [S_sides], hp_side⟩
        · left
          have hp1pos : 0 < p 1 := lt_of_le_of_ne hp1_nonneg (Ne.symm h1zero)
          have hp1lt : p 1 < 1 := lt_of_le_of_ne hp1_le_one h1one
          exact ⟨hp0pos, hp0lt, hp1pos, hp1lt⟩

/-
The unit square is a closed set.
-/
lemma UnitSquare_isClosed : IsClosed UnitSquare := by
  unfold UnitSquare
  simp +decide only [setOf_forall]
  refine isClosed_iInter fun i => ?_
  change IsClosed {p : Point | p i ∈ Set.Icc (0 : ℝ) 1}
  exact (isClosed_Icc : IsClosed (Set.Icc (0 : ℝ) 1)).preimage
    (by
      simpa [EuclideanSpace.coe_proj] using (EuclideanSpace.proj (𝕜 := ℝ) i).continuous)

/-
If a corner of the unit square lies in the open segment between two points in the square, then those two points must be equal to the corner.
-/
lemma SquareCorners_extreme_v2 (c : Point) (hc : c ∈ SquareCorners) (x y : Point) (hx : x ∈ UnitSquare) (hy : y ∈ UnitSquare) (h : c ∈ openSegment ℝ x y) : x = c ∧ y = c := by
  rcases hc with ( rfl | rfl | rfl | rfl ) <;> simp +decide [ *, openSegment ] at h ⊢;
  · obtain ⟨ a, ha, b, hb, hab, h ⟩ := h; have := congrArg (fun p : Point => p 0) h; have := congrArg (fun p : Point => p 1) h; simp_all +decide [ ← eq_sub_iff_add_eq' ] ;
    have := congrArg (fun p : Point => p 0) h; have := congrArg (fun p : Point => p 1) h; norm_num at *; exact ⟨ by ext i; fin_cases i <;> norm_num <;> nlinarith! [ hx 0, hx 1, hy 0, hy 1 ], by ext i; fin_cases i <;> norm_num <;> nlinarith! [ hx 0, hx 1, hy 0, hy 1 ] ⟩ ;
  · obtain ⟨ a, ha, b, hb, hab, h ⟩ := h;
    simp_all +decide [ ← List.ofFn_inj, UnitSquare ];
    have := congrArg (fun p : Point => p 0) h; have := congrArg (fun p : Point => p 1) h; norm_num at *; exact ⟨ by ext i; fin_cases i <;> norm_num <;> nlinarith !, by ext i; fin_cases i <;> norm_num <;> nlinarith ! ⟩ ;
  · rcases h with ⟨ a, ha, b, hb, hab, h ⟩ ; have := congrArg (fun p : Point => p 0) h ; have := congrArg (fun p : Point => p 1) h ; norm_num at *;
    -- Since $x$ and $y$ are in the unit square, we have $0 \leq x 0 \leq 1$ and $0 \leq y 0 \leq 1$, and similarly for $x 1$ and $y 1$.
    have hx0 : 0 ≤ x 0 ∧ x 0 ≤ 1 := by
      exact ⟨ hx 0 |>.1, hx 0 |>.2 ⟩
    have hy0 : 0 ≤ y 0 ∧ y 0 ≤ 1 := by
      exact ⟨ hy 0 |>.1, hy 0 |>.2 ⟩
    have hx1 : 0 ≤ x 1 ∧ x 1 ≤ 1 := by
      exact ⟨ hx 1 |>.1, hx 1 |>.2 ⟩
    have hy1 : 0 ≤ y 1 ∧ y 1 ≤ 1 := by
      exact ⟨ hy 1 |>.1, hy 1 |>.2 ⟩;
    -- Since $a$ and $b$ are positive and their sum is $1$, we can solve for $x_0$ and $y_0$.
    have hx0_eq : x 0 = 1 := by
      nlinarith
    have hy0_eq : y 0 = 1 := by
      nlinarith
    have hx1_eq : x 1 = 0 := by
      nlinarith [ ha, hb, hab, this, hx1, hy1 ]
    have hy1_eq : y 1 = 0 := by
      nlinarith;
    exact ⟨ by ext i; fin_cases i <;> assumption, by ext i; fin_cases i <;> assumption ⟩;
  · obtain ⟨ a, ha, b, hb, hab, h ⟩ := h; simp_all +decide [ ← List.ofFn_inj, Point ] ;
    simp_all +decide [ ← List.ofFn_inj, UnitSquare ];
    have := congrArg (fun p : Point => p 0) h; have := congrArg (fun p : Point => p 1) h; norm_num at *; exact ⟨ by ext i; fin_cases i <;> norm_num <;> nlinarith !, by ext i; fin_cases i <;> norm_num <;> nlinarith ! ⟩ ;

/-
If a unit segment in the closed unit square is disjoint from the sides, it is in the open unit square.
-/
lemma unit_segment_in_UnitSquare_disjoint_S_sides_implies_in_Region_Square (L : Set Point) (hL : IsUnitSegment L) (h_sub : L ⊆ UnitSquare) (h_disj : ∀ s ∈ S_sides, Disjoint s L) : L ⊆ Region_Square := by
  -- By `UnitSquare_decomposition`, `L ⊆ Region_Square ∪ SquareCorners`.
  have hL_decomp : L ⊆ Region_Square ∪ SquareCorners := by
    intro p hp
    have hp_unit : p ∈ UnitSquare := h_sub hp
    have hp_decomp : p ∈ Region_Square ∨ p ∈ SquareCorners ∨ ∃ s ∈ S_sides, p ∈ s := by
      have := UnitSquare_decomposition p hp_unit; aesop;
    exact hp_decomp.elim ( fun h => Or.inl h ) fun h => h.elim ( fun h => Or.inr h ) fun h => False.elim <| Set.disjoint_left.mp ( h_disj _ h.choose_spec.1 ) h.choose_spec.2 hp |> fun h => h.elim;
  -- Suppose for contradiction that $L$ contains a corner point $c$.
  by_contra h_contra;
  -- Then there exists a point $c \in L$ such that $c \in \text{SquareCorners}$.
  obtain ⟨c, hcL, hcC⟩ : ∃ c ∈ L, c ∈ SquareCorners := by
    rcases Set.not_subset.mp h_contra with ⟨c, hcL, hc_not_square⟩
    cases hL_decomp hcL with
    | inl hc_square => exact False.elim (hc_not_square hc_square)
    | inr hc_corner => exact ⟨c, hcL, hc_corner⟩
  -- By `SquareCorners_extreme_v2`, $a = c$ and $b = c$, which contradicts `hL`.
  obtain ⟨a, b, ha, hb, hab⟩ := hL
  have h_eq : a = c ∧ b = c := by
    have hab_unit : a ∈ UnitSquare ∧ b ∈ UnitSquare := by
      have h_closed : IsClosed UnitSquare := by
        exact UnitSquare_isClosed
      have h_closed_a : a ∈ UnitSquare := by
        have h_closed_a : a ∈ closure (openSegment ℝ a b) := by
          have h_closed_a : a ∈ segment ℝ a b := by
            exact left_mem_segment _ _ _
          have h_closed_a : segment ℝ a b ⊆ closure (openSegment ℝ a b) := by
            exact segment_subset_closure_openSegment;
          exact h_closed_a ‹_›;
        exact h_closed.closure_subset_iff.mpr h_sub h_closed_a |> fun h => by simpa using h;
      have h_closed_b : b ∈ UnitSquare := by
        have h_closed_b : Filter.Tendsto (fun t : ℝ => (1 - t) • a + t • b) (nhdsWithin 1 (Set.Iio 1)) (nhds b) := by
          exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num );
        exact h_closed.mem_of_tendsto h_closed_b ( Filter.eventually_of_mem ( Ioo_mem_nhdsLT zero_lt_one ) fun t ht => h_sub <| by exact ⟨ 1 - t, t, by linarith [ ht.1, ht.2 ], by linarith [ ht.1, ht.2 ], by simp +decide [ add_comm ] ⟩ ) |> fun h => by simpa using h;
      exact ⟨h_closed_a, h_closed_b⟩
    have hc_open : c ∈ openSegment ℝ a b := by
      exact hcL
    have h_eq : a = c ∧ b = c := by
      exact SquareCorners_extreme_v2 c hcC a b hab_unit.1 hab_unit.2 hc_open
    exact h_eq;
  aesop

/-
S_total blocks the closed unit square.
-/
lemma S_total_blocks_UnitSquare : IsBlocking S_total UnitSquare := by
  intro L hL hL_sub
  by_cases hL_disj_S_sides : ∀ s ∈ S_sides, Disjoint s L
  · have hL_sub_Region_Square : L ⊆ Region_Square := by
      exact
        unit_segment_in_UnitSquare_disjoint_S_sides_implies_in_Region_Square L hL hL_sub
          hL_disj_S_sides
    have hL_block_S_finite : ∃ s ∈ S_finite, ¬Disjoint s L := by
      apply S_finite_blocks_Region_Square L hL hL_sub_Region_Square
    have hL_block_S_total : ∃ s ∈ S_total, ¬Disjoint s L := by
      exact ⟨ hL_block_S_finite.choose, hL_block_S_finite.choose_spec.1 |> fun h => Set.mem_union_left _ h, hL_block_S_finite.choose_spec.2 ⟩
    exact hL_block_S_total
  · generalize_proofs at *
    unfold S_total
    aesop

/-
A disjoint collection of unit segments in a region is maximal if and only if every unit segment in the region intersects at least one segment in the collection.
-/
def IsMaximalDisjointCollection (S : Set (Set Point)) (R : Set Point) : Prop :=
  IsDisjointCollection S ∧ IsInRegion S R ∧
  ∀ S', IsDisjointCollection S' → IsInRegion S' R → S ⊆ S' → S = S'

theorem maximal_iff_blocking (S : Set (Set Point)) (R : Set Point) (hS : IsDisjointCollection S) (hR : IsInRegion S R) :
  IsMaximalDisjointCollection S R ↔ IsBlocking S R := by
    unfold IsBlocking IsMaximalDisjointCollection;
    constructor;
    · intro hL L hL1 hL2
      by_contra h_contra
      push Not at h_contra;
      -- Since $L$ is a unit segment in $R$ and is disjoint from all segments in $S$, the collection $S \cup \{L\}$ is a disjoint collection in $R$.
      have h_add_L : IsDisjointCollection (insert L S) := by
        refine ⟨ ?_, ?_ ⟩;
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
      refine ⟨ hS, hR, fun S' hS' hR' hSS' => Set.Subset.antisymm hSS' ?_ ⟩;
      intro L hL;
      contrapose! h;
      cases hS' ; aesop

/-
S_total is a maximal disjoint collection in the closed unit square.
-/
theorem S_total_maximal : IsMaximalDisjointCollection S_total UnitSquare := by
  rw [maximal_iff_blocking];
  · convert S_total_blocks_UnitSquare using 1;
  · convert S_total_is_disjoint_collection using 1;
  · exact S_total_in_UnitSquare

/-
There exists a finite maximal disjoint collection in the closed unit square.
-/
theorem erdos_1071b : ∃ S, IsMaximalDisjointCollection S UnitSquare ∧ Set.Finite S := by
  -- Let's choose the set S to be the union of S_finite and S_sides.
  use S_total;
  -- By definition of $S_total$, we know that it is finite and maximal in the closed unit square.
  apply And.intro S_total_maximal S_total_finite

end Erdos1071b

#print axioms Erdos1071.Corollary_3
-- 'Erdos1071.Corollary_3' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms Erdos1071b.erdos_1071b
-- 'Erdos1071b.erdos_1071b' depends on axioms: [propext, Classical.choice, Quot.sound]
