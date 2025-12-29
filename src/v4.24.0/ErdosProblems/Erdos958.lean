/-

This is a Lean formalization of a solution to Erdős Problem 958.
https://www.erdosproblems.com/958

This proof was written by Aristotle.  It found the proof given only
the formal statement.

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/

import Mathlib


/-- The Euclidean plane `ℝ²`. -/
abbrev Point : Type := EuclideanSpace ℝ (Fin 2)

/-- Distance of an unordered pair `{p,q}` (modeled as `Sym2 Point`). -/
noncomputable def pairDist : Sym2 Point → ℝ :=
  Sym2.lift ⟨(fun p q : Point => dist p q), (fun p q => dist_comm p q)⟩

/-- Unordered pairs of **distinct** points from `A` (diagonal `{p,p}` removed). -/
noncomputable def unorderedPairs (A : Finset Point) : Finset (Sym2 Point) :=
  (A.sym2).filter (fun z => ¬ z.IsDiag)

/-- The finset of distances determined by `A`, using unordered pairs of distinct points. -/
noncomputable def distances (A : Finset Point) : Finset ℝ :=
  (unorderedPairs A).image pairDist

/-- Multiplicity of a distance `d`: number of unordered **distinct** pairs `{p,q}` in `A`
with `dist p q = d`.

Named differently to avoid clashing with existing `multiplicity` in mathlib. -/
noncomputable def distMultiplicity (A : Finset Point) (d : ℝ) : ℕ :=
  ((unorderedPairs A).filter (fun z => pairDist z = d)).card

/-- Equally spaced points on a line: an affine arithmetic progression `p₀ + i • v`. -/
def EquallySpacedOnLine (A : Finset Point) : Prop :=
  ∃ p₀ v : Point,
    v ≠ 0 ∧
      A = (Finset.range A.card).image (fun i : ℕ => p₀ + (i : ℝ) • v)

/-- The unit-circle parametrization `θ ↦ (cos θ, sin θ)` as a `Point`. -/
noncomputable def unitCircle (θ : ℝ) : Point :=
  fun j : Fin 2 => if j = 0 then Real.cos θ else Real.sin θ

/--
Equally spaced points on a circle **with constant angular step**:

There exist a center `c`, radius `r > 0`, starting angle `θ₀`, and step `Δθ`
such that `A` is exactly the image of `i ↦ c + r • unitCircle (θ₀ + i * Δθ)`
for `i = 0,1,...,n-1` where `n = A.card`.

This is the “arithmetic progression in the angle” version (not necessarily a full regular `n`-gon).
-/
def EquallySpacedOnCircle (A : Finset Point) : Prop :=
  ∃ c : Point, ∃ r θ₀ Δθ : ℝ,
    0 < r ∧
      A =
        (Finset.range A.card).image (fun i : ℕ =>
          c + r • unitCircle (θ₀ + (i : ℝ) * Δθ))

/-- The profile condition from the prompt:
* `k = n - 1`, where `k` is the number of distinct distances, and
* `{ f(d) | d ∈ D } = {1,2,...,n-1}` as finsets. -/
def HasProfile (A : Finset Point) : Prop :=
  let n := A.card
  let D := distances A
  D.card = n - 1 ∧ D.image (distMultiplicity A) = Finset.Icc 1 (n - 1)

/-
The counterexample set {(0,0), (1,0), (0,1), (0,-1)}.
-/
noncomputable def counterexample_set : Finset Point :=
  let p0 : Point := ![0, 0]
  let p1 : Point := ![1, 0]
  let p2 : Point := ![0, 1]
  let p3 : Point := ![0, -1]
  {p0, p1, p2, p3}

/-
The counterexample set satisfies the profile condition.
-/
lemma counterexample_has_profile : HasProfile counterexample_set := by
  unfold HasProfile;
  -- Let's calculate the set of distances and their multiplicities.
  have h_dist : distances counterexample_set = {1, Real.sqrt 2, 2} := by
    unfold distances counterexample_set;
    -- Let's calculate the distances between the points in the counterexample set.
    ext d
    simp [pairDist, unorderedPairs];
    constructor <;> intro h;
    · rcases h with ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; rcases a with ⟨ p, q ⟩ ; simp_all +decide [ dist_eq_norm, EuclideanSpace.norm_eq ];
      rcases ha₁ with ⟨ rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl ⟩ <;> norm_num [ Real.sqrt_eq_iff_mul_self_eq_of_pos ];
      · contradiction;
      · contradiction;
      · contradiction;
      · contradiction;
    · rcases h with ( rfl | rfl | rfl );
      · refine' ⟨ Sym2.mk ( ![0, 0], ![1, 0] ), _, _ ⟩ <;> norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
        exact ne_of_apply_ne ( fun x => x 0 ) ( by norm_num );
      · refine' ⟨ Sym2.mk ( ![0, 1], ![1, 0] ), _, _ ⟩ <;> norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
        exact ne_of_apply_ne ( fun x => x 0 ) ( by norm_num );
      · refine' ⟨ Sym2.mk ( ![0, 1], ![0, -1] ), _, _ ⟩ <;> norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
        exact ne_of_apply_ne ( fun x => x 1 ) ( by norm_num );
  -- Let's calculate the multiplicities of the distances.
  have h_mult : distMultiplicity counterexample_set 1 = 3 ∧ distMultiplicity counterexample_set (Real.sqrt 2) = 2 ∧ distMultiplicity counterexample_set 2 = 1 := by
    unfold distMultiplicity;
    erw [ show unorderedPairs counterexample_set = { Sym2.mk ( ![0, 0], ![1, 0] ), Sym2.mk ( ![0, 0], ![0, 1] ), Sym2.mk ( ![0, 0], ![0, -1] ), Sym2.mk ( ![1, 0], ![0, 1] ), Sym2.mk ( ![1, 0], ![0, -1] ), Sym2.mk ( ![0, 1], ![0, -1] ) } from ?_ ];
    · unfold pairDist;
      norm_num [ Finset.filter_insert, Finset.filter_singleton, dist_eq_norm, EuclideanSpace.norm_eq ];
      rw [ if_neg ( by nlinarith [ Real.sq_sqrt ( show 0 ≤ 2 by norm_num ) ] ), if_neg ( by nlinarith [ Real.sq_sqrt ( show 0 ≤ 2 by norm_num ) ] ), if_neg ( by nlinarith [ Real.sq_sqrt ( show 0 ≤ 2 by norm_num ) ] ), if_neg ( by nlinarith [ Real.sq_sqrt ( show 0 ≤ 2 by norm_num ) ] ) ] ; norm_num;
    · unfold counterexample_set unorderedPairs; simp +decide [ Finset.ext_iff ] ;
      intro a; constructor <;> intro ha <;> rcases a with ⟨ x, y ⟩ <;> simp_all +decide [ Sym2.eq_swap ] ;
      · grind;
      · rcases ha with ( ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> norm_num [ ← List.ofFn_inj ];
        all_goals intro h; have := congr_fun h 0; norm_num at this;
        all_goals have := congr_fun h 1; norm_num at this;
  -- Let's calculate the cardinality of the set of distances.
  have h_card : (distances counterexample_set).card = 3 := by
    rw [ h_dist, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton ] <;> aesop;
  simp_all +decide [ Finset.ext_iff ];
  erw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> norm_num [ ← List.ofFn_inj ];
  · exact fun a => ⟨ by rintro ( rfl | rfl | rfl ) <;> decide, by rintro ⟨ ha₁, ha₂ ⟩ ; interval_cases a <;> trivial ⟩;
  · exact ne_of_apply_ne ( fun x => x 1 ) ( by norm_num );
  · exact ⟨ ne_of_apply_ne ( fun x => x 0 ) ( by norm_num ), ne_of_apply_ne ( fun x => x 0 ) ( by norm_num ) ⟩;
  · exact ⟨ ne_of_apply_ne ( fun x => x 0 ) ( by norm_num ), ne_of_apply_ne ( fun x => x 1 ) ( by norm_num ), ne_of_apply_ne ( fun x => x 1 ) ( by norm_num ) ⟩

/-
The counterexample set is not equally spaced on a line.
-/
lemma counterexample_not_line : ¬ EquallySpacedOnLine counterexample_set := by
  rintro ⟨ p₀, v, hv, h ⟩;
  -- By definition of `counterexample_set`, we know that `(0,0)`, `(1,0)`, `(0,1)`, and `(0,-1)` are in `counterexample_set`.
  have h_points : ![0, 0] ∈ counterexample_set ∧ ![1, 0] ∈ counterexample_set ∧ ![0, 1] ∈ counterexample_set ∧ ![0, -1] ∈ counterexample_set := by
    exact ⟨ Finset.mem_insert_self _ _, Finset.mem_insert_of_mem ( Finset.mem_insert_self _ _ ), Finset.mem_insert_of_mem ( Finset.mem_insert_of_mem ( Finset.mem_insert_self _ _ ) ), Finset.mem_insert_of_mem ( Finset.mem_insert_of_mem ( Finset.mem_insert_of_mem ( Finset.mem_singleton_self _ ) ) ) ⟩;
  simp_all +decide [ Finset.ext_iff ];
  obtain ⟨ ⟨ a, ha, ha' ⟩, ⟨ b, hb, hb' ⟩, ⟨ c, hc, hc' ⟩, ⟨ d, hd, hd' ⟩ ⟩ := h_points;
  rw [ ← List.ofFn_inj ] at * ; norm_num at *;
  exact hv ( by nlinarith ) ( by nlinarith )

/-
The counterexample set is not equally spaced on a circle.
-/
lemma counterexample_not_circle : ¬ EquallySpacedOnCircle counterexample_set := by
  rintro ⟨ c, r, θ₀, Δθ, hr, ha ⟩;
  -- From the equality of sets, we know that the points (0,0), (1,0), (0,1), and (0,-1) must lie on the circle with center `c` and radius `r`.
  have h_points_on_circle : ∀ p ∈ ({![0, 0], ![1, 0], ![0, 1], ![0, -1]} : Finset Point), dist p c = r := by
    intro p hp
    have h_eq : p ∈ Finset.image (fun i : ℕ => c + r • unitCircle (θ₀ + (i : ℝ) * Δθ)) (Finset.range counterexample_set.card) := by
      exact ha ▸ by simpa [ counterexample_set ] using hp;
    rw [ Finset.mem_image ] at h_eq; obtain ⟨ i, hi, rfl ⟩ := h_eq; simp +decide [ dist_eq_norm, norm_smul, abs_of_pos hr ] ;
    norm_num [ EuclideanSpace.norm_eq, unitCircle ];
  norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] at h_points_on_circle;
  norm_num [ Real.sqrt_eq_iff_mul_self_eq_of_pos hr ] at h_points_on_circle ; nlinarith


/-- The question as a `Prop`. -/
def erdos_958 : Prop :=
  ∀ A : Finset Point,
    HasProfile A ↔ (EquallySpacedOnLine A ∨ EquallySpacedOnCircle A)

theorem not_erdos_958 : ¬erdos_958 := by
  have h_not_line : ¬ EquallySpacedOnLine counterexample_set := by
    exact counterexample_not_line
  have h_not_circle : ¬ EquallySpacedOnCircle counterexample_set := by
    exact counterexample_not_circle
  have h_has_profile : HasProfile counterexample_set := by
    exact counterexample_has_profile
  exact fun h => by have := h counterexample_set; aesop;

#print axioms not_erdos_958
-- 'not_erdos_958' depends on axioms: [propext, Classical.choice, Quot.sound]
