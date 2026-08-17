import Mathlib

open scoped Real SimpleGraph BigOperators

namespace Consecutive56

noncomputable def walkCount {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) (u v : W) : ℕ :=
  Fintype.card {p : A.Walk u v // p.length = m}

noncomputable def closedWalkCount {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) : ℕ :=
  ∑ x : W, walkCount A m x x

lemma closedWalkCount_cast_eq_trace {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) :
    (closedWalkCount A m : ℝ) = Matrix.trace (A.adjMatrix ℝ ^ m) := by
  rw [closedWalkCount, Nat.cast_sum, Matrix.trace]
  apply Finset.sum_congr rfl
  intro x _
  rw [Matrix.diag_apply, A.adjMatrix_pow_apply_eq_card_walk]
  rfl

lemma closedWalkCount_cast_eq_sum_walkCount_sq {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj] (m : ℕ) :
    (closedWalkCount A (2 * m) : ℝ) =
      ∑ u : W, ∑ v : W, (walkCount A m u v : ℝ) ^ 2 := by
  rw [closedWalkCount_cast_eq_trace]
  have hpow : A.adjMatrix ℝ ^ (2 * m) =
      A.adjMatrix ℝ ^ m * A.adjMatrix ℝ ^ m := by
    rw [show 2 * m = m + m by omega, pow_add]
  rw [hpow, Matrix.trace]
  apply Finset.sum_congr rfl
  intro u _
  rw [Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro v _
  rw [A.adjMatrix_pow_apply_eq_card_walk,
    A.adjMatrix_pow_apply_eq_card_walk]
  have hrev : walkCount A m v u = walkCount A m u v := by
    unfold walkCount
    apply Fintype.card_congr
    exact
      { toFun := fun p ↦ ⟨p.1.reverse, by simpa using p.2⟩
        invFun := fun p ↦ ⟨p.1.reverse, by simpa using p.2⟩
        left_inv := by intro p; apply Subtype.ext; simp
        right_inv := by intro p; apply Subtype.ext; simp }
  change (walkCount A m u v : ℝ) * (walkCount A m v u : ℝ) = _
  rw [hrev]
  ring

abbrev FixedWalk {W : Type*} (A : SimpleGraph W) (m : ℕ) (u v : W) :=
  {p : A.Walk u v // p.length = m}

def WalkConflict28 {W : Type*} {A : SimpleGraph W}
    (R : W → W → Prop) (x : W) {z y : W} (q : FixedWalk A 28 y z) : Prop :=
  R x (q.1.getVert 1)

noncomputable instance instDecidableWalkConflict28 {W : Type*} {A : SimpleGraph W}
    (R : W → W → Prop) [DecidableRel R] (x : W) {z y : W}
    (q : FixedWalk A 28 y z) : Decidable (WalkConflict28 R x q) :=
  Classical.propDecidable _

noncomputable def walkConflictingNeighbors28 {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    {z y : W} (q : FixedWalk A 28 y z) : Finset W := by
  classical
  exact (A.neighborFinset y).filter fun x ↦ WalkConflict28 R x q

@[simp] lemma mem_walkConflictingNeighbors28 {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    {z y : W} (q : FixedWalk A 28 y z) (x : W) :
    x ∈ walkConflictingNeighbors28 A R q ↔
      A.Adj y x ∧ WalkConflict28 R x q := by
  classical
  simp [walkConflictingNeighbors28]

lemma card_walkConflictingNeighbors28_le {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] (s : ℝ)
    (hsymm : ∀ x y, R x y → R y x)
    (hlocal : ∀ u y, A.Adj y u →
      (((A.neighborFinset y).filter (R u)).card : ℝ) ≤ s)
    {z y : W} (q : FixedWalk A 28 y z) :
    ((walkConflictingNeighbors28 A R q).card : ℝ) ≤ s := by
  classical
  have hqadj : A.Adj y (q.1.getVert 1) := by
    have h := q.1.adj_getVert_succ (show 0 < q.1.length by simp [q.2])
    simpa using h
  have heq : walkConflictingNeighbors28 A R q =
      (A.neighborFinset y).filter (R (q.1.getVert 1)) := by
    ext x
    rw [walkConflictingNeighbors28, Finset.mem_filter, Finset.mem_filter]
    change (x ∈ A.neighborFinset y ∧ R x (q.1.getVert 1)) ↔
      (x ∈ A.neighborFinset y ∧ R (q.1.getVert 1) x)
    constructor
    · rintro ⟨hxy, hR⟩
      exact ⟨hxy, hsymm _ _ hR⟩
    · rintro ⟨hxy, hR⟩
      exact ⟨hxy, hsymm _ _ hR⟩
  rw [heq]
  exact hlocal _ _ hqadj

abbrev LowHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (t : ℝ) :=
  Σ z : W, Σ x₁ : W,
    FixedWalk A 27 z x₁ ×
      Σ x₂ : A.neighborSet x₁,
        {q : FixedWalk A 28 x₂.1 z //
          (walkCount A 28 x₂.1 z : ℝ) <
            t * (walkCount A 27 z x₁ : ℝ)}

lemma card_LowHalfCycle_cast {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (t : ℝ) :
    (Fintype.card (LowHalfCycle A t) : ℝ) =
      ∑ z : W, ∑ x₁ : W,
        (walkCount A 27 z x₁ : ℝ) *
          ∑ x₂ : A.neighborSet x₁,
            (Fintype.card {q : FixedWalk A 28 x₂.1 z //
              (walkCount A 28 x₂.1 z : ℝ) <
                t * (walkCount A 27 z x₁ : ℝ)} : ℝ) := by
  simp only [LowHalfCycle, Fintype.card_sigma, Fintype.card_prod,
    Nat.cast_sum, Nat.cast_mul]
  rfl

lemma card_lowFixedWalks_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (t : ℝ) (ht : 0 ≤ t)
    (z x₁ : W) (x₂ : A.neighborSet x₁) :
    (Fintype.card {q : FixedWalk A 28 x₂.1 z //
      (walkCount A 28 x₂.1 z : ℝ) <
        t * (walkCount A 27 z x₁ : ℝ)} : ℝ) ≤
      t * (walkCount A 27 z x₁ : ℝ) := by
  let T := {q : FixedWalk A 28 x₂.1 z //
    (walkCount A 28 x₂.1 z : ℝ) <
      t * (walkCount A 27 z x₁ : ℝ)}
  have hnonneg : 0 ≤ t * (walkCount A 27 z x₁ : ℝ) :=
    mul_nonneg ht (by positivity)
  cases isEmpty_or_nonempty T with
  | inl hempty =>
      have hcard : Fintype.card T = 0 := Fintype.card_eq_zero
      rw [hcard, Nat.cast_zero]
      exact hnonneg
  | inr hnonempty =>
      let q : T := Classical.choice hnonempty
      calc
        (Fintype.card T : ℝ) ≤
            (Fintype.card (FixedWalk A 28 x₂.1 z) : ℝ) := by
          exact_mod_cast Fintype.card_subtype_le (fun _q : FixedWalk A 28 x₂.1 z ↦
            (walkCount A 28 x₂.1 z : ℝ) <
              t * (walkCount A 27 z x₁ : ℝ))
        _ = (walkCount A 28 x₂.1 z : ℝ) := rfl
        _ ≤ t * (walkCount A 27 z x₁ : ℝ) := q.2.le

lemma card_LowHalfCycle_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (t D : ℝ) (ht : 0 ≤ t)
    (hdegree : ∀ x, (A.degree x : ℝ) ≤ D) :
    (Fintype.card (LowHalfCycle A t) : ℝ) ≤
      D * t * (closedWalkCount A 54 : ℝ) := by
  rw [card_LowHalfCycle_cast]
  calc
    (∑ z : W, ∑ x₁ : W,
        (walkCount A 27 z x₁ : ℝ) *
          ∑ x₂ : A.neighborSet x₁,
            (Fintype.card {q : FixedWalk A 28 x₂.1 z //
              (walkCount A 28 x₂.1 z : ℝ) <
                t * (walkCount A 27 z x₁ : ℝ)} : ℝ)) ≤
      ∑ z : W, ∑ x₁ : W,
        (walkCount A 27 z x₁ : ℝ) *
          (D * (t * (walkCount A 27 z x₁ : ℝ))) := by
      apply Finset.sum_le_sum
      intro z _
      apply Finset.sum_le_sum
      intro x₁ _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        (∑ x₂ : A.neighborSet x₁,
            (Fintype.card {q : FixedWalk A 28 x₂.1 z //
              (walkCount A 28 x₂.1 z : ℝ) <
                t * (walkCount A 27 z x₁ : ℝ)} : ℝ)) ≤
            ∑ _x₂ : A.neighborSet x₁,
              t * (walkCount A 27 z x₁ : ℝ) := by
          apply Finset.sum_le_sum
          intro x₂ _
          exact card_lowFixedWalks_le A t ht z x₁ x₂
        _ = (A.degree x₁ : ℝ) *
              (t * (walkCount A 27 z x₁ : ℝ)) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            SimpleGraph.card_neighborSet_eq_degree, Nat.cast_mul]
        _ ≤ D * (t * (walkCount A 27 z x₁ : ℝ)) := by
          exact mul_le_mul_of_nonneg_right (hdegree x₁)
            (mul_nonneg ht (by positivity))
    _ = D * t * (∑ z : W, ∑ x₁ : W,
        (walkCount A 27 z x₁ : ℝ) ^ 2) := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro x₁ _
      ring
    _ = D * t * (closedWalkCount A 54 : ℝ) := by
      rw [show 54 = 2 * 27 by norm_num,
        closedWalkCount_cast_eq_sum_walkCount_sq]

abbrev HighBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] (t : ℝ) :=
  Σ z : W, Σ x₂ : W, Σ q : FixedWalk A 28 x₂ z,
    Σ x₁ : ↑(walkConflictingNeighbors28 A R q),
      {p : FixedWalk A 27 z x₁.1 //
        t * (walkCount A 27 z x₁.1 : ℝ) ≤
          (walkCount A 28 x₂ z : ℝ)}

lemma card_HighBadHalfCycle_cast {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] (t : ℝ) :
    (Fintype.card (HighBadHalfCycle A R t) : ℝ) =
      ∑ z : W, ∑ x₂ : W, ∑ q : FixedWalk A 28 x₂ z,
        ∑ x₁ : ↑(walkConflictingNeighbors28 A R q),
          (Fintype.card {p : FixedWalk A 27 z x₁.1 //
            t * (walkCount A 27 z x₁.1 : ℝ) ≤
              (walkCount A 28 x₂ z : ℝ)} : ℝ) := by
  simp only [HighBadHalfCycle, Fintype.card_sigma, Nat.cast_sum]

lemma card_highFixedWalks_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] (t : ℝ) (ht : 0 < t)
    (z x₂ : W) (q : FixedWalk A 28 x₂ z)
    (x₁ : ↑(walkConflictingNeighbors28 A R q)) :
    (Fintype.card {p : FixedWalk A 27 z x₁.1 //
      t * (walkCount A 27 z x₁.1 : ℝ) ≤
        (walkCount A 28 x₂ z : ℝ)} : ℝ) ≤
      t⁻¹ * (walkCount A 28 x₂ z : ℝ) := by
  let T := {p : FixedWalk A 27 z x₁.1 //
    t * (walkCount A 27 z x₁.1 : ℝ) ≤
      (walkCount A 28 x₂ z : ℝ)}
  have hnonneg : 0 ≤ t⁻¹ * (walkCount A 28 x₂ z : ℝ) :=
    mul_nonneg (inv_nonneg.mpr ht.le) (by positivity)
  cases isEmpty_or_nonempty T with
  | inl hempty =>
      have hcard : Fintype.card T = 0 := Fintype.card_eq_zero
      rw [hcard, Nat.cast_zero]
      exact hnonneg
  | inr hnonempty =>
      let p : T := Classical.choice hnonempty
      calc
        (Fintype.card T : ℝ) ≤
            (Fintype.card (FixedWalk A 27 z x₁.1) : ℝ) := by
          exact_mod_cast Fintype.card_subtype_le (fun _p : FixedWalk A 27 z x₁.1 ↦
            t * (walkCount A 27 z x₁.1 : ℝ) ≤
              (walkCount A 28 x₂ z : ℝ))
        _ = (walkCount A 27 z x₁.1 : ℝ) := rfl
        _ ≤ t⁻¹ * (walkCount A 28 x₂ z : ℝ) := by
          rw [inv_mul_eq_div]
          exact (le_div_iff₀' ht).2 p.2

lemma card_HighBadHalfCycle_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] (t s : ℝ)
    (ht : 0 < t) (hs : 0 ≤ s)
    (hsymm : ∀ x y, R x y → R y x)
    (hlocal : ∀ u y, A.Adj y u →
      (((A.neighborFinset y).filter (R u)).card : ℝ) ≤ s) :
    (Fintype.card (HighBadHalfCycle A R t) : ℝ) ≤
      s * t⁻¹ * (closedWalkCount A 56 : ℝ) := by
  rw [card_HighBadHalfCycle_cast]
  calc
    (∑ z : W, ∑ x₂ : W, ∑ q : FixedWalk A 28 x₂ z,
        ∑ x₁ : ↑(walkConflictingNeighbors28 A R q),
          (Fintype.card {p : FixedWalk A 27 z x₁.1 //
            t * (walkCount A 27 z x₁.1 : ℝ) ≤
              (walkCount A 28 x₂ z : ℝ)} : ℝ)) ≤
      ∑ z : W, ∑ x₂ : W, ∑ _q : FixedWalk A 28 x₂ z,
        s * (t⁻¹ * (walkCount A 28 x₂ z : ℝ)) := by
      apply Finset.sum_le_sum
      intro z _
      apply Finset.sum_le_sum
      intro x₂ _
      apply Finset.sum_le_sum
      intro q _
      calc
        (∑ x₁ : ↑(walkConflictingNeighbors28 A R q),
          (Fintype.card {p : FixedWalk A 27 z x₁.1 //
            t * (walkCount A 27 z x₁.1 : ℝ) ≤
              (walkCount A 28 x₂ z : ℝ)} : ℝ)) ≤
            ∑ _x₁ : ↑(walkConflictingNeighbors28 A R q),
              t⁻¹ * (walkCount A 28 x₂ z : ℝ) := by
          apply Finset.sum_le_sum
          intro x₁ _
          exact card_highFixedWalks_le A R t ht z x₂ q x₁
        _ = ((walkConflictingNeighbors28 A R q).card : ℝ) *
              (t⁻¹ * (walkCount A 28 x₂ z : ℝ)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
            nsmul_eq_mul, Nat.cast_mul]
        _ ≤ s *
              (t⁻¹ * (walkCount A 28 x₂ z : ℝ)) := by
          exact mul_le_mul_of_nonneg_right
            (card_walkConflictingNeighbors28_le A R s hsymm hlocal q)
            (mul_nonneg (inv_nonneg.mpr ht.le) (by positivity))
        _ = s *
              (t⁻¹ * (walkCount A 28 x₂ z : ℝ)) := by ring
    _ = s * t⁻¹ * (∑ z : W, ∑ x₂ : W,
        (walkCount A 28 x₂ z : ℝ) ^ 2) := by
      simp_rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Finset.mul_sum, walkCount]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro x₂ _
      ring
    _ = s * t⁻¹ * (closedWalkCount A 56 : ℝ) := by
      rw [show 56 = 2 * 28 by norm_num,
        closedWalkCount_cast_eq_sum_walkCount_sq]
      congr 1
      exact Finset.sum_comm

abbrev RawHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] :=
  Σ z : W, Σ x₁ : W,
    FixedWalk A 27 z x₁ ×
      Σ x₂ : A.neighborSet x₁, FixedWalk A 28 x₂.1 z

abbrev BadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] :=
  {b : RawHalfCycle A // WalkConflict28 R b.2.1 b.2.2.2.2}

def eraseBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] :
    BadHalfCycle A R → RawHalfCycle A
  | b => b.1

lemma eraseBadHalfCycle_injective {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] :
    Function.Injective (eraseBadHalfCycle A R) := by
  exact Subtype.val_injective

noncomputable def decodeHalfCycleSplit {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] (t : ℝ) :
    LowHalfCycle A t ⊕ HighBadHalfCycle A R t → RawHalfCycle A
  | Sum.inl ⟨z, x₁, p, x₂, q⟩ => ⟨z, x₁, p, x₂, q.1⟩
  | Sum.inr ⟨z, x₂, q, x₁, p⟩ =>
      ⟨z, x₁.1, p.1,
        ⟨x₂, by
          have hx := x₁.2
          rw [mem_walkConflictingNeighbors28] at hx
          exact hx.1.symm⟩,
        q⟩

noncomputable def encodeBadHalfCycleSplit {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] (t : ℝ) :
    BadHalfCycle A R → LowHalfCycle A t ⊕ HighBadHalfCycle A R t
  | ⟨⟨z, x₁, p, x₂, q⟩, hbad⟩ =>
      if hlow : (walkCount A 28 x₂.1 z : ℝ) <
          t * (walkCount A 27 z x₁ : ℝ) then
        Sum.inl ⟨z, x₁, p, x₂, ⟨q, hlow⟩⟩
      else
        Sum.inr ⟨z, x₂.1, q,
          ⟨x₁, by
            rw [mem_walkConflictingNeighbors28]
            exact ⟨by simpa using x₂.2.symm, hbad⟩⟩,
          ⟨p, le_of_not_gt hlow⟩⟩

lemma decode_encodeBadHalfCycleSplit {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] (t : ℝ)
    (b : BadHalfCycle A R) :
    decodeHalfCycleSplit A R t (encodeBadHalfCycleSplit A R t b) =
      eraseBadHalfCycle A R b := by
  rcases b with ⟨⟨z, x₁, p, x₂, q⟩, hbad⟩
  simp only [encodeBadHalfCycleSplit]
  split <;> simp [decodeHalfCycleSplit, eraseBadHalfCycle]

lemma encodeBadHalfCycleSplit_injective {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] (t : ℝ) :
    Function.Injective (encodeBadHalfCycleSplit A R t) := by
  intro b c h
  apply eraseBadHalfCycle_injective A R
  rw [← decode_encodeBadHalfCycleSplit A R t b,
    ← decode_encodeBadHalfCycleSplit A R t c, h]

lemma card_BadHalfCycle_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] (t D s : ℝ)
    (ht : 0 < t) (hs : 0 ≤ s)
    (hdegree : ∀ x, (A.degree x : ℝ) ≤ D)
    (hsymm : ∀ x y, R x y → R y x)
    (hlocal : ∀ u y, A.Adj y u →
      (((A.neighborFinset y).filter (R u)).card : ℝ) ≤ s) :
    (Fintype.card (BadHalfCycle A R) : ℝ) ≤
      D * t * (closedWalkCount A 54 : ℝ) +
        s * t⁻¹ * (closedWalkCount A 56 : ℝ) := by
  have hcardNat := Fintype.card_le_of_injective
    (encodeBadHalfCycleSplit A R t) (encodeBadHalfCycleSplit_injective A R t)
  have hcard : (Fintype.card (BadHalfCycle A R) : ℝ) ≤
      Fintype.card (LowHalfCycle A t ⊕ HighBadHalfCycle A R t) := by
    exact_mod_cast hcardNat
  rw [Fintype.card_sum, Nat.cast_add] at hcard
  exact hcard.trans (add_le_add
    (card_LowHalfCycle_le A t D ht.le hdegree)
    (card_HighBadHalfCycle_le A R t s ht hs hsymm hlocal))

end Consecutive56
