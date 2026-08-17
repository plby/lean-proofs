import ErdosProblems.Erdos113.EncodeConsecutive56

open scoped Real SimpleGraph BigOperators

namespace Erdos113SidesConsecutive56

open Consecutive56

abbrev LowHalfCycleSide {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (side : W → Bool) (b : Bool) (t : ℝ) :=
  Σ z : W, Σ x₁ : {x : W // side x = b},
    FixedWalk A 27 z x₁.1 ×
      Σ x₂ : A.neighborSet x₁.1,
        {q : FixedWalk A 28 x₂.1 z //
          (walkCount A 28 x₂.1 z : ℝ) <
            t * (walkCount A 27 z x₁.1 : ℝ)}

abbrev HighBadHalfCycleSide {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (b : Bool) (t : ℝ) :=
  Σ z : W, Σ x₂ : {x : W // side x = !b},
    Σ q : FixedWalk A 28 x₂.1 z,
      Σ x₁ : {x : ↑(walkConflictingNeighbors28 A R q) // side x.1 = b},
        {p : FixedWalk A 27 z x₁.1.1 //
          t * (walkCount A 27 z x₁.1.1 : ℝ) ≤
            (walkCount A 28 x₂.1 z : ℝ)}

lemma card_LowHalfCycleSide_cast {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (side : W → Bool) (b : Bool) (t : ℝ) :
    (Fintype.card (LowHalfCycleSide A side b t) : ℝ) =
      ∑ z : W, ∑ x₁ : {x : W // side x = b},
        (walkCount A 27 z x₁.1 : ℝ) *
          ∑ x₂ : A.neighborSet x₁.1,
            (Fintype.card {q : FixedWalk A 28 x₂.1 z //
              (walkCount A 28 x₂.1 z : ℝ) <
                t * (walkCount A 27 z x₁.1 : ℝ)} : ℝ) := by
  simp only [LowHalfCycleSide, Fintype.card_sigma, Fintype.card_prod,
    Nat.cast_sum, Nat.cast_mul]
  rfl

lemma card_LowHalfCycleSide_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (side : W → Bool) (b : Bool) (t D : ℝ) (ht : 0 ≤ t) (hD : 0 ≤ D)
    (hdegree : ∀ x, side x = b → (A.degree x : ℝ) ≤ D) :
    (Fintype.card (LowHalfCycleSide A side b t) : ℝ) ≤
      D * t * (closedWalkCount A 54 : ℝ) := by
  rw [card_LowHalfCycleSide_cast]
  calc
    (∑ z : W, ∑ x₁ : {x : W // side x = b},
        (walkCount A 27 z x₁.1 : ℝ) *
          ∑ x₂ : A.neighborSet x₁.1,
            (Fintype.card {q : FixedWalk A 28 x₂.1 z //
              (walkCount A 28 x₂.1 z : ℝ) <
                t * (walkCount A 27 z x₁.1 : ℝ)} : ℝ)) ≤
      ∑ z : W, ∑ x₁ : {x : W // side x = b},
        (walkCount A 27 z x₁.1 : ℝ) *
          (D * (t * (walkCount A 27 z x₁.1 : ℝ))) := by
      apply Finset.sum_le_sum
      intro z _
      apply Finset.sum_le_sum
      intro x₁ _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        (∑ x₂ : A.neighborSet x₁.1,
            (Fintype.card {q : FixedWalk A 28 x₂.1 z //
              (walkCount A 28 x₂.1 z : ℝ) <
                t * (walkCount A 27 z x₁.1 : ℝ)} : ℝ)) ≤
            ∑ _x₂ : A.neighborSet x₁.1,
              t * (walkCount A 27 z x₁.1 : ℝ) := by
          apply Finset.sum_le_sum
          intro x₂ _
          exact card_lowFixedWalks_le A t ht z x₁.1 x₂
        _ = (A.degree x₁.1 : ℝ) *
              (t * (walkCount A 27 z x₁.1 : ℝ)) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            SimpleGraph.card_neighborSet_eq_degree, Nat.cast_mul]
        _ ≤ D * (t * (walkCount A 27 z x₁.1 : ℝ)) := by
          exact mul_le_mul_of_nonneg_right (hdegree x₁.1 x₁.2)
            (mul_nonneg ht (by positivity))
    _ = D * t * (∑ z : W, ∑ x₁ : {x : W // side x = b},
        (walkCount A 27 z x₁.1 : ℝ) ^ 2) := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro x₁ _
      ring
    _ ≤ D * t * (∑ z : W, ∑ x₁ : W,
        (walkCount A 27 z x₁ : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hD ht)
      apply Finset.sum_le_sum
      intro z _
      rw [← Finset.sum_subtype (Finset.univ.filter fun x : W ↦ side x = b)
        (by simp) (fun x ↦ (walkCount A 27 z x : ℝ) ^ 2)]
      apply Finset.sum_le_sum_of_subset_of_nonneg (by simp)
      intro x _ _
      positivity
    _ = D * t * (closedWalkCount A 54 : ℝ) := by
      rw [show 54 = 2 * 27 by norm_num,
        closedWalkCount_cast_eq_sum_walkCount_sq]

lemma card_walkConflictingNeighbors28_le_at {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] (s : ℝ)
    (hsymm : ∀ x y, R x y → R y x)
    {z y : W} (q : FixedWalk A 28 y z)
    (hlocal : ∀ u, A.Adj y u →
      (((A.neighborFinset y).filter (R u)).card : ℝ) ≤ s) :
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
  exact hlocal _ hqadj

lemma card_HighBadHalfCycleSide_cast {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (b : Bool) (t : ℝ) :
    (Fintype.card (HighBadHalfCycleSide A R side b t) : ℝ) =
      ∑ z : W, ∑ x₂ : {x : W // side x = !b},
        ∑ q : FixedWalk A 28 x₂.1 z,
          ∑ x₁ : {x : ↑(walkConflictingNeighbors28 A R q) // side x.1 = b},
            (Fintype.card {p : FixedWalk A 27 z x₁.1.1 //
              t * (walkCount A 27 z x₁.1.1 : ℝ) ≤
                (walkCount A 28 x₂.1 z : ℝ)} : ℝ) := by
  simp only [HighBadHalfCycleSide, Fintype.card_sigma, Nat.cast_sum]

lemma card_HighBadHalfCycleSide_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (b : Bool) (t s : ℝ)
    (ht : 0 < t) (hs : 0 ≤ s)
    (hsymm : ∀ x y, R x y → R y x)
    (hlocal : ∀ u y, A.Adj y u → side y = !b →
      (((A.neighborFinset y).filter (R u)).card : ℝ) ≤ s) :
    (Fintype.card (HighBadHalfCycleSide A R side b t) : ℝ) ≤
      s * t⁻¹ * (closedWalkCount A 56 : ℝ) := by
  rw [card_HighBadHalfCycleSide_cast]
  calc
    (∑ z : W, ∑ x₂ : {x : W // side x = !b},
        ∑ q : FixedWalk A 28 x₂.1 z,
          ∑ x₁ : {x : ↑(walkConflictingNeighbors28 A R q) // side x.1 = b},
            (Fintype.card {p : FixedWalk A 27 z x₁.1.1 //
              t * (walkCount A 27 z x₁.1.1 : ℝ) ≤
                (walkCount A 28 x₂.1 z : ℝ)} : ℝ)) ≤
      ∑ z : W, ∑ x₂ : {x : W // side x = !b},
        ∑ _q : FixedWalk A 28 x₂.1 z,
          s * (t⁻¹ * (walkCount A 28 x₂.1 z : ℝ)) := by
      apply Finset.sum_le_sum
      intro z _
      apply Finset.sum_le_sum
      intro x₂ _
      apply Finset.sum_le_sum
      intro q _
      calc
        (∑ x₁ : {x : ↑(walkConflictingNeighbors28 A R q) // side x.1 = b},
            (Fintype.card {p : FixedWalk A 27 z x₁.1.1 //
              t * (walkCount A 27 z x₁.1.1 : ℝ) ≤
                (walkCount A 28 x₂.1 z : ℝ)} : ℝ)) ≤
            ∑ _x₁ : {x : ↑(walkConflictingNeighbors28 A R q) // side x.1 = b},
              t⁻¹ * (walkCount A 28 x₂.1 z : ℝ) := by
          apply Finset.sum_le_sum
          intro x₁ _
          exact card_highFixedWalks_le A R t ht z x₂.1 q x₁.1
        _ = (Fintype.card {x : ↑(walkConflictingNeighbors28 A R q) //
              side x.1 = b} : ℝ) *
              (t⁻¹ * (walkCount A 28 x₂.1 z : ℝ)) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            Nat.cast_mul]
        _ ≤ ((walkConflictingNeighbors28 A R q).card : ℝ) *
              (t⁻¹ * (walkCount A 28 x₂.1 z : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg (inv_nonneg.mpr ht.le) (by positivity))
          have hc := Fintype.card_subtype_le
            (fun x : ↑(walkConflictingNeighbors28 A R q) ↦ side x.1 = b)
          have hc' : Fintype.card {x : ↑(walkConflictingNeighbors28 A R q) //
                side x.1 = b} ≤ (walkConflictingNeighbors28 A R q).card := by
            simpa only [Fintype.card_coe] using hc
          exact_mod_cast hc'
        _ ≤ s *
              (t⁻¹ * (walkCount A 28 x₂.1 z : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg (inv_nonneg.mpr ht.le) (by positivity))
          exact card_walkConflictingNeighbors28_le_at A R s hsymm q
            (fun u huy ↦ hlocal u x₂.1 huy x₂.2)
        _ = s *
              (t⁻¹ * (walkCount A 28 x₂.1 z : ℝ)) := by ring
    _ = s * t⁻¹ * (∑ z : W,
        ∑ x₂ : {x : W // side x = !b},
          (walkCount A 28 x₂.1 z : ℝ) ^ 2) := by
      simp_rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Finset.mul_sum, walkCount]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro x₂ _
      ring
    _ ≤ s * t⁻¹ * (∑ z : W, ∑ x₂ : W,
        (walkCount A 28 x₂ z : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro z _
      rw [← Finset.sum_subtype (Finset.univ.filter fun x : W ↦ side x = !b)
        (by simp) (fun x ↦ (walkCount A 28 x z : ℝ) ^ 2)]
      apply Finset.sum_le_sum_of_subset_of_nonneg (by simp)
      intro x _ _
      positivity
    _ = s * t⁻¹ * (closedWalkCount A 56 : ℝ) := by
      rw [show 56 = 2 * 28 by norm_num,
        closedWalkCount_cast_eq_sum_walkCount_sq]
      congr 1
      exact Finset.sum_comm

abbrev HalfCycleSideSplit {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t : Bool → ℝ) :=
  Σ b : Bool,
    LowHalfCycleSide A side b (t b) ⊕
      HighBadHalfCycleSide A R side b (t b)

noncomputable def encodeBadHalfCycleSideSplit {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t : Bool → ℝ)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x) :
    BadHalfCycle A R → HalfCycleSideSplit A R side t
  | ⟨⟨z, x₁, p, x₂, q⟩, hbad⟩ =>
      let b := side x₁
      if hlow : (walkCount A 28 x₂.1 z : ℝ) <
          t b * (walkCount A 27 z x₁ : ℝ) then
        ⟨b, Sum.inl ⟨z, ⟨x₁, rfl⟩, p, x₂, ⟨q, hlow⟩⟩⟩
      else
        ⟨b, Sum.inr ⟨z, ⟨x₂.1, hcross x₂.2⟩, q,
          ⟨⟨x₁, by
            rw [mem_walkConflictingNeighbors28]
            exact ⟨by simpa using x₂.2.symm, hbad⟩⟩, rfl⟩,
          ⟨p, le_of_not_gt hlow⟩⟩⟩

noncomputable def decodeHalfCycleSideSplit {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t : Bool → ℝ) :
    HalfCycleSideSplit A R side t → RawHalfCycle A
  | ⟨_b, Sum.inl ⟨z, x₁, p, x₂, q⟩⟩ =>
      ⟨z, x₁.1, p, x₂, q.1⟩
  | ⟨_b, Sum.inr ⟨z, x₂, q, x₁, p⟩⟩ =>
      ⟨z, x₁.1.1, p.1,
        ⟨x₂.1, by
          have hx := x₁.1.2
          rw [mem_walkConflictingNeighbors28] at hx
          exact hx.1.symm⟩,
        q⟩

lemma decode_encodeBadHalfCycleSideSplit {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t : Bool → ℝ)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x)
    (b : BadHalfCycle A R) :
    decodeHalfCycleSideSplit A R side t
        (encodeBadHalfCycleSideSplit A R side t hcross b) =
      eraseBadHalfCycle A R b := by
  rcases b with ⟨⟨z, x₁, p, x₂, q⟩, hbad⟩
  simp only [encodeBadHalfCycleSideSplit]
  split <;> simp [decodeHalfCycleSideSplit, eraseBadHalfCycle]

lemma encodeBadHalfCycleSideSplit_injective {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t : Bool → ℝ)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x) :
    Function.Injective (encodeBadHalfCycleSideSplit A R side t hcross) := by
  intro b c h
  apply eraseBadHalfCycle_injective A R
  rw [← decode_encodeBadHalfCycleSideSplit A R side t hcross b,
    ← decode_encodeBadHalfCycleSideSplit A R side t hcross c, h]

lemma card_BadHalfCycle_side_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t D s : Bool → ℝ)
    (ht : ∀ b, 0 < t b) (hD : ∀ b, 0 ≤ D b) (hs : ∀ b, 0 ≤ s b)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x)
    (hdegree : ∀ x, (A.degree x : ℝ) ≤ D (side x))
    (hsymm : ∀ x y, R x y → R y x)
    (hlocal : ∀ u y, A.Adj y u →
      (((A.neighborFinset y).filter (R u)).card : ℝ) ≤ s (side y)) :
    (Fintype.card (BadHalfCycle A R) : ℝ) ≤
      ∑ b : Bool, (D b * t b * (closedWalkCount A 54 : ℝ) +
        s (!b) * (t b)⁻¹ * (closedWalkCount A 56 : ℝ)) := by
  have hcardNat := Fintype.card_le_of_injective
    (encodeBadHalfCycleSideSplit A R side t hcross)
    (encodeBadHalfCycleSideSplit_injective A R side t hcross)
  have hcard : (Fintype.card (BadHalfCycle A R) : ℝ) ≤
      Fintype.card (HalfCycleSideSplit A R side t) := by
    exact_mod_cast hcardNat
  rw [Fintype.card_sigma, Nat.cast_sum] at hcard
  refine hcard.trans ?_
  apply Finset.sum_le_sum
  intro b _
  rw [Fintype.card_sum, Nat.cast_add]
  apply add_le_add
  · exact card_LowHalfCycleSide_le A side b (t b) (D b)
      (ht b).le (hD b) (fun x hx ↦ by simpa [hx] using hdegree x)
  · exact card_HighBadHalfCycleSide_le A R side b (t b) (s (!b))
      (ht b) (hs (!b)) hsymm
      (fun u y huy hy ↦ by simpa [hy] using hlocal u y huy)

lemma card_BadClosedWalk56_side_cast_le {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (side : W → Bool) (t D s : Bool → ℝ)
    (ht : ∀ b, 0 < t b) (hD : ∀ b, 0 ≤ D b) (hs : ∀ b, 0 ≤ s b)
    (hcross : ∀ {x y}, A.Adj x y → side y = !side x)
    (hdegree : ∀ x, (A.degree x : ℝ) ≤ D (side x))
    (hsymm : ∀ x y, R x y → R y x)
    (hlocal : ∀ u y, A.Adj y u →
      (((A.neighborFinset y).filter (R u)).card : ℝ) ≤ s (side y)) :
    (Fintype.card (EncodeConsecutive56.BadClosedWalk56 A R) : ℝ) ≤
      56 * ∑ b : Bool,
        (D b * t b * (closedWalkCount A 54 : ℝ) +
          s (!b) * (t b)⁻¹ * (closedWalkCount A 56 : ℝ)) := by
  calc
    (Fintype.card (EncodeConsecutive56.BadClosedWalk56 A R) : ℝ) ≤
        56 * (Fintype.card (BadHalfCycle A R) : ℝ) := by
      exact_mod_cast EncodeConsecutive56.card_BadClosedWalk56_le A R hsymm
    _ ≤ 56 * ∑ b : Bool,
        (D b * t b * (closedWalkCount A 54 : ℝ) +
          s (!b) * (t b)⁻¹ * (closedWalkCount A 56 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact card_BadHalfCycle_side_le A R side t D s ht hD hs hcross hdegree
        hsymm hlocal

end Erdos113SidesConsecutive56
