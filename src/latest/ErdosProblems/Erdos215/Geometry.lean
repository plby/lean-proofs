import Mathlib

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-!
# The geometric interface for Erdős Problem 215

Exact coordinate translations and rotations, the embedded integer lattice, and elementary
equivalences turning the original congruent-copy statement into a transversal statement.
-/

set_option linter.style.setOption false
set_option linter.flexible false

namespace Erdos215

open Set
open scoped BigOperators

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- The Euclidean plane in standard orthonormal coordinates. -/
abbrev Point : Type := EuclideanSpace ℝ (Fin 2)

/-- Integer coordinate pairs. -/
abbrev IntPoint : Type := Fin 2 → ℤ

/-- The standard coordinate embedding of `ℤ²` in the Euclidean plane. -/
def intPoint (z : IntPoint) : Point :=
  WithLp.toLp 2 (fun i ↦ (z i : ℝ))

@[simp]
lemma intPoint_apply (z : IntPoint) (i : Fin 2) : intPoint z i = (z i : ℝ) := rfl

lemma intPoint_injective : Function.Injective intPoint := by
  intro z w h
  funext i
  have hi := congrArg (fun p : Point ↦ p i) h
  change (z i : ℝ) = (w i : ℝ) at hi
  exact Int.cast_injective hi

/-- The standard integer lattice `ℤ² ⊆ ℝ²`. -/
def integerLattice : Set Point := Set.range intPoint

@[simp]
lemma intPoint_mem_integerLattice (z : IntPoint) : intPoint z ∈ integerLattice :=
  ⟨z, rfl⟩

/-- Rotation with cosine `c` and sine `s`. It is an isometry when `c² + s² = 1`. -/
def rotate (c s : ℝ) (p : Point) : Point :=
  WithLp.toLp 2 fun i : Fin 2 ↦
    if i = 0 then c * p 0 - s * p 1 else s * p 0 + c * p 1

@[simp]
lemma rotate_apply_zero (c s : ℝ) (p : Point) :
    rotate c s p 0 = c * p 0 - s * p 1 := by
  simp [rotate]

@[simp]
lemma rotate_apply_one (c s : ℝ) (p : Point) :
    rotate c s p 1 = s * p 0 + c * p 1 := by
  simp [rotate]

@[simp]
lemma rotate_zero (c s : ℝ) : rotate c s 0 = 0 := by
  ext i
  fin_cases i <;> simp [rotate]

lemma rotate_add (c s : ℝ) (p q : Point) :
    rotate c s (p + q) = rotate c s p + rotate c s q := by
  ext i
  fin_cases i <;> simp [rotate] <;> ring

lemma rotate_sub (c s : ℝ) (p q : Point) :
    rotate c s (p - q) = rotate c s p - rotate c s q := by
  ext i
  fin_cases i <;> simp [rotate] <;> ring

lemma rotate_neg (c s : ℝ) (p : Point) :
    rotate c s (-p) = -rotate c s p := by
  ext i
  fin_cases i <;> simp [rotate] <;> ring

lemma rotate_inverse_left (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (p : Point) :
    rotate c (-s) (rotate c s p) = p := by
  have hmul (x : ℝ) : (c ^ 2 + s ^ 2) * x = x := by rw [hcs, one_mul]
  ext i
  fin_cases i
  · simp [rotate]
    calc
      c * (c * p 0 - s * p 1) + s * (s * p 0 + c * p 1) =
          (c ^ 2 + s ^ 2) * p 0 := by ring
      _ = p 0 := hmul (p 0)
  · simp [rotate]
    calc
      -(s * (c * p 0 - s * p 1)) + c * (s * p 0 + c * p 1) =
          (c ^ 2 + s ^ 2) * p 1 := by ring
      _ = p 1 := hmul (p 1)

lemma rotate_inverse_right (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (p : Point) :
    rotate c s (rotate c (-s) p) = p := by
  have hmul (x : ℝ) : (c ^ 2 + s ^ 2) * x = x := by rw [hcs, one_mul]
  ext i
  fin_cases i
  · simp [rotate]
    calc
      c * (c * p 0 + s * p 1) - s * (-(s * p 0) + c * p 1) =
          (c ^ 2 + s ^ 2) * p 0 := by ring
      _ = p 0 := hmul (p 0)
  · simp [rotate]
    calc
      s * (c * p 0 + s * p 1) + c * (-(s * p 0) + c * p 1) =
          (c ^ 2 + s ^ 2) * p 1 := by ring
      _ = p 1 := hmul (p 1)

/-- The rigid motion which first rotates and then translates. -/
def motion (t : Point) (c s : ℝ) (p : Point) : Point :=
  t + rotate c s p

/-- The inverse formula for `motion t c s`, valid when `c² + s² = 1`. -/
def inverseMotion (t : Point) (c s : ℝ) (p : Point) : Point :=
  rotate c (-s) (p - t)

lemma inverseMotion_motion (t : Point) (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1)
    (p : Point) : inverseMotion t c s (motion t c s p) = p := by
  simpa [inverseMotion, motion] using rotate_inverse_left c s hcs p

lemma motion_inverseMotion (t : Point) (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1)
    (p : Point) : motion t c s (inverseMotion t c s p) = p := by
  simp [inverseMotion, motion, rotate_inverse_right c s hcs]

/-- A translate of a rotation of `S`. -/
def movedSet (S : Set Point) (t : Point) (c s : ℝ) : Set Point :=
  motion t c s '' S

lemma mem_rotate_image_iff (S : Set Point) (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1)
    (p : Point) : p ∈ rotate c s '' S ↔ rotate c (-s) p ∈ S := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa only [rotate_inverse_left c s hcs q] using hq
  · intro hp
    refine ⟨rotate c (-s) p, hp, ?_⟩
    exact rotate_inverse_right c s hcs p

lemma mem_movedSet_iff (S : Set Point) (t : Point) (c s : ℝ)
    (hcs : c ^ 2 + s ^ 2 = 1) (p : Point) :
    p ∈ movedSet S t c s ↔ inverseMotion t c s p ∈ S := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa only [inverseMotion_motion t c s hcs q] using hq
  · intro hp
    refine ⟨inverseMotion t c s p, hp, ?_⟩
    exact motion_inverseMotion t c s hcs p

lemma movedSet_image_inverseMotion (S : Set Point) (t : Point) (c s : ℝ)
    (hcs : c ^ 2 + s ^ 2 = 1) :
    inverseMotion t c s '' movedSet S t c s = S := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (mem_movedSet_iff S t c s hcs q).mp hq
  · intro hp
    refine ⟨motion t c s p, ⟨p, hp, rfl⟩, ?_⟩
    exact inverseMotion_motion t c s hcs p

/-- Squared Euclidean distance in standard coordinates. -/
def distSq (p q : Point) : ℝ :=
  ∑ i : Fin 2, (p i - q i) ^ 2

@[simp]
lemma distSq_self (p : Point) : distSq p p = 0 := by
  simp [distSq]

lemma distSq_comm (p q : Point) : distSq p q = distSq q p := by
  simp only [distSq, Fin.sum_univ_two]
  ring

lemma distSq_eq_dist_sq (p q : Point) : distSq p q = dist p q ^ 2 := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq]
  simp [distSq, Fin.sum_univ_two]
  rw [Real.sq_sqrt]
  positivity

lemma distSq_rotate (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (p q : Point) :
    distSq (rotate c s p) (rotate c s q) = distSq p q := by
  simp [distSq, Fin.sum_univ_two, rotate]
  nlinarith

lemma distSq_motion (t : Point) (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1)
    (p q : Point) : distSq (motion t c s p) (motion t c s q) = distSq p q := by
  calc
    distSq (motion t c s p) (motion t c s q) =
        distSq (rotate c s p) (rotate c s q) := by
      simp [motion, distSq, Fin.sum_univ_two]
    _ = distSq p q := distSq_rotate c s hcs p q

lemma distSq_inverseMotion (t : Point) (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1)
    (p q : Point) :
    distSq (inverseMotion t c s p) (inverseMotion t c s q) = distSq p q := by
  have hcs' : c ^ 2 + (-s) ^ 2 = 1 := by nlinarith
  calc
    distSq (inverseMotion t c s p) (inverseMotion t c s q) =
        distSq (p - t) (q - t) := by
      exact distSq_rotate c (-s) hcs' (p - t) (q - t)
    _ = distSq p q := by simp [distSq, Fin.sum_univ_two]

/-- Squared distance between two integer coordinate pairs, as an integer. -/
def intDistSq (z w : IntPoint) : ℤ :=
  ∑ i : Fin 2, (z i - w i) ^ 2

@[simp]
lemma distSq_intPoint (z w : IntPoint) :
    distSq (intPoint z) (intPoint w) = (intDistSq z w : ℝ) := by
  simp [distSq, intDistSq, Fin.sum_univ_two]

/-- No two distinct selected points have integral squared distance. -/
def IsPartialSteinhaus (S : Set Point) : Prop :=
  ∀ ⦃p : Point⦄, p ∈ S → ∀ ⦃q : Point⦄, q ∈ S → p ≠ q →
    ∀ n : ℤ, distSq p q ≠ (n : ℝ)

/-- Every inverse image of the integer lattice under a direct rigid motion is hit. -/
def HitsEveryLattice (S : Set Point) : Prop :=
  ∀ (t : Point) (c s : ℝ), c ^ 2 + s ^ 2 = 1 →
    ∃ z : IntPoint, inverseMotion t c s (intPoint z) ∈ S

/-- The literal statement of Erdős Problem 215. -/
def IsSteinhaus (S : Set Point) : Prop :=
  ∀ (t : Point) (c s : ℝ), c ^ 2 + s ^ 2 = 1 →
    ∃! z : Point, z ∈ integerLattice ∧ z ∈ movedSet S t c s

lemma integer_points_equal_of_partial
    {S : Set Point} (hS : IsPartialSteinhaus S)
    (t : Point) (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1)
    (z w : IntPoint)
    (hz : inverseMotion t c s (intPoint z) ∈ S)
    (hw : inverseMotion t c s (intPoint w) ∈ S) : z = w := by
  by_contra hzw
  have hpq : inverseMotion t c s (intPoint z) ≠ inverseMotion t c s (intPoint w) := by
    intro h
    apply hzw
    apply intPoint_injective
    have := congrArg (motion t c s) h
    simpa only [motion_inverseMotion t c s hcs] using this
  have hnot := hS hz hw hpq (intDistSq z w)
  apply hnot
  rw [distSq_inverseMotion t c s hcs, distSq_intPoint]

/-- The partial-distance condition supplies uniqueness, so hitting every lattice is enough. -/
theorem isSteinhaus_of_partial_of_hits {S : Set Point}
    (hpartial : IsPartialSteinhaus S) (hhits : HitsEveryLattice S) : IsSteinhaus S := by
  intro t c s hcs
  obtain ⟨z, hz⟩ := hhits t c s hcs
  refine ⟨intPoint z, ⟨intPoint_mem_integerLattice z,
    (mem_movedSet_iff S t c s hcs (intPoint z)).2 hz⟩, ?_⟩
  intro p hp
  rcases hp.1 with ⟨w, rfl⟩
  have hw : inverseMotion t c s (intPoint w) ∈ S :=
    (mem_movedSet_iff S t c s hcs (intPoint w)).1 hp.2
  exact congrArg intPoint (integer_points_equal_of_partial hpartial t c s hcs w z hw hz)

end

end Erdos215
