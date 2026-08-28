import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Tactic.Abel

/-!
# Closing paths in the abelianized fundamental group

Choosing a path from a basepoint to every point turns each path into a based
loop. The class of this loop in the abelianized fundamental group is additive
under concatenation. These identities use actual paths and path homotopies;
they are the path-algebra part of the first singular Hurewicz theorem.

Mathlib multiplies fundamental-group elements in the opposite order to path
concatenation. This reversal disappears after abelianization.
-/

noncomputable section

namespace Wikipedia.HopfProblem.FirstHurewicz

variable {X : Type*} [TopologicalSpace X] {b x y z : X}

/-- The abelianized fundamental group, written additively. -/
abbrev AbelianPi1 (X : Type*) [TopologicalSpace X] (b : X) :=
  Additive (Abelianization (FundamentalGroup X b))

/-- The canonical fundamental-group element of a based loop. -/
def loopQuotient (p : Path b b) : FundamentalGroup X b :=
  Path.Homotopic.Quotient.mk p

/-- The canonical abelianized class of a based loop. -/
def loopClass (p : Path b b) : AbelianPi1 X b :=
  Additive.ofMul (Abelianization.of (loopQuotient p))

/-- Every abelianized fundamental-group element is represented by an actual loop. -/
theorem loopClass_surjective : Function.Surjective (loopClass (b := b)) := by
  intro a
  obtain ⟨g, hg⟩ := Quotient.exists_rep a.toMul
  change Abelianization.of g = a.toMul at hg
  obtain ⟨p, hp⟩ := Path.Homotopic.Quotient.mk_surjective g
  have hp' : loopQuotient p = g := hp
  refine ⟨p, ?_⟩
  rw [loopClass, hp', hg]
  rfl

theorem loopQuotient_trans (p q : Path b b) :
    loopQuotient (p.trans q) = loopQuotient q * loopQuotient p := rfl

theorem loopQuotient_symm (p : Path b b) :
    loopQuotient p.symm = (loopQuotient p)⁻¹ := rfl

/-- Homotopic based loops have the same abelianized class. -/
theorem loopClass_homotopic {p q : Path b b} (h : p.Homotopic q) :
    loopClass p = loopClass q :=
  congrArg (fun g : FundamentalGroup X b => Additive.ofMul (Abelianization.of g))
    (Path.Homotopic.Quotient.eq.mpr h)

@[simp] theorem loopClass_refl : loopClass (Path.refl b) = 0 := by
  change Additive.ofMul (Abelianization.of (1 : FundamentalGroup X b)) = 0
  rw [map_one, ofMul_one]

/-- Concatenation is addition, despite the reversed multiplication convention
in the fundamental group. -/
theorem loopClass_trans (p q : Path b b) :
    loopClass (p.trans q) = loopClass p + loopClass q := by
  rw [loopClass, loopQuotient_trans, map_mul, ofMul_mul, add_comm]
  rfl

@[simp] theorem loopClass_symm (p : Path b b) :
    loopClass p.symm = -loopClass p := by
  rw [loopClass, loopQuotient_symm, map_inv, ofMul_inv]
  rfl

/-- Close a path using the specified paths from the basepoint. -/
def basedLoop (r : ∀ x : X, Path b x) (p : Path x y) : Path b b :=
  (r x).trans (p.trans (r y).symm)

/-- The actual fundamental-group element obtained by closing a path. -/
def basedLoopQuotient (r : ∀ x : X, Path b x) (p : Path x y) :
    FundamentalGroup X b :=
  Path.Homotopic.Quotient.mk (basedLoop r p)

/-- The abelianized class obtained by closing a path at the chosen basepoint. -/
def basedLoopClass (r : ∀ x : X, Path b x) (p : Path x y) : AbelianPi1 X b :=
  loopClass (basedLoop r p)

theorem basedLoopClass_eq (r : ∀ x : X, Path b x) (p : Path x y) :
    basedLoopClass r p = Additive.ofMul (Abelianization.of (basedLoopQuotient r p)) := rfl

/-- Closing paths respects homotopy relative to their endpoints. -/
theorem basedLoop_homotopic (r : ∀ x : X, Path b x) {p q : Path x y}
    (h : p.Homotopic q) : (basedLoop r p).Homotopic (basedLoop r q) :=
  (Path.Homotopic.refl (r x)).hcomp (h.hcomp (Path.Homotopic.refl (r y).symm))

theorem basedLoopClass_homotopic (r : ∀ x : X, Path b x) {p q : Path x y}
    (h : p.Homotopic q) : basedLoopClass r p = basedLoopClass r q :=
  loopClass_homotopic (basedLoop_homotopic r h)

@[simp] theorem basedLoopQuotient_refl (r : ∀ x : X, Path b x) (x : X) :
    basedLoopQuotient r (Path.refl x) = 1 := by
  simp only [basedLoopQuotient, basedLoop, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.refl_trans, Path.Homotopic.Quotient.trans_symm,
    FundamentalGroup.one_def]

/-- Before abelianization, concatenation is multiplication in the reverse order. -/
theorem basedLoopQuotient_trans (r : ∀ x : X, Path b x) (p : Path x y)
    (q : Path y z) : basedLoopQuotient r (p.trans q) =
      basedLoopQuotient r q * basedLoopQuotient r p := by
  simp only [basedLoopQuotient, basedLoop, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm, FundamentalGroup.mul_def,
    Path.Homotopic.Quotient.trans_assoc]
  rw [← Path.Homotopic.Quotient.trans_assoc
    (Path.Homotopic.Quotient.mk (r y)).symm (Path.Homotopic.Quotient.mk (r y)),
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]

@[simp] theorem basedLoopClass_refl (r : ∀ x : X, Path b x) (x : X) :
    basedLoopClass r (Path.refl x) = 0 := by
  rw [basedLoopClass_eq, basedLoopQuotient_refl, map_one, ofMul_one]

/-- The chosen closing paths cancel at the intermediate point. -/
theorem basedLoopClass_trans (r : ∀ x : X, Path b x) (p : Path x y)
    (q : Path y z) : basedLoopClass r (p.trans q) =
      basedLoopClass r p + basedLoopClass r q := by
  rw [basedLoopClass_eq, basedLoopQuotient_trans, map_mul, ofMul_mul,
    add_comm, ← basedLoopClass_eq, ← basedLoopClass_eq]

@[simp] theorem basedLoopClass_symm (r : ∀ x : X, Path b x) (p : Path x y) :
    basedLoopClass r p.symm = -basedLoopClass r p := by
  apply eq_neg_iff_add_eq_zero.mpr
  rw [← basedLoopClass_trans, basedLoopClass_homotopic r (Path.Homotopic.symm_trans p),
    basedLoopClass_refl]

/-- For an already based loop, the auxiliary path at the basepoint contributes
only a conjugation, which vanishes in the abelianization. -/
@[simp] theorem basedLoopClass_loop (r : ∀ x : X, Path b x) (p : Path b b) :
    basedLoopClass r p = loopClass p := by
  rw [basedLoopClass, basedLoop, loopClass_trans, loopClass_trans, loopClass_symm]
  abel

/-- The additive relation supplied by a homotopy across a triangle. -/
theorem basedLoopClass_triangle (r : ∀ x : X, Path b x)
    (p₀₁ : Path x y) (p₁₂ : Path y z) (p₀₂ : Path x z)
    (h : (p₀₁.trans p₁₂).Homotopic p₀₂) :
    basedLoopClass r p₀₁ + basedLoopClass r p₁₂ = basedLoopClass r p₀₂ := by
  rw [← basedLoopClass_trans]
  exact basedLoopClass_homotopic r h

/-- The boundary sign convention for an oriented singular two-simplex. -/
theorem basedLoopClass_triangle_boundary (r : ∀ x : X, Path b x)
    (p₀₁ : Path x y) (p₁₂ : Path y z) (p₀₂ : Path x z)
    (h : (p₀₁.trans p₁₂).Homotopic p₀₂) :
    basedLoopClass r p₁₂ - basedLoopClass r p₀₂ + basedLoopClass r p₀₁ = 0 := by
  rw [← basedLoopClass_triangle r p₀₁ p₁₂ p₀₂ h]
  abel

end Wikipedia.HopfProblem.FirstHurewicz
