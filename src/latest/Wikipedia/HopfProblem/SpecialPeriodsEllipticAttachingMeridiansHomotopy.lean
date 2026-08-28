import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# Based conjugacy from an actual continuous family of loops

A continuous square whose vertical edges agree gives a free homotopy of
its two horizontal loops.  The path traced by the left edge is retained
explicitly.  The square proves that the initial loop followed by this
path is homotopic to this path followed by the final loop, with the
corresponding oriented conjugacy of actual path and fundamental-group
classes.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.EllipticAttachingMeridians

variable {X : Type*} [TopologicalSpace X] {a b : X}

private theorem cast_id_map (p : Path a b) :
    (Path.id.map p.continuous).cast p.source.symm p.target.symm = p := by
  ext t
  rfl

/-- An actual continuous family of closed loops with specified initial
and final loops. No path-homotopy or conjugacy conclusion is an input. -/
structure LoopSquare (p : Path a a) (q : Path b b) where
  map : C(unitInterval × unitInterval, X)
  initial : ∀ u, map (0, u) = p u
  final : ∀ u, map (1, u) = q u
  closed : ∀ t, map (t, 0) = map (t, 1)

namespace LoopSquare

variable {p : Path a a} {q : Path b b}

/-- Package a literal continuous square and its three edge identities. -/
def ofContinuous (L : unitInterval × unitInterval → X) (hL : Continuous L)
    (h₀ : ∀ u, L (0, u) = p u) (h₁ : ∀ u, L (1, u) = q u)
    (hc : ∀ t, L (t, 0) = L (t, 1)) : LoopSquare p q where
  map := ⟨L, hL⟩
  initial := h₀
  final := h₁
  closed := hc

variable (S : LoopSquare p q)

/-- The actual basepoint trajectory along the left edge of the square. -/
def tail : Path a b where
  toFun t := S.map (t, 0)
  continuous_toFun := S.map.continuous.comp (continuous_id.prodMk continuous_const)
  source' := (S.initial 0).trans p.source
  target' := (S.final 0).trans q.source

@[simp] theorem tail_apply (t : unitInterval) : S.tail t = S.map (t, 0) := rfl

/-- Forgetting the identified vertical edges gives a genuine homotopy
between the two maps from the interval. -/
def homotopy : p.toContinuousMap.Homotopy q.toContinuousMap where
  toFun := S.map
  continuous_toFun := S.map.continuous
  map_zero_left := S.initial
  map_one_left := S.final

@[simp] theorem homotopy_apply (t u : unitInterval) : S.homotopy (t, u) = S.map (t, u) := rfl

theorem homotopy_evalAt_zero :
    (S.homotopy.evalAt 0).cast p.source.symm q.source.symm = S.tail := by
  ext t
  rfl

theorem homotopy_evalAt_one :
    (S.homotopy.evalAt 1).cast p.target.symm q.target.symm = S.tail := by
  ext t
  exact (S.closed t).symm

/-- The two oriented boundary paths of the actual square are homotopic. -/
theorem homotopic_boundary : (p.trans S.tail).Homotopic (S.tail.trans q) := by
  have h := (Path.Homotopic.map_trans_evalAt S.homotopy Path.id).pathCast
    p.source.symm q.target.symm
  rw [Path.cast_trans (Path.id.map p.continuous) (S.homotopy.evalAt 1)
      p.source.symm p.target.symm q.target.symm,
    Path.cast_trans (S.homotopy.evalAt 0) (Path.id.map q.continuous)
      p.source.symm q.source.symm q.target.symm,
    cast_id_map p, cast_id_map q, S.homotopy_evalAt_zero, S.homotopy_evalAt_one] at h
  exact h

/-- Explicit based conjugacy: the initial loop is the final loop
surrounded by the actual basepoint trajectory and its reversal. -/
theorem homotopic_conjugate : p.Homotopic (S.tail.trans (q.trans S.tail.symm)) := by
  have hcancel : ((p.trans S.tail).trans S.tail.symm).Homotopic p :=
    (Path.Homotopic.trans_assoc p S.tail S.tail.symm).trans
      (((Path.Homotopic.refl p).hcomp (Path.Homotopic.trans_symm S.tail)).trans
        (Path.Homotopic.trans_refl p))
  exact hcancel.symm.trans
    ((S.homotopic_boundary.hcomp (Path.Homotopic.refl S.tail.symm)).trans
      (Path.Homotopic.trans_assoc S.tail q S.tail.symm))

/-- Equality of the actual oriented boundary classes in the fundamental groupoid. -/
theorem quotient_boundary :
    (Path.Homotopic.Quotient.mk p).trans (Path.Homotopic.Quotient.mk S.tail) =
      (Path.Homotopic.Quotient.mk S.tail).trans (Path.Homotopic.Quotient.mk q) :=
  Path.Homotopic.Quotient.eq.mpr S.homotopic_boundary

theorem quotient_conjugate :
    Path.Homotopic.Quotient.mk p =
      (Path.Homotopic.Quotient.mk S.tail).trans
        ((Path.Homotopic.Quotient.mk q).trans
          (Path.Homotopic.Quotient.mk S.tail).symm) :=
  Path.Homotopic.Quotient.eq.mpr S.homotopic_conjugate

/-- Mathlib's path-change isomorphism sends the initial loop class to
the final loop class, with the orientation determined by the given square. -/
theorem fundamentalGroup_pathChange :
    FundamentalGroup.fundamentalGroupMulEquivOfPath S.tail
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q) := by
  change (Path.Homotopic.Quotient.mk S.tail).symm.trans
    ((Path.Homotopic.Quotient.mk p).trans (Path.Homotopic.Quotient.mk S.tail)) = _
  rw [S.quotient_boundary, ← Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]

end LoopSquare

end Wikipedia.HopfProblem.SpecialPeriods.EllipticAttachingMeridians
