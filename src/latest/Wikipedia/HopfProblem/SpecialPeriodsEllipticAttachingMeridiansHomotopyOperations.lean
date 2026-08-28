import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingMeridiansHomotopy

/-!
# Operations on actual continuous families of loops

Continuous postcomposition and concatenation preserve loop squares. The
concatenated square has exactly the concatenated basepoint trajectory.
The resulting conjugacy also records any independently chosen path to
the initial basepoint, using path composition throughout.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.EllipticAttachingMeridians.LoopSquare

variable {X : Type*} [TopologicalSpace X] {a b c : X}
variable {p : Path a a} {q : Path b b} {r : Path c c}

/-- Apply a continuous map to every point of a literal loop square. -/
def postcompose {Y : Type*} [TopologicalSpace Y] (S : LoopSquare p q)
    (f : X → Y) (hf : Continuous f) : LoopSquare (p.map hf) (q.map hf) where
  map := ⟨fun z => f (S.map z), hf.comp S.map.continuous⟩
  initial u := congrArg f (S.initial u)
  final u := congrArg f (S.final u)
  closed t := congrArg f (S.closed t)

@[simp] theorem postcompose_apply {Y : Type*} [TopologicalSpace Y]
    (S : LoopSquare p q) (f : X → Y) (hf : Continuous f) (t u : unitInterval) :
    (S.postcompose f hf).map (t, u) = f (S.map (t, u)) := rfl

@[simp] theorem tail_postcompose {Y : Type*} [TopologicalSpace Y]
    (S : LoopSquare p q) (f : X → Y) (hf : Continuous f) :
    (S.postcompose f hf).tail = S.tail.map hf := by
  ext t
  rfl

/-- Concatenate two actual loop squares in the homotopy parameter. -/
def trans (S : LoopSquare p q) (T : LoopSquare q r) : LoopSquare p r where
  map := (S.homotopy.trans T.homotopy).toContinuousMap
  initial := (S.homotopy.trans T.homotopy).map_zero_left
  final := (S.homotopy.trans T.homotopy).map_one_left
  closed t := by
    change (S.homotopy.trans T.homotopy) (t, 0) =
      (S.homotopy.trans T.homotopy) (t, 1)
    simp only [ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · exact S.closed _
    · exact T.closed _

/-- Concatenation keeps the actual two-stage basepoint path, not merely its class. -/
@[simp] theorem tail_trans (S : LoopSquare p q) (T : LoopSquare q r) :
    (S.trans T).tail = S.tail.trans T.tail := by
  ext t
  change (S.homotopy.trans T.homotopy) (t, 0) = (S.tail.trans T.tail) t
  rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
  split_ifs <;> rfl

theorem homotopic_conjugate_trans (S : LoopSquare p q) (T : LoopSquare q r) :
    p.Homotopic ((S.tail.trans T.tail).trans
      (r.trans (S.tail.trans T.tail).symm)) := by
  simpa only [tail_trans] using (S.trans T).homotopic_conjugate

theorem quotient_conjugate_trans (S : LoopSquare p q) (T : LoopSquare q r) :
    Path.Homotopic.Quotient.mk p =
      Path.Homotopic.Quotient.mk ((S.tail.trans T.tail).trans
        (r.trans (S.tail.trans T.tail).symm)) :=
  Path.Homotopic.Quotient.eq.mpr (S.homotopic_conjugate_trans T)

/-- A path from the final basepoint to the initial one turns the trajectory
into the explicit based loop that conjugates the two based loop classes. -/
theorem homotopic_whisker_conjugate (S : LoopSquare p q) (τ : Path b a) :
    (τ.trans (p.trans τ.symm)).Homotopic
      ((τ.trans S.tail).trans (q.trans (τ.trans S.tail).symm)) := by
  apply Path.Homotopic.Quotient.eq.mp
  simp only [Path.trans_symm, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm]
  rw [S.quotient_conjugate]
  simp only [Path.Homotopic.Quotient.trans_assoc]

theorem quotient_whisker_conjugate (S : LoopSquare p q) (τ : Path b a) :
    Path.Homotopic.Quotient.mk (τ.trans (p.trans τ.symm)) =
      Path.Homotopic.Quotient.mk
        ((τ.trans S.tail).trans (q.trans (τ.trans S.tail).symm)) :=
  Path.Homotopic.Quotient.eq.mpr (S.homotopic_whisker_conjugate τ)

/-- The external path and both square trajectories are retained in order. -/
theorem homotopic_whisker_conjugate_trans (S : LoopSquare p q) (T : LoopSquare q r)
    (τ : Path c a) :
    (τ.trans (p.trans τ.symm)).Homotopic
      ((τ.trans (S.tail.trans T.tail)).trans
        (r.trans (τ.trans (S.tail.trans T.tail)).symm)) := by
  simpa only [tail_trans] using (S.trans T).homotopic_whisker_conjugate τ

theorem quotient_whisker_conjugate_trans (S : LoopSquare p q) (T : LoopSquare q r)
    (τ : Path c a) :
    Path.Homotopic.Quotient.mk (τ.trans (p.trans τ.symm)) =
      Path.Homotopic.Quotient.mk ((τ.trans (S.tail.trans T.tail)).trans
        (r.trans (τ.trans (S.tail.trans T.tail)).symm)) :=
  Path.Homotopic.Quotient.eq.mpr (S.homotopic_whisker_conjugate_trans T τ)

end Wikipedia.HopfProblem.SpecialPeriods.EllipticAttachingMeridians.LoopSquare
