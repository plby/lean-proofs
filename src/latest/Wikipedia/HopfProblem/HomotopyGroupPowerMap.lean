import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Power maps on native homotopy groups

Pointwise multiplication of generalized loops into a topological monoid
induces the existing Mathlib homotopy-group multiplication. Consequently,
the pointwise `m`th power of a loop represents the `m`th power of its native
homotopy class. No computation of the homotopy groups of spheres is assumed
or proved here. The final exponent lemma has that input as an explicit
hypothesis, rather than a new axiom or a replacement homotopy group.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HomotopyGroupPowerMap

variable {N G : Type*} [TopologicalSpace G] [Monoid G] [ContinuousMul G]

/-- Literal pointwise multiplication of based generalized loops. -/
def mulLoop (p q : GenLoop N G 1) : GenLoop N G 1 :=
  ⟨p.val * q.val, fun t ht => by simp [p.property t ht, q.property t ht]⟩

@[simp] theorem mulLoop_apply (p q : GenLoop N G 1) (t : N → I) :
    mulLoop p q t = p t * q t := rfl

@[simp] theorem mulLoop_const (p : GenLoop N G 1) :
    mulLoop p GenLoop.const = p := by ext t; simp [GenLoop.const_apply]

@[simp] theorem const_mulLoop (p : GenLoop N G 1) :
    mulLoop GenLoop.const p = p := by ext t; simp [GenLoop.const_apply]

/-- Pointwise products preserve the actual boundary-relative homotopy relation. -/
theorem mulLoop_homotopic {p p' q q' : GenLoop N G 1}
    (hp : GenLoop.Homotopic p p') (hq : GenLoop.Homotopic q q') :
    GenLoop.Homotopic (mulLoop p q) (mulLoop p' q') := by
  obtain ⟨H⟩ := hp
  obtain ⟨K⟩ := hq
  exact ⟨{
    toFun := fun tx => H tx * K tx
    continuous_toFun := H.continuous.mul K.continuous
    map_zero_left := fun t => by simp
    map_one_left := fun t => by simp
    prop' := fun s t ht => by
      change H (s, t) * K (s, t) = p t * q t
      rw [H.eq_fst s ht, K.eq_fst s ht]
      rfl
  }⟩

/-- The operation on the original quotient induced by pointwise multiplication. -/
def mulClass (a b : HomotopyGroup N G 1) : HomotopyGroup N G 1 :=
  Quotient.liftOn₂ a b (fun p q => ⟦mulLoop p q⟧)
    (fun _ _ _ _ hp hq => Quotient.sound (mulLoop_homotopic hp hq))

@[simp] theorem mulClass_mk (p q : GenLoop N G 1) :
    mulClass (⟦p⟧ : HomotopyGroup N G 1) ⟦q⟧ = ⟦mulLoop p q⟧ := rfl

variable [DecidableEq N] [Nonempty N]

@[simp] theorem mulClass_one (a : HomotopyGroup N G 1) : mulClass a 1 = a := by
  refine Quotient.inductionOn a fun p => ?_
  change (⟦mulLoop p GenLoop.const⟧ : HomotopyGroup N G 1) = ⟦p⟧
  rw [mulLoop_const]

@[simp] theorem one_mulClass (a : HomotopyGroup N G 1) : mulClass 1 a = a := by
  refine Quotient.inductionOn a fun p => ?_
  change (⟦mulLoop GenLoop.const p⟧ : HomotopyGroup N G 1) = ⟦p⟧
  rw [const_mulLoop]

omit [Nonempty N] in
theorem mulLoop_transAt (i : N) (p q r s : GenLoop N G 1) :
    mulLoop (GenLoop.transAt i p q) (GenLoop.transAt i r s) =
      GenLoop.transAt i (mulLoop p r) (mulLoop q s) := by
  apply GenLoop.ext
  intro t
  change ((if (t i : ℝ) ≤ 1 / 2 then _ else _) : G) *
      ((if (t i : ℝ) ≤ 1 / 2 then _ else _) : G) =
    if (t i : ℝ) ≤ 1 / 2 then _ else _
  split_ifs <;> rfl

/-- Interchange with the native concatenation multiplication. -/
theorem mulClass_interchange (a b c d : HomotopyGroup N G 1) :
    mulClass (a * b) (c * d) = mulClass a c * mulClass b d := by
  refine Quotient.inductionOn a fun p => ?_
  refine Quotient.inductionOn b fun q => ?_
  refine Quotient.inductionOn c fun r => ?_
  refine Quotient.inductionOn d fun s => ?_
  simp only [HomotopyGroup.mul_spec (i := Classical.arbitrary N), mulClass_mk,
    mulLoop_transAt]
  rfl

/-- Eckmann--Hilton identifies pointwise and native homotopy-group products. -/
theorem mulClass_eq_mul (a b : HomotopyGroup N G 1) : mulClass a b = a * b := by
  simpa only [mul_one, one_mul, mulClass_one, one_mulClass] using
    mulClass_interchange a 1 1 b

theorem class_mulLoop (p q : GenLoop N G 1) :
    (⟦mulLoop p q⟧ : HomotopyGroup N G 1) =
      ((· * ·) : HomotopyGroup N G 1 → HomotopyGroup N G 1 →
        HomotopyGroup N G 1) ⟦p⟧ ⟦q⟧ :=
  mulClass_eq_mul ⟦p⟧ ⟦q⟧

omit [DecidableEq N] [Nonempty N] in
/-- Literal pointwise powers, with the original cube boundary fixed. -/
def powLoop (p : GenLoop N G 1) (m : ℕ) : GenLoop N G 1 :=
  ⟨p.val ^ m, fun t ht => by simp [p.property t ht]⟩

omit [DecidableEq N] [Nonempty N] in
@[simp] theorem powLoop_apply (p : GenLoop N G 1) (m : ℕ) (t : N → I) :
    powLoop p m t = p t ^ m := rfl

omit [DecidableEq N] [Nonempty N] in
@[simp] theorem powLoop_zero (p : GenLoop N G 1) : powLoop p 0 = GenLoop.const := by
  ext t; simp [GenLoop.const_apply]

omit [DecidableEq N] [Nonempty N] in
theorem powLoop_succ (p : GenLoop N G 1) (m : ℕ) :
    powLoop p (m + 1) = mulLoop (powLoop p m) p := by
  ext t; simp [pow_succ]

/-- Power maps act by the usual power on native homotopy classes. -/
theorem class_powLoop (p : GenLoop N G 1) (m : ℕ) :
    (⟦powLoop p m⟧ : HomotopyGroup N G 1) =
      ((· ^ m) : HomotopyGroup N G 1 → HomotopyGroup N G 1) ⟦p⟧ := by
  induction m with
  | zero =>
      rw [powLoop_zero]
      exact (pow_zero (M := HomotopyGroup N G 1) ⟦p⟧).symm
  | succ m ih =>
      rw [powLoop_succ, class_mulLoop, ih]
      exact (pow_succ (M := HomotopyGroup N G 1) ⟦p⟧ m).symm

/-- An explicitly supplied exponent yields an actual relative null-homotopy.
This does not assert that any particular sphere has this exponent. -/
theorem powLoop_homotopic_const_of_exponent (m : ℕ)
    (hexp : ∀ a : HomotopyGroup N G 1, a ^ m = 1) (p : GenLoop N G 1) :
    GenLoop.Homotopic (powLoop p m) GenLoop.const := by
  exact Quotient.exact ((class_powLoop p m).trans (hexp ⟦p⟧))

end Wikipedia.HopfProblem.HomotopyGroupPowerMap
