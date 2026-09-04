import Wikipedia.GreenTao.Sieve.PairedLocalFactors
import Wikipedia.GreenTao.Sieve.WTrickedLocalFactors

/-!
# Finite-box congruence boundaries for the CFZ divisor expansion

This file isolates the exact finite-box step between the divisor expansion
and the prime-local arithmetic.  It has three layers.

* A normalized boundary estimate compares a bounded periodic function on a
  natural box with its exact residue-class mean.
* Coordinatewise `Fin`/`ZMod` equivalences identify the mean on a
  `CubePoint k N` with the corresponding natural box mean.
* For the cyclic representative used by `cfzWTrickedLinearValue`, periodicity
  modulo a divisor modulus `D` is proved under the precise compatibility
  hypothesis `D ∣ W * N`.

The compatibility hypothesis in the last item is mathematically necessary
for this direct rectangular trimming argument: reducing a form modulo `N`
can change an integer lift by a multiple of `N`, and the subsequent
`W`-trick changes its value by a multiple of `W * N`.  Without divisibility
by `D`, an unconditional treatment must subdivide the box into carry cells
on which every modular reduction has a fixed integer lift.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Why cyclic representatives need a compatibility or carry argument -/

/-- The direct periodicity assertion is false without lift compatibility.
Here `2` and `4` are congruent modulo `2`, but their representatives modulo
`3` are `2` and `1`, respectively. -/
theorem not_periodic_cyclic_divisibility_example :
    ¬PeriodicInEachCoordinate
      (fun x : Fin 1 → ℕ =>
        natDivisibilityIndicator 2
          (wTrickedValue 1 0 (x 0 : ZMod 3)))
      2 := by
  intro hperiodic
  have hbad :=
    hperiodic (fun _ : Fin 1 => 2) (fun _ : Fin 1 => 4)
      (fun _ => by norm_num)
  norm_num [natDivisibilityIndicator, wTrickedValue,
    ZMod.val_natCast, ZMod.val_ofNat] at hbad

/-- A carry cell records a region on which every cyclic CFZ form has a fixed
integer lift.  An unconditional replacement of the cyclic density by affine
local factors needs:

1. a finite partition of the natural box into sets satisfying this
   predicate, for a bounded family of carry vectors; and
2. a residue-class discrepancy estimate on each such (rational polyhedral)
   cell, with total error `O(D * N^(card-1))`.

Rectangular trimming proves the second item only for boxes, which is why the
compatibility hypothesis appears in the theorem below. -/
def IsCFZCarryCell
    {κ : Type*} {k N : ℕ}
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (cell : Finset (CFZVariable k → ℕ)) : Prop :=
  ∀ x ∈ cell, ∀ q,
    (cfzAffineForm (forms q)).eval (fun v => (x v : ℤ)) =
      (apLinearForm k N (forms q).1 (forms q).2
        (fun i b => (x (i, b) : ZMod N))).val +
        (N : ℤ) * carry q

/-! ## Weighted lifts through two moduli -/

/-- Multiplication by `W` makes the standard representative of a residue
modulo `N` independent of the chosen integer lift modulo `D`, provided
`D ∣ W * N`. -/
theorem weighted_val_cast_eq_intCast_of_dvd
    {N D W : ℕ} [NeZero N]
    (hD : D ∣ W * N) (a : ZMod N) (A : ℤ)
    (hA : (A : ZMod N) = a) :
    ((W * a.val : ℕ) : ZMod D) =
      (((W : ℤ) * A : ℤ) : ZMod D) := by
  have hAN : (N : ℤ) ∣ (a.val : ℤ) - A := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    simpa using hA
  obtain ⟨t, ht⟩ := hAN
  have hDint : (D : ℤ) ∣ (W : ℤ) * N := by
    exact_mod_cast hD
  rw [← Int.cast_natCast (R := ZMod D) (W * a.val)]
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub
    (W * a.val : ℕ) ((W : ℤ) * A) D).2
  norm_num only [Int.natCast_mul]
  obtain ⟨u, hu⟩ := hDint
  refine ⟨-(u * t), ?_⟩
  calc
    (W : ℤ) * A - (W : ℤ) * a.val =
        -(W : ℤ) * ((a.val : ℤ) - A) := by ring
    _ = -(W : ℤ) * ((N : ℤ) * t) := by rw [ht]
    _ = (-((W : ℤ) * N)) * t := by ring
    _ = (-((D : ℤ) * u)) * t := by rw [hu]
    _ = (D : ℤ) * (-(u * t)) := by ring

/-! ## Natural representatives of CFZ cube points -/

/-- Interpret a natural vector as a doubled CFZ variable vector modulo `N`. -/
def cubePointOfNat {k N : ℕ}
    (x : CFZVariable k → ℕ) : CubePoint k N :=
  fun i b => (x (i, b) : ZMod N)

@[simp]
theorem cubePointOfNat_apply {k N : ℕ}
    (x : CFZVariable k → ℕ) (i : Fin k) (b : Bool) :
    cubePointOfNat (N := N) x i b = (x (i, b) : ZMod N) :=
  rfl

/-- Casting an integer affine evaluation agrees with first reducing all
inputs and coefficients modulo the target modulus. -/
theorem AffineForm.intCast_eval_eq_evalZMod
    {ι : Type*} [Fintype ι]
    (D : ℕ) (ψ : AffineForm ι ℤ) (x : ι → ℤ) :
    ((ψ.eval x : ℤ) : ZMod D) =
      ψ.evalZMod D (fun i => (x i : ZMod D)) := by
  simp only [AffineForm.eval, AffineForm.evalZMod,
    AffineForm.linearMapZMod]
  push_cast
  rfl

/-- The integer CFZ form evaluated on natural representatives represents
the cyclic CFZ form modulo `N`. -/
theorem intCast_cfzAffineForm_eval_eq_apLinearForm
    {k N : ℕ}
    (q : CFZFormIndex k) (x : CFZVariable k → ℕ) :
    (((cfzAffineForm q).eval
        (fun v => (x v : ℤ)) : ℤ) : ZMod N) =
      apLinearForm k N q.1 q.2
        (cubePointOfNat (N := N) x) := by
  rw [← cfzCoefficientEval_eq_apLinearForm k N q]
  unfold cfzCoefficientEval
  simp only [AffineForm.eval, cfzAffineForm_constant,
    cfzAffineForm_coefficient, zero_add]
  push_cast
  rfl

/-! ## Canonical carry cells -/

/-- The integer carry made when an integer CFZ affine form is reduced to its
standard representative modulo `N`. -/
def cfzCarry
    {k N : ℕ} [NeZero N]
    (q : CFZFormIndex k) (x : CFZVariable k → ℕ) : ℤ :=
  (cfzAffineForm q).eval (fun v => (x v : ℤ)) / (N : ℤ)

/-- The standard representative of the cyclic form plus `N` times the
canonical carry is exactly the original integer affine evaluation. -/
theorem cfzAffineForm_eval_eq_val_add_mul_cfzCarry
    {k N : ℕ} [NeZero N]
    (q : CFZFormIndex k) (x : CFZVariable k → ℕ) :
    (cfzAffineForm q).eval (fun v => (x v : ℤ)) =
      (apLinearForm k N q.1 q.2
        (cubePointOfNat (N := N) x)).val +
        (N : ℤ) * cfzCarry (N := N) q x := by
  let A : ℤ :=
    (cfzAffineForm q).eval (fun v => (x v : ℤ))
  let a : ZMod N :=
    apLinearForm k N q.1 q.2
      (cubePointOfNat (N := N) x)
  have hcast : (A : ZMod N) = a := by
    exact intCast_cfzAffineForm_eval_eq_apLinearForm q x
  have hval : (a.val : ℤ) = A % (N : ℤ) := by
    calc
      (a.val : ℤ) = (((A : ZMod N).val : ℕ) : ℤ) := by
        exact_mod_cast congrArg ZMod.val hcast.symm
      _ = A % (N : ℤ) := ZMod.val_intCast A
  change A = (a.val : ℤ) + (N : ℤ) * (A / (N : ℤ))
  rw [hval]
  exact (Int.emod_add_mul_ediv A (N : ℤ)).symm

/-- Coarse but uniform bound for the integer CFZ affine evaluation on the
standard box.  It uses only the coefficient bound and the `2k` doubled
variables. -/
theorem natAbs_cfzAffineForm_eval_finiteBox_le
    {k N : ℕ}
    (q : CFZFormIndex k)
    (x : FiniteBox (fun _ : CFZVariable k => N)) :
    Int.natAbs
        ((cfzAffineForm q).eval
          (fun v => ((x v : ℕ) : ℤ))) ≤
      Fintype.card (CFZVariable k) * k * N := by
  simp only [AffineForm.eval, cfzAffineForm_constant,
    cfzAffineForm_coefficient, zero_add]
  calc
    Int.natAbs
        (∑ v, cfzCoefficient q v * ((x v : ℕ) : ℤ)) ≤
      ∑ v, Int.natAbs
        (cfzCoefficient q v * ((x v : ℕ) : ℤ)) := by
      simpa using Int.natAbs_sum_le
        (Finset.univ : Finset (CFZVariable k))
        (fun v => cfzCoefficient q v * ((x v : ℕ) : ℤ))
    _ ≤ ∑ _v : CFZVariable k, k * N := by
      apply Finset.sum_le_sum
      intro v _hv
      rw [Int.natAbs_mul, Int.natAbs_natCast]
      exact Nat.mul_le_mul
        (cfzCoefficient_natAbs_le q v)
        (Nat.le_of_lt (x v).isLt)
    _ = Fintype.card (CFZVariable k) * k * N := by
      simp [mul_assoc]

/-- Consequently the canonical carry on the standard box ranges over a
fixed finite interval depending only on `k`. -/
theorem natAbs_cfzCarry_finiteBox_le
    {k N : ℕ} [NeZero N]
    (q : CFZFormIndex k)
    (x : FiniteBox (fun _ : CFZVariable k => N)) :
    Int.natAbs
        (cfzCarry (N := N) q (fun v => (x v : ℕ))) ≤
      Fintype.card (CFZVariable k) * k + 1 := by
  let xNat : CFZVariable k → ℕ := fun v => (x v : ℕ)
  let A : ℤ :=
    (cfzAffineForm q).eval (fun v => (xNat v : ℤ))
  let a : ZMod N :=
    apLinearForm k N q.1 q.2
      (cubePointOfNat (N := N) xNat)
  let c : ℤ := cfzCarry (N := N) q xNat
  have hidentity : A = (a.val : ℤ) + (N : ℤ) * c := by
    exact cfzAffineForm_eval_eq_val_add_mul_cfzCarry q xNat
  have hdiff : A - (a.val : ℤ) = (N : ℤ) * c := by
    rw [hidentity]
    ring
  have habs :
      Int.natAbs (A - (a.val : ℤ)) =
        N * Int.natAbs c := by
    rw [hdiff, Int.natAbs_mul, Int.natAbs_natCast]
  have hA :
      Int.natAbs A ≤
        Fintype.card (CFZVariable k) * k * N := by
    exact natAbs_cfzAffineForm_eval_finiteBox_le q x
  have ha : a.val ≤ N := (ZMod.val_lt a).le
  have hdiffBound :
      Int.natAbs (A - (a.val : ℤ)) ≤
        N * (Fintype.card (CFZVariable k) * k + 1) := by
    calc
      Int.natAbs (A - (a.val : ℤ)) ≤
          Int.natAbs A + Int.natAbs (a.val : ℤ) :=
        Int.natAbs_sub_le _ _
      _ = Int.natAbs A + a.val := by
        rw [Int.natAbs_natCast]
      _ ≤ Fintype.card (CFZVariable k) * k * N + N :=
        Nat.add_le_add hA ha
      _ = N * (Fintype.card (CFZVariable k) * k + 1) := by
        ring
  apply Nat.le_of_mul_le_mul_left
    (show
      N * Int.natAbs c ≤
        N * (Fintype.card (CFZVariable k) * k + 1) by
      rw [← habs]
      exact hdiffBound)
    (NeZero.pos N)

/-- On an affine strip between two consecutive multiples of `N`, the
canonical carry is the strip index. -/
theorem cfzCarry_eq_of_mem_affineStrip
    {k N : ℕ} [NeZero N]
    (q : CFZFormIndex k) (x : CFZVariable k → ℕ)
    (c : ℤ)
    (hlower :
      (N : ℤ) * c ≤
        (cfzAffineForm q).eval (fun v => (x v : ℤ)))
    (hupper :
      (cfzAffineForm q).eval (fun v => (x v : ℤ)) <
        (N : ℤ) * (c + 1)) :
    cfzCarry (N := N) q x = c := by
  let A : ℤ :=
    (cfzAffineForm q).eval (fun v => (x v : ℤ))
  have hN : (N : ℤ) ≠ 0 := by
    exact_mod_cast NeZero.ne N
  have hNpos : (0 : ℤ) < N := by
    exact_mod_cast NeZero.pos N
  have hremainder_nonneg : 0 ≤ A - (N : ℤ) * c := by
    exact sub_nonneg.mpr hlower
  have hremainder_lt :
      A - (N : ℤ) * c < |(N : ℤ)| := by
    rw [abs_of_pos hNpos]
    calc
      A - (N : ℤ) * c <
          (N : ℤ) * (c + 1) - (N : ℤ) * c :=
        sub_lt_sub_right hupper _
      _ = N := by ring
  have hdiv :
      A / (N : ℤ) = c :=
    ((Int.ediv_emod_unique'' hN).2
      ⟨by ring, hremainder_nonneg, hremainder_lt⟩).1
  exact hdiv

/-- A finite block contained in one affine strip has constant CFZ carry. -/
theorem cfzCarry_eq_on_finset_of_affineStrip
    {k N : ℕ} [NeZero N]
    (q : CFZFormIndex k)
    (cell : Finset (CFZVariable k → ℕ))
    (c : ℤ)
    (hstrip : ∀ x ∈ cell,
      (N : ℤ) * c ≤
          (cfzAffineForm q).eval (fun v => (x v : ℤ)) ∧
        (cfzAffineForm q).eval (fun v => (x v : ℤ)) <
          (N : ℤ) * (c + 1)) :
    ∀ x ∈ cell, cfzCarry (N := N) q x = c := by
  intro x hx
  exact cfzCarry_eq_of_mem_affineStrip (N := N) q x c
    (hstrip x hx).1 (hstrip x hx).2

/-- Coordinatewise affine-strip containment supplies an
`IsCFZCarryCell` certificate for a finite family. -/
theorem isCFZCarryCell_of_affineStrips
    {κ : Type*} [Fintype κ]
    {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (cell : Finset (CFZVariable k → ℕ))
    (hstrip : ∀ x ∈ cell, ∀ q,
      (N : ℤ) * carry q ≤
          (cfzAffineForm (forms q)).eval
            (fun v => (x v : ℤ)) ∧
        (cfzAffineForm (forms q)).eval
            (fun v => (x v : ℤ)) <
          (N : ℤ) * (carry q + 1)) :
    IsCFZCarryCell (N := N) forms carry cell := by
  intro x hx q
  rw [cfzAffineForm_eval_eq_val_add_mul_cfzCarry (N := N)]
  rw [cfzCarry_eq_of_mem_affineStrip
    (N := N) (forms q) x (carry q)
    (hstrip x hx q).1 (hstrip x hx q).2]
  rfl

/-- Under `D ∣ W*N`, the cyclic W-tricked representative is congruent
modulo `D` to the ordinary integer W-tricked affine form on the same natural
coordinate representatives. -/
theorem natCast_cfzWTrickedLinearValue_eq_evalZMod_of_dvd
    {k N D : ℕ} [NeZero N]
    (W b : ℕ) (hD : D ∣ W * N)
    (q : CFZFormIndex k) (x : CFZVariable k → ℕ) :
    (cfzWTrickedLinearValue W b q
        (cubePointOfNat (N := N) x) : ZMod D) =
      (wTrickedAffineForm W b (cfzAffineForm q)).evalZMod D
        (fun v => (x v : ZMod D)) := by
  rw [wTrickedAffineForm_evalZMod]
  unfold cfzWTrickedLinearValue wTrickedValue
  push_cast
  have hweighted := weighted_val_cast_eq_intCast_of_dvd hD
      (apLinearForm k N q.1 q.2
        (cubePointOfNat (N := N) x))
      ((cfzAffineForm q).eval (fun v => (x v : ℤ)))
      (intCast_cfzAffineForm_eval_eq_apLinearForm q x)
  have hweighted' :
      (W : ZMod D) *
          ((apLinearForm k N q.1 q.2
            (cubePointOfNat (N := N) x)).val : ZMod D) =
        (W : ZMod D) *
          (((cfzAffineForm q).eval
            (fun v => (x v : ℤ)) : ℤ) : ZMod D) := by
    simpa only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast] using hweighted
  rw [hweighted']
  rw [AffineForm.intCast_eval_eq_evalZMod]
  simp only [Int.cast_natCast]

/-! ## Divisibility indicators modulo a common multiple -/

/-- Congruent natural numbers modulo a multiple of `d` have the same
divisibility indicator at `d`. -/
theorem natDivisibilityIndicator_eq_of_cast_eq_of_dvd
    {d D a b : ℕ} (hdD : d ∣ D)
    (hab : (a : ZMod D) = (b : ZMod D)) :
    natDivisibilityIndicator d a =
      natDivisibilityIndicator d b := by
  have habD : a ≡ b [MOD D] :=
    (ZMod.natCast_eq_natCast_iff a b D).mp hab
  have habd : a ≡ b [MOD d] := habD.of_dvd hdD
  unfold natDivisibilityIndicator
  have hiff : d ∣ a ↔ d ∣ b := by
    rw [← Nat.modEq_zero_iff_dvd, ← Nat.modEq_zero_iff_dvd]
    exact ⟨fun ha => habd.symm.trans ha,
      fun hb => habd.trans hb⟩
  simp only [hiff]

/-- Each left divisor in a paired family divides the global paired LCM. -/
theorem pairedDivisor_left_dvd_lcm
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (z : κ → ℕ × ℕ) (q : κ) :
    (z q).1 ∣ pairedDivisorLcm z := by
  unfold pairedDivisorLcm
  exact Finset.dvd_lcm
    (f := Sum.elim (fun i => (z i).1) (fun i => (z i).2))
    (Finset.mem_univ (Sum.inl q))

/-- Each right divisor in a paired family divides the global paired LCM. -/
theorem pairedDivisor_right_dvd_lcm
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (z : κ → ℕ × ℕ) (q : κ) :
    (z q).2 ∣ pairedDivisorLcm z := by
  unfold pairedDivisorLcm
  exact Finset.dvd_lcm
    (f := Sum.elim (fun i => (z i).1) (fun i => (z i).2))
    (Finset.mem_univ (Sum.inr q))

/-! ## Exact finite-box and residue-vector reindexing -/

/-- `boxMean` is the ordinary normalized mean on its typed finite box. -/
theorem boxMean_eq_mean_finiteBox
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (side : ι → ℕ) (F : (ι → ℕ) → ℝ) :
    boxMean side F =
      mean (fun x : FiniteBox side => F (fun i => x i)) := by
  rw [boxMean, boxSum, mean, Fintype.expect_eq_sum_div_card,
    card_finiteBox]
  simp only [Nat.cast_prod]

/-- Standard representatives give an explicit equivalence between a typed
natural residue box and a vector over `ZMod D`. -/
def finiteBoxEquivZModVector
    {ι : Type*} (D : ℕ) [NeZero D] :
    FiniteBox (fun _ : ι => D) ≃ (ι → ZMod D) where
  toFun x i := (x i : ℕ)
  invFun x i := ⟨(x i).val, (x i).val_lt⟩
  left_inv x := by
    funext i
    apply Fin.ext
    exact ZMod.val_natCast_of_lt (x i).isLt
  right_inv x := by
    funext i
    exact ZMod.natCast_zmod_val (x i)

@[simp]
theorem finiteBoxEquivZModVector_apply
    {ι : Type*} (D : ℕ) [NeZero D]
    (x : FiniteBox (fun _ : ι => D)) (i : ι) :
    finiteBoxEquivZModVector D x i = (x i : ℕ) :=
  rfl

@[simp]
theorem finiteBoxEquivZModVector_symm_apply_val
    {ι : Type*} (D : ℕ) [NeZero D]
    (x : ι → ZMod D) (i : ι) :
    ((finiteBoxEquivZModVector D).symm x i : ℕ) =
      (x i).val :=
  rfl

/-- The exact residue-box mean can be reindexed by standard `ZMod`
representatives. -/
theorem meanMod_eq_mean_zmodVector
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ℕ) [NeZero D] (F : (ι → ℕ) → ℝ) :
    meanMod D F =
      mean (fun x : ι → ZMod D => F (fun i => (x i).val)) := by
  rw [meanMod, boxMean_eq_mean_finiteBox]
  unfold mean
  apply Fintype.expect_equiv (finiteBoxEquivZModVector D)
  intro x
  congr 1
  funext i
  exact (ZMod.val_natCast_of_lt (x i).isLt).symm

/-! ## Reindexing the cyclic CFZ cube -/

/-- Standard coordinate representatives identify the natural box of side
`N` with the doubled cyclic CFZ cube. -/
def finiteBoxEquivCubePoint
    (k N : ℕ) [NeZero N] :
    FiniteBox (fun _ : CFZVariable k => N) ≃ CubePoint k N where
  toFun x i b := (x (i, b) : ℕ)
  invFun x v := ⟨(x v.1 v.2).val, (x v.1 v.2).val_lt⟩
  left_inv x := by
    funext v
    apply Fin.ext
    exact ZMod.val_natCast_of_lt (x v).isLt
  right_inv x := by
    funext i b
    exact ZMod.natCast_zmod_val (x i b)

@[simp]
theorem finiteBoxEquivCubePoint_apply
    (k N : ℕ) [NeZero N]
    (x : FiniteBox (fun _ : CFZVariable k => N))
    (i : Fin k) (b : Bool) :
    finiteBoxEquivCubePoint k N x i b =
      (x (i, b) : ℕ) :=
  rfl

/-- A mean on the cyclic CFZ cube is exactly the natural-box mean of its
standard-representative pullback. -/
theorem mean_cubePoint_eq_boxMean
    {k N : ℕ} [NeZero N]
    (F : CubePoint k N → ℝ) :
    mean F =
      boxMean (fun _ : CFZVariable k => N)
        (fun x => F (cubePointOfNat (N := N) x)) := by
  rw [boxMean_eq_mean_finiteBox]
  symm
  unfold mean
  apply Fintype.expect_equiv (finiteBoxEquivCubePoint k N)
  intro x
  rfl

/-! ## CFZ periodicity under lift compatibility -/

/-- Coordinatewise congruent natural representatives give congruent cyclic
W-tricked CFZ values modulo `D` when `D ∣ W*N`. -/
theorem natCast_cfzWTrickedLinearValue_eq_of_coordinate_modEq
    {k N D : ℕ} [NeZero N]
    (W b : ℕ) (hD : D ∣ W * N)
    (q : CFZFormIndex k) (x y : CFZVariable k → ℕ)
    (hxy : ∀ v, x v % D = y v % D) :
    (cfzWTrickedLinearValue W b q
        (cubePointOfNat (N := N) x) : ZMod D) =
      (cfzWTrickedLinearValue W b q
        (cubePointOfNat (N := N) y) : ZMod D) := by
  have hxyZ :
      (fun v : CFZVariable k => (x v : ZMod D)) =
        fun v => (y v : ZMod D) := by
    funext v
    exact (ZMod.natCast_eq_natCast_iff' (x v) (y v) D).2 (hxy v)
  calc
    (cfzWTrickedLinearValue W b q
        (cubePointOfNat (N := N) x) : ZMod D) =
        (wTrickedAffineForm W b (cfzAffineForm q)).evalZMod D
          (fun v => (x v : ZMod D)) :=
      natCast_cfzWTrickedLinearValue_eq_evalZMod_of_dvd
        W b hD q x
    _ = (wTrickedAffineForm W b (cfzAffineForm q)).evalZMod D
          (fun v => (y v : ZMod D)) := by rw [hxyZ]
    _ = (cfzWTrickedLinearValue W b q
        (cubePointOfNat (N := N) y) : ZMod D) :=
      (natCast_cfzWTrickedLinearValue_eq_evalZMod_of_dvd
        W b hD q y).symm

/-- The paired CFZ divisor indicator is genuinely periodic modulo its global
paired LCM under the exact lift-compatibility hypothesis. -/
theorem periodicInEachCoordinate_pairedDivisibilityIndicator_cfz_of_dvd
    {k N : ℕ} [NeZero N]
    (W b : ℕ)
    (z : CFZFormIndex k → ℕ × ℕ)
    (hD : pairedDivisorLcm z ∣ W * N) :
    PeriodicInEachCoordinate
      (fun x : CFZVariable k → ℕ =>
        pairedDivisibilityIndicator
          (fun q y =>
            cfzWTrickedLinearValue W b q
              (cubePointOfNat (N := N) y))
          z x)
      (pairedDivisorLcm z) := by
  intro x y hxy
  unfold pairedDivisibilityIndicator
  apply Finset.prod_congr rfl
  intro q _hq
  have hvalue :=
    natCast_cfzWTrickedLinearValue_eq_of_coordinate_modEq
      W b hD q x y hxy
  rw [natDivisibilityIndicator_eq_of_cast_eq_of_dvd
      (pairedDivisor_left_dvd_lcm z q) hvalue,
    natDivisibilityIndicator_eq_of_cast_eq_of_dvd
      (pairedDivisor_right_dvd_lcm z q) hvalue]

/-- Arbitrary finite-subfamily form of CFZ periodicity.  This is the version
used for Boolean-selected subfamilies in the linear-forms condition. -/
theorem periodicInEachCoordinate_pairedDivisibilityIndicator_cfzFamily_of_dvd
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b : ℕ) (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ)
    (hD : pairedDivisorLcm z ∣ W * N) :
    PeriodicInEachCoordinate
      (fun x : CFZVariable k → ℕ =>
        pairedDivisibilityIndicator
          (fun q y =>
            cfzWTrickedLinearValue W b (forms q)
              (cubePointOfNat (N := N) y))
          z x)
      (pairedDivisorLcm z) := by
  intro x y hxy
  unfold pairedDivisibilityIndicator
  apply Finset.prod_congr rfl
  intro q _hq
  have hvalue :=
    natCast_cfzWTrickedLinearValue_eq_of_coordinate_modEq
      W b hD (forms q) x y hxy
  rw [natDivisibilityIndicator_eq_of_cast_eq_of_dvd
      (pairedDivisor_left_dvd_lcm z q) hvalue,
    natDivisibilityIndicator_eq_of_cast_eq_of_dvd
      (pairedDivisor_right_dvd_lcm z q) hvalue]

/-! ## The exact affine residue model -/

/-- Natural representative of the W-tricked integer affine form evaluated
modulo `D`.  Its divisibility conditions at every divisor of `D` are exactly
the corresponding affine zero congruences. -/
def cfzWTrickedAffineResidueValue
    {k D : ℕ} [NeZero D]
    (W b : ℕ) (q : CFZFormIndex k)
    (x : CFZVariable k → ZMod D) : ℕ :=
  ((wTrickedAffineForm W b (cfzAffineForm q)).evalZMod D x).val

@[simp]
theorem natCast_cfzWTrickedAffineResidueValue
    {k D : ℕ} [NeZero D]
    (W b : ℕ) (q : CFZFormIndex k)
    (x : CFZVariable k → ZMod D) :
    (cfzWTrickedAffineResidueValue W b q x : ZMod D) =
      (wTrickedAffineForm W b (cfzAffineForm q)).evalZMod D x := by
  exact ZMod.natCast_zmod_val _

/-- Pointwise identification of the cyclic paired divisor indicator with
the exact affine residue model, under `D ∣ W*N`. -/
theorem pairedDivisibilityIndicator_cfz_eq_affineResidue_of_dvd
    {k N : ℕ} [NeZero N]
    (W b : ℕ)
    (z : CFZFormIndex k → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    (hD : pairedDivisorLcm z ∣ W * N)
    (x : CFZVariable k → ℕ) :
    pairedDivisibilityIndicator
        (fun q y =>
          cfzWTrickedLinearValue W b q
            (cubePointOfNat (N := N) y))
        z x =
      pairedDivisibilityIndicator
        (cfzWTrickedAffineResidueValue
          (D := pairedDivisorLcm z) W b)
        z (fun v => (x v : ZMod (pairedDivisorLcm z))) := by
  unfold pairedDivisibilityIndicator
  apply Finset.prod_congr rfl
  intro q _hq
  have hvalue :
      (cfzWTrickedLinearValue W b q
          (cubePointOfNat (N := N) x) :
            ZMod (pairedDivisorLcm z)) =
        (cfzWTrickedAffineResidueValue
          (D := pairedDivisorLcm z) W b q
          (fun v => (x v : ZMod (pairedDivisorLcm z))) :
            ZMod (pairedDivisorLcm z)) := by
    exact
      (natCast_cfzWTrickedLinearValue_eq_evalZMod_of_dvd
        W b hD q x).trans
        (natCast_cfzWTrickedAffineResidueValue
          W b q (fun v =>
            (x v : ZMod (pairedDivisorLcm z)))).symm
  rw [natDivisibilityIndicator_eq_of_cast_eq_of_dvd
      (pairedDivisor_left_dvd_lcm z q) hvalue,
    natDivisibilityIndicator_eq_of_cast_eq_of_dvd
      (pairedDivisor_right_dvd_lcm z q) hvalue]

/-- Pointwise affine-residue identification for an arbitrary finite CFZ
subfamily. -/
theorem pairedDivisibilityIndicator_cfzFamily_eq_affineResidue_of_dvd
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b : ℕ) (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    (hD : pairedDivisorLcm z ∣ W * N)
    (x : CFZVariable k → ℕ) :
    pairedDivisibilityIndicator
        (fun q y =>
          cfzWTrickedLinearValue W b (forms q)
            (cubePointOfNat (N := N) y))
        z x =
      pairedDivisibilityIndicator
        (fun q =>
          cfzWTrickedAffineResidueValue
            (D := pairedDivisorLcm z) W b (forms q))
        z (fun v => (x v : ZMod (pairedDivisorLcm z))) := by
  unfold pairedDivisibilityIndicator
  apply Finset.prod_congr rfl
  intro q _hq
  have hvalue :
      (cfzWTrickedLinearValue W b (forms q)
          (cubePointOfNat (N := N) x) :
            ZMod (pairedDivisorLcm z)) =
        (cfzWTrickedAffineResidueValue
          (D := pairedDivisorLcm z) W b (forms q)
          (fun v => (x v : ZMod (pairedDivisorLcm z))) :
            ZMod (pairedDivisorLcm z)) := by
    exact
      (natCast_cfzWTrickedLinearValue_eq_evalZMod_of_dvd
        W b hD (forms q) x).trans
        (natCast_cfzWTrickedAffineResidueValue
          W b (forms q) (fun v =>
            (x v : ZMod (pairedDivisorLcm z)))).symm
  rw [natDivisibilityIndicator_eq_of_cast_eq_of_dvd
      (pairedDivisor_left_dvd_lcm z q) hvalue,
    natDivisibilityIndicator_eq_of_cast_eq_of_dvd
      (pairedDivisor_right_dvd_lcm z q) hvalue]

/-- The exact residue-class mean of the natural cyclic indicator is the
paired affine divisibility density modulo its common LCM. -/
theorem meanMod_pairedDivisibilityIndicator_cfz_eq_affineResidueDensity
    {k N : ℕ} [NeZero N]
    (W b : ℕ)
    (z : CFZFormIndex k → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    (hD : pairedDivisorLcm z ∣ W * N) :
    meanMod (pairedDivisorLcm z)
        (fun x : CFZVariable k → ℕ =>
          pairedDivisibilityIndicator
            (fun q y =>
              cfzWTrickedLinearValue W b q
                (cubePointOfNat (N := N) y))
            z x) =
      pairedDivisibilityDensity
        (cfzWTrickedAffineResidueValue
          (D := pairedDivisorLcm z) W b)
        z := by
  rw [meanMod_eq_mean_zmodVector]
  unfold pairedDivisibilityDensity
  congr 1
  funext x
  have hpoint :=
    pairedDivisibilityIndicator_cfz_eq_affineResidue_of_dvd
      W b z hD (fun v => (x v).val)
  simpa only [ZMod.natCast_zmod_val] using hpoint

/-- Exact residue-density identification for an arbitrary finite CFZ
subfamily. -/
theorem meanMod_pairedDivisibilityIndicator_cfzFamily_eq_affineResidueDensity
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b : ℕ) (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    (hD : pairedDivisorLcm z ∣ W * N) :
    meanMod (pairedDivisorLcm z)
        (fun x : CFZVariable k → ℕ =>
          pairedDivisibilityIndicator
            (fun q y =>
              cfzWTrickedLinearValue W b (forms q)
                (cubePointOfNat (N := N) y))
            z x) =
      pairedDivisibilityDensity
        (fun q =>
          cfzWTrickedAffineResidueValue
            (D := pairedDivisorLcm z) W b (forms q))
        z := by
  rw [meanMod_eq_mean_zmodVector]
  unfold pairedDivisibilityDensity
  congr 1
  funext x
  have hpoint :=
    pairedDivisibilityIndicator_cfzFamily_eq_affineResidue_of_dvd
      W b forms z hD (fun v => (x v).val)
  simpa only [ZMod.natCast_zmod_val] using hpoint

/-! ## Normalized trimming loss -/

/-- An elementary normalization inequality used to pass from a sum boundary
estimate to a mean boundary estimate. -/
theorem abs_div_sub_div_le_two_mul_boundary
    {S T V U E B : ℝ}
    (hV : 0 < V) (hU : 0 < U)
    (hE : 0 ≤ E)
    (hVU : V - U = E)
    (hST : |S - T| ≤ E * B)
    (hT : |T / U| ≤ B) :
    |S / V - T / U| ≤ 2 * E * B / V := by
  have hdecomp :
      S / V - T / U =
        (S - T) / V + (T / U) * (U / V - 1) := by
    field_simp
    ring
  have hscale : |U / V - 1| = E / V := by
    have heq : U / V - 1 = -E / V := by
      rw [← hVU]
      field_simp
      ring
    rw [heq, abs_div, abs_neg, abs_of_nonneg hE, abs_of_pos hV]
  rw [hdecomp]
  calc
    |(S - T) / V + (T / U) * (U / V - 1)| ≤
        |(S - T) / V| + |(T / U) * (U / V - 1)| :=
      abs_add_le _ _
    _ = |S - T| / V + |T / U| * (E / V) := by
      rw [abs_div, abs_of_pos hV, abs_mul, hscale]
    _ ≤ (E * B) / V + B * (E / V) := by
      gcongr
    _ = 2 * E * B / V := by ring

/-- A globally bounded function has a bounded exact residue-class mean. -/
theorem abs_meanMod_le_of_abs_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {D : ℕ} (hD : 0 < D)
    (F : (ι → ℕ) → ℝ) (B : ℝ)
    (hF : ∀ x, |F x| ≤ B) :
    |meanMod D F| ≤ B := by
  let : NeZero D := ⟨hD.ne'⟩
  rw [meanMod_eq_mean_zmodVector]
  apply abs_le.mpr
  constructor
  · exact const_le_mean fun x => neg_le_of_abs_le (hF fun i => (x i).val)
  · exact mean_le_of_le_const fun x => le_of_abs_le (hF fun i => (x i).val)

/-- **Normalized periodic box boundary estimate.**

If every side contains at least one complete period, the box mean differs
from the exact residue mean by at most twice the relative number of points
removed by coordinatewise trimming, times the global pointwise bound. -/
theorem abs_boxMean_sub_meanMod_le_boundary
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ℕ) (side : ι → ℕ)
    (F : (ι → ℕ) → ℝ) (B : ℝ)
    (hD : 0 < D) (hside : ∀ i, D ≤ side i)
    (hperiodic : PeriodicInEachCoordinate F D)
    (hbound : ∀ x, |F x| ≤ B) :
    |boxMean side F - meanMod D F| ≤
      2 *
        (((∏ i, side i) -
          ∏ i, trimToMultiple D (side i) : ℕ) : ℝ) *
        B /
        ∏ i, (side i : ℝ) := by
  have hsidepos : ∀ i, 0 < side i :=
    fun i => hD.trans_le (hside i)
  have htrimpos : ∀ i, 0 < trimmedSide D side i := by
    intro i
    change 0 < side i / D * D
    exact Nat.mul_pos (Nat.div_pos (hside i) hD) hD
  have htrimdvd : ∀ i, D ∣ trimmedSide D side i :=
    fun i => trimToMultiple_dvd D (side i)
  have hmeantrim :
      boxMean (trimmedSide D side) F = meanMod D F :=
    boxMean_periodic_of_dvd
      (trimmedSide D side) D F htrimdvd htrimpos hD hperiodic
  have hprodle :
      (∏ i, trimmedSide D side i) ≤ ∏ i, side i := by
    apply Finset.prod_le_prod
    · intro i _hi
      exact Nat.zero_le _
    · intro i _hi
      exact trimmedSide_le D side i
  have hvolume :
      (∏ i, (side i : ℝ)) -
          ∏ i, (trimmedSide D side i : ℝ) =
        (((∏ i, side i) -
          ∏ i, trimmedSide D side i : ℕ) : ℝ) := by
    rw [← Nat.cast_prod, ← Nat.cast_prod, Nat.cast_sub hprodle]
  have hsum :
      |boxSum side F - boxSum (trimmedSide D side) F| ≤
        (((∏ i, side i) -
          ∏ i, trimmedSide D side i : ℕ) : ℝ) * B :=
    abs_boxSum_sub_trimmed_le_explicit D side F B
      (fun x _hx => hbound x)
  have hV : 0 < ∏ i, (side i : ℝ) := by
    apply Finset.prod_pos
    intro i _hi
    exact_mod_cast hsidepos i
  have hU : 0 < ∏ i, (trimmedSide D side i : ℝ) := by
    apply Finset.prod_pos
    intro i _hi
    exact_mod_cast htrimpos i
  have hE :
      0 ≤ (((∏ i, side i) -
        ∏ i, trimmedSide D side i : ℕ) : ℝ) := by
    positivity
  have htrimmean :
      |boxSum (trimmedSide D side) F /
          ∏ i, (trimmedSide D side i : ℝ)| ≤ B := by
    rw [← boxMean, hmeantrim]
    exact abs_meanMod_le_of_abs_le hD F B hbound
  have hnormalize :=
    abs_div_sub_div_le_two_mul_boundary
      hV hU hE hvolume hsum htrimmean
  change
    |boxMean side F - boxMean (trimmedSide D side) F| ≤
      2 *
        (((∏ i, side i) -
          ∏ i, trimmedSide D side i : ℕ) : ℝ) *
        B /
        ∏ i, (side i : ℝ) at hnormalize
  rw [hmeantrim] at hnormalize
  simpa [trimmedSide] using hnormalize

/-! ## Paired divisibility specialization -/

/-- Every paired divisibility indicator is a zero--one valued function. -/
theorem abs_pairedDivisibilityIndicator_le_one
    {κ X : Type*} [Fintype κ]
    (values : κ → X → ℕ)
    (z : κ → ℕ × ℕ) (x : X) :
    |pairedDivisibilityIndicator values z x| ≤ 1 := by
  have hnonneg :
      0 ≤ pairedDivisibilityIndicator values z x := by
    unfold pairedDivisibilityIndicator natDivisibilityIndicator
    positivity
  rw [abs_of_nonneg hnonneg]
  unfold pairedDivisibilityIndicator
  apply Finset.prod_le_one
  · intro q _hq
    unfold natDivisibilityIndicator
    positivity
  · intro q _hq
    unfold natDivisibilityIndicator
    split_ifs <;> norm_num

/-- **Finite cyclic CFZ density versus exact affine residue density.**

For any finite CFZ subfamily and any supported paired divisor choice, assume
the common LCM is lift-compatible (`D ∣ W*N`) and the box is long enough
(`R^(2*card κ) ≤ N`).  The actual cyclic `CubePoint k N` density then differs
from the exact affine density modulo `D` only by the explicit coordinatewise
trimming boundary.

The power hypothesis is used through
`pairedDivisorLcm_le_pow`, so this statement exposes exactly the
`D ≤ R^(2m)` input produced by the Selberg expansion. -/
theorem abs_pairedDivisibilityDensity_cfzFamily_sub_affineResidueDensity_le_boundary
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N R : ℕ} [NeZero N]
    (W b : ℕ) (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    (hz : z ∈ smoothDivisorFamilyChoices κ R)
    (hcompat : pairedDivisorLcm z ∣ W * N)
    (hlong : R ^ (2 * Fintype.card κ) ≤ N) :
    |pairedDivisibilityDensity
        (fun q (x : CubePoint k N) =>
          cfzWTrickedLinearValue W b (forms q) x)
        z -
      pairedDivisibilityDensity
        (fun q =>
          cfzWTrickedAffineResidueValue
            (D := pairedDivisorLcm z) W b (forms q))
        z| ≤
      2 *
        (((∏ _v : CFZVariable k, N) -
          ∏ _v : CFZVariable k,
            trimToMultiple (pairedDivisorLcm z) N : ℕ) : ℝ) /
        ∏ _v : CFZVariable k, (N : ℝ) := by
  have hDpos : 0 < pairedDivisorLcm z :=
    pairedDivisorLcm_pos hz
  have hDle : pairedDivisorLcm z ≤ N :=
    (pairedDivisorLcm_le_pow hz).trans hlong
  let F : (CFZVariable k → ℕ) → ℝ :=
    fun x =>
      pairedDivisibilityIndicator
        (fun q y =>
          cfzWTrickedLinearValue W b (forms q)
            (cubePointOfNat (N := N) y))
        z x
  have hperiodic : PeriodicInEachCoordinate F (pairedDivisorLcm z) :=
    periodicInEachCoordinate_pairedDivisibilityIndicator_cfzFamily_of_dvd
      W b forms z hcompat
  have hbound : ∀ x, |F x| ≤ (1 : ℝ) :=
    fun x =>
      abs_pairedDivisibilityIndicator_le_one
        (fun q y =>
          cfzWTrickedLinearValue W b (forms q)
            (cubePointOfNat (N := N) y))
        z x
  have hboundary :=
    abs_boxMean_sub_meanMod_le_boundary
      (pairedDivisorLcm z)
      (fun _ : CFZVariable k => N) F 1
      hDpos (fun _ => hDle) hperiodic hbound
  have hresidue :
      meanMod (pairedDivisorLcm z) F =
        pairedDivisibilityDensity
          (fun q =>
            cfzWTrickedAffineResidueValue
              (D := pairedDivisorLcm z) W b (forms q))
          z := by
    exact
      meanMod_pairedDivisibilityIndicator_cfzFamily_eq_affineResidueDensity
        W b forms z hcompat
  have hcube :
      pairedDivisibilityDensity
          (fun q (x : CubePoint k N) =>
            cfzWTrickedLinearValue W b (forms q) x)
          z =
        boxMean (fun _ : CFZVariable k => N) F := by
    unfold pairedDivisibilityDensity
    exact mean_cubePoint_eq_boxMean
      (pairedDivisibilityIndicator
        (fun q (x : CubePoint k N) =>
          cfzWTrickedLinearValue W b (forms q) x)
        z)
  rw [hresidue] at hboundary
  rw [hcube]
  simpa [F] using hboundary

/-- The exact boundary cardinality of a constant-side box is at most
`D * t * N^(t-1)`. -/
theorem cast_pow_sub_trimToMultiple_pow_le
    {D N t : ℕ} (hD : 0 < D) :
    (((N ^ t - (trimToMultiple D N) ^ t : ℕ) : ℝ)) ≤
      (D : ℝ) * (t : ℝ) * (N : ℝ) ^ (t - 1) := by
  have htrimle : trimToMultiple D N ≤ N :=
    trimToMultiple_le D N
  have hpowle :
      (trimToMultiple D N) ^ t ≤ N ^ t :=
    Nat.pow_le_pow_left htrimle t
  have hdiff :
      N - trimToMultiple D N ≤ D :=
    (trimToMultiple_boundary_lt (L := N) hD).le
  have hcastdiff :
      (N : ℝ) - (trimToMultiple D N : ℝ) =
        ((N - trimToMultiple D N : ℕ) : ℝ) := by
    rw [Nat.cast_sub htrimle]
  have hnonneg :
      0 ≤ (N : ℝ) ^ t -
        (trimToMultiple D N : ℝ) ^ t := by
    exact sub_nonneg.mpr (pow_le_pow_left₀
      (by positivity) (by exact_mod_cast htrimle) t)
  calc
    (((N ^ t - (trimToMultiple D N) ^ t : ℕ) : ℝ)) =
        (N : ℝ) ^ t -
          (trimToMultiple D N : ℝ) ^ t := by
      rw [Nat.cast_sub hpowle]
      norm_num only [Nat.cast_pow]
    _ = |(N : ℝ) ^ t -
          (trimToMultiple D N : ℝ) ^ t| :=
      (abs_of_nonneg hnonneg).symm
    _ ≤ |(N : ℝ) - (trimToMultiple D N : ℝ)| *
          (t : ℝ) *
          max |(N : ℝ)| |(trimToMultiple D N : ℝ)| ^ (t - 1) :=
      abs_pow_sub_pow_le (N : ℝ) (trimToMultiple D N : ℝ) t
    _ = ((N - trimToMultiple D N : ℕ) : ℝ) *
          (t : ℝ) * (N : ℝ) ^ (t - 1) := by
      rw [hcastdiff, abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (Nat.cast_nonneg _),
        max_eq_left (by exact_mod_cast htrimle)]
    _ ≤ (D : ℝ) * (t : ℝ) * (N : ℝ) ^ (t - 1) := by
      gcongr

/-- Power-form boundary estimate obtained by combining the exact theorem
with `D ≤ R^(2*card κ)`.  This is the form directly suited to the support
bound in the `2m`-divisor Selberg expansion. -/
theorem abs_pairedDivisibilityDensity_cfzFamily_sub_affineResidueDensity_le_pow
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N R : ℕ} [NeZero N]
    (W b : ℕ) (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    (hz : z ∈ smoothDivisorFamilyChoices κ R)
    (hcompat : pairedDivisorLcm z ∣ W * N)
    (hlong : R ^ (2 * Fintype.card κ) ≤ N) :
    |pairedDivisibilityDensity
        (fun q (x : CubePoint k N) =>
          cfzWTrickedLinearValue W b (forms q) x)
        z -
      pairedDivisibilityDensity
        (fun q =>
          cfzWTrickedAffineResidueValue
            (D := pairedDivisorLcm z) W b (forms q))
        z| ≤
      2 *
        ((R ^ (2 * Fintype.card κ) : ℕ) : ℝ) *
        (Fintype.card (CFZVariable k) : ℝ) *
        (N : ℝ) ^ (Fintype.card (CFZVariable k) - 1) /
        (N : ℝ) ^ Fintype.card (CFZVariable k) := by
  have hbase :=
    abs_pairedDivisibilityDensity_cfzFamily_sub_affineResidueDensity_le_boundary
      W b forms z hz hcompat hlong
  have hboundary :=
    cast_pow_sub_trimToMultiple_pow_le
      (pairedDivisorLcm_pos hz)
      (N := N) (t := Fintype.card (CFZVariable k))
  have hDlcm :
      pairedDivisorLcm z ≤ R ^ (2 * Fintype.card κ) :=
    pairedDivisorLcm_le_pow hz
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast NeZero.pos N
  calc
    |pairedDivisibilityDensity
        (fun q (x : CubePoint k N) =>
          cfzWTrickedLinearValue W b (forms q) x)
        z -
      pairedDivisibilityDensity
        (fun q =>
          cfzWTrickedAffineResidueValue
            (D := pairedDivisorLcm z) W b (forms q))
        z| ≤
        2 *
          (((N ^ Fintype.card (CFZVariable k) -
            (trimToMultiple (pairedDivisorLcm z) N) ^
              Fintype.card (CFZVariable k) : ℕ) : ℝ)) /
          (N : ℝ) ^ Fintype.card (CFZVariable k) := by
      simpa only [Finset.prod_const, Finset.card_univ] using hbase
    _ ≤ 2 *
          ((pairedDivisorLcm z : ℕ) : ℝ) *
          (Fintype.card (CFZVariable k) : ℝ) *
          (N : ℝ) ^ (Fintype.card (CFZVariable k) - 1) /
          (N : ℝ) ^ Fintype.card (CFZVariable k) := by
      apply div_le_div_of_nonneg_right _ (le_of_lt (pow_pos hNpos _))
      have htwo : (0 : ℝ) ≤ 2 := by norm_num
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hboundary htwo
    _ ≤ 2 *
          ((R ^ (2 * Fintype.card κ) : ℕ) : ℝ) *
          (Fintype.card (CFZVariable k) : ℝ) *
          (N : ℝ) ^ (Fintype.card (CFZVariable k) - 1) /
          (N : ℝ) ^ Fintype.card (CFZVariable k) := by
      gcongr

end Wikipedia.SzemeredisTheorem
