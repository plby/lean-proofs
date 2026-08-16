import Wikipedia.GreenTao.Sieve.CFZCarryBlockBoundary

/-!
# Canonical carry-cell partition independent of divisor choices

The quotient-block argument used so far chooses its block side from the
paired divisor LCM.  Consequently its frozen affine family varies with the
divisor choice, which obstructs a direct comparison with one unrestricted
Euler series.

There is also a divisor-independent decomposition: partition the standard
natural box by the complete vector of canonical CFZ carries.  The carry
range is bounded solely in terms of `k`, so a fixed finite product of
integer intervals contains every realized vector.  Each fiber is a genuine
simultaneous `IsCFZCarryCell`, the fibers are pairwise disjoint, and their
union is the whole box.

This file establishes that exact combinatorial reorganization.  The next
analytic input for this route is a residue-class discrepancy estimate on
these rational polyhedral cells, uniform in the paired divisor modulus.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Carry vectors and their finite range -/

/-- The complete canonical carry vector of a finite selected CFZ family at
one natural point. -/
def cfzCanonicalCarryVector
    {κ : Type*} {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k)
    (x : CFZVariable k → ℕ) : κ → ℤ :=
  fun q => cfzCarry (N := N) (forms q) x

/-- All carry vectors in the uniform coordinatewise range.  The finset
depends only on `k` and the finite index type, not on `N`, the divisor
choice, or the affine constants. -/
noncomputable def cfzCanonicalCarryVectorChoices
    (κ : Type*) [Fintype κ] [DecidableEq κ]
    (k : ℕ) : Finset (κ → ℤ) :=
  Fintype.piFinset fun _q : κ =>
    Finset.Icc (-(cfzCarryRange k : ℤ))
      (cfzCarryRange k : ℤ)

/-- An integer whose natural absolute value is at most `C` lies in the
integer interval `[-C,C]`. -/
theorem mem_Icc_of_natAbs_le
    {c : ℤ} {C : ℕ} (hc : c.natAbs ≤ C) :
    c ∈ Finset.Icc (-(C : ℤ)) (C : ℤ) := by
  rw [Finset.mem_Icc]
  cases c with
  | ofNat n =>
      simp at hc ⊢
      omega
  | negSucc n =>
      simp at hc ⊢
      omega

/-- Every carry vector realized in the standard box belongs to the fixed
finite range. -/
theorem cfzCanonicalCarryVector_mem_choices
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k)
    {x : CFZVariable k → ℕ}
    (hx : x ∈ natBox (fun _ : CFZVariable k => N)) :
    cfzCanonicalCarryVector (N := N) forms x ∈
      cfzCanonicalCarryVectorChoices κ k := by
  apply Fintype.mem_piFinset.mpr
  intro q
  exact
    mem_Icc_of_natAbs_le
      (natAbs_cfzCarry_of_mem_natBox_le (N := N)
        (forms q) hx)

/-! ## The canonical cells -/

/-- The fiber of one complete carry vector inside the standard natural
box. -/
def cfzCanonicalCarryCell
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ) :
    Finset (CFZVariable k → ℕ) :=
  (natBox (fun _ : CFZVariable k => N)).filter
    fun x => cfzCanonicalCarryVector (N := N) forms x = carry

@[simp]
theorem mem_cfzCanonicalCarryCell
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (x : CFZVariable k → ℕ) :
    x ∈ cfzCanonicalCarryCell (N := N) forms carry ↔
      x ∈ natBox (fun _ : CFZVariable k => N) ∧
        cfzCanonicalCarryVector (N := N) forms x = carry := by
  simp [cfzCanonicalCarryCell]

/-- A point of the natural box belongs to its own carry-vector fiber. -/
theorem mem_cfzCanonicalCarryCell_self
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k)
    {x : CFZVariable k → ℕ}
    (hx : x ∈ natBox (fun _ : CFZVariable k => N)) :
    x ∈ cfzCanonicalCarryCell (N := N) forms
      (cfzCanonicalCarryVector (N := N) forms x) := by
  exact (mem_cfzCanonicalCarryCell (N := N) forms _ x).mpr
    ⟨hx, rfl⟩

/-- Distinct carry vectors have disjoint canonical cells. -/
theorem disjoint_cfzCanonicalCarryCell
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k)
    {carry₁ carry₂ : κ → ℤ}
    (hne : carry₁ ≠ carry₂) :
    Disjoint
      (cfzCanonicalCarryCell (N := N) forms carry₁)
      (cfzCanonicalCarryCell (N := N) forms carry₂) := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  have h₁ :=
    (mem_cfzCanonicalCarryCell (N := N) forms carry₁ x).mp hx₁
  have h₂ :=
    (mem_cfzCanonicalCarryCell (N := N) forms carry₂ x).mp hx₂
  exact hne (h₁.2.symm.trans h₂.2)

/-- Every canonical fiber is a simultaneous carry cell for the selected
family. -/
theorem isCFZCarryCell_cfzCanonicalCarryCell
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ) :
    IsCFZCarryCell (N := N) forms carry
      (cfzCanonicalCarryCell (N := N) forms carry) := by
  intro x hx q
  have hcarry :
      cfzCarry (N := N) (forms q) x = carry q := by
    have hvector :=
      (mem_cfzCanonicalCarryCell (N := N) forms carry x).mp hx |>.2
    exact congrFun hvector q
  rw [cfzAffineForm_eval_eq_val_add_mul_cfzCarry
    (N := N) (forms q) x, hcarry]
  rfl

/-! ## Exact partition identities -/

/-- The finite union of all allowed carry fibers is exactly the standard
natural box. -/
theorem biUnion_cfzCanonicalCarryCell_eq_natBox
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k) :
    (cfzCanonicalCarryVectorChoices κ k).biUnion
        (cfzCanonicalCarryCell (N := N) forms) =
      natBox (fun _ : CFZVariable k => N) := by
  ext x
  constructor
  · intro hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨carry, _hcarry, hxcell⟩ := hx
    exact
      (mem_cfzCanonicalCarryCell (N := N) forms carry x).mp hxcell |>.1
  · intro hx
    rw [Finset.mem_biUnion]
    exact
      ⟨cfzCanonicalCarryVector (N := N) forms x,
        cfzCanonicalCarryVector_mem_choices (N := N) forms hx,
        mem_cfzCanonicalCarryCell_self (N := N) forms hx⟩

/-- The family of canonical cells is pairwise disjoint on the finite carry
range. -/
theorem pairwise_disjoint_cfzCanonicalCarryCell
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k) :
    ((cfzCanonicalCarryVectorChoices κ k : Finset (κ → ℤ)) :
        Set (κ → ℤ)).Pairwise
      (fun carry₁ carry₂ =>
        Disjoint
          (cfzCanonicalCarryCell (N := N) forms carry₁)
          (cfzCanonicalCarryCell (N := N) forms carry₂)) := by
  intro carry₁ _hcarry₁ carry₂ _hcarry₂ hne
  exact disjoint_cfzCanonicalCarryCell (N := N) forms hne

/-- Every finite sum on the natural box decomposes exactly into the
divisor-independent canonical carry cells. -/
theorem sum_cfzCanonicalCarryCell_eq_sum_natBox
    {κ A : Type*} [Fintype κ] [DecidableEq κ]
    [AddCommMonoid A]
    {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k)
    (F : (CFZVariable k → ℕ) → A) :
    ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
        ∑ x ∈ cfzCanonicalCarryCell (N := N) forms carry,
          F x =
      ∑ x ∈ natBox (fun _ : CFZVariable k => N), F x := by
  rw [← biUnion_cfzCanonicalCarryCell_eq_natBox (N := N) forms]
  exact
    (Finset.sum_biUnion (M := A) (f := F)
      (pairwise_disjoint_cfzCanonicalCarryCell (N := N) forms)).symm

end Wikipedia.SzemeredisTheorem
