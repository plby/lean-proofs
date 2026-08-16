import Mathlib.Data.Int.Interval
import Wikipedia.GreenTao.Sieve.CFZCongruenceBoundary

/-!
# Carry-block boundaries for the cyclic CFZ lift

The standard representative of a CFZ form modulo `N` is not periodic in the
natural input coordinates.  This file gives the unconditional replacement
for the false periodicity step.

We divide the standard box into coordinatewise quotient blocks of side `D`.
On a block where every selected CFZ carry is constant, the cyclic lift is an
ordinary affine form with a carry-dependent constant.  A block on which one
carry changes must cross a hyperplane at an integral multiple of `N`.
Because CFZ coefficients are bounded and every CFZ form has a coefficient
equal to `1` or `-1`, the union of all such blocks has an explicit
codimension-one cardinality bound.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Coordinate quotient blocks -/

/-- Two natural vectors lie in the same coordinatewise quotient block of
side `D`. -/
def SameQuotientBlock {ι : Type*} (D : ℕ)
    (x y : ι → ℕ) : Prop :=
  ∀ i, x i / D = y i / D

theorem sameQuotientBlock_refl {ι : Type*} (D : ℕ)
    (x : ι → ℕ) :
    SameQuotientBlock D x x :=
  fun _ => rfl

theorem SameQuotientBlock.symm {ι : Type*} {D : ℕ}
    {x y : ι → ℕ} (hxy : SameQuotientBlock D x y) :
    SameQuotientBlock D y x :=
  fun i => (hxy i).symm

theorem SameQuotientBlock.trans {ι : Type*} {D : ℕ}
    {x y z : ι → ℕ}
    (hxy : SameQuotientBlock D x y)
    (hyz : SameQuotientBlock D y z) :
    SameQuotientBlock D x z :=
  fun i => (hxy i).trans (hyz i)

/-- The part of the standard `N`-box in the quotient block containing `x`. -/
noncomputable def quotientBlock {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (N D : ℕ) (x : ι → ℕ) : Finset (ι → ℕ) :=
  by
    classical
    exact
      (natBox (fun _ : ι => N)).filter
        (SameQuotientBlock D x)

@[simp]
theorem mem_quotientBlock {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {N D : ℕ} {x y : ι → ℕ} :
    y ∈ quotientBlock N D x ↔
      y ∈ natBox (fun _ : ι => N) ∧
        SameQuotientBlock D x y := by
  simp [quotientBlock]

theorem mem_quotientBlock_self {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {N D : ℕ} {x : ι → ℕ}
    (hx : x ∈ natBox (fun _ : ι => N)) :
    x ∈ quotientBlock N D x := by
  exact mem_quotientBlock.mpr
    ⟨hx, sameQuotientBlock_refl D x⟩

/-- Intersecting quotient blocks are equal.  Together with
`mem_quotientBlock_self`, this is the partition property used below. -/
theorem quotientBlock_eq_of_mem {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {N D : ℕ} {x y : ι → ℕ}
    (hy : y ∈ quotientBlock N D x) :
    quotientBlock N D y = quotientBlock N D x := by
  classical
  ext z
  rw [mem_quotientBlock, mem_quotientBlock]
  constructor
  · rintro ⟨hz, hyz⟩
    exact ⟨hz, (mem_quotientBlock.mp hy).2.trans hyz⟩
  · rintro ⟨hz, hxz⟩
    exact
      ⟨hz, (mem_quotientBlock.mp hy).2.symm.trans hxz⟩

/-- Coordinates in the same positive-side quotient block differ by less
than the block side. -/
theorem natAbs_natCast_sub_natCast_lt_of_sameQuotientBlock
    {ι : Type*} {D : ℕ} (hD : 0 < D)
    {x y : ι → ℕ} (hxy : SameQuotientBlock D x y)
    (i : ι) :
    Int.natAbs ((x i : ℤ) - (y i : ℤ)) < D := by
  have hdecomp :
      (x i : ℤ) - (y i : ℤ) =
        ((x i % D : ℕ) : ℤ) - ((y i % D : ℕ) : ℤ) := by
    have hx :
        x i = x i % D + D * (x i / D) := by
      exact (Nat.mod_add_div (x i) D).symm
    have hy :
        y i = y i % D + D * (y i / D) := by
      exact (Nat.mod_add_div (y i) D).symm
    have hxZ :
        (x i : ℤ) =
          ((x i % D : ℕ) : ℤ) +
            (D : ℤ) * ((x i / D : ℕ) : ℤ) := by
      exact_mod_cast hx
    have hyZ :
        (y i : ℤ) =
          ((y i % D : ℕ) : ℤ) +
            (D : ℤ) * ((y i / D : ℕ) : ℤ) := by
      exact_mod_cast hy
    rw [hxZ, hyZ, hxy i]
    ring
  rw [hdecomp]
  exact Int.natAbs_coe_sub_coe_lt_of_lt
    (Nat.mod_lt _ hD) (Nat.mod_lt _ hD)

/-! ## A generic unit-coefficient strip count -/

/-- Integer points in the standard box lying in a closed affine strip. -/
def affineStripInBox {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (N L : ℕ) (ψ : AffineForm ι ℤ) (a : ℤ) :
    Finset (ι → ℕ) :=
  (natBox (fun _ : ι => N)).filter fun x =>
    Int.natAbs
      (ψ.eval (fun i => (x i : ℤ)) - a) ≤ L

@[simp]
theorem mem_affineStripInBox {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {N L : ℕ} {ψ : AffineForm ι ℤ} {a : ℤ}
    {x : ι → ℕ} :
    x ∈ affineStripInBox N L ψ a ↔
      x ∈ natBox (fun _ : ι => N) ∧
        Int.natAbs
          (ψ.eval (fun i => (x i : ℤ)) - a) ≤ L := by
  simp [affineStripInBox]

/-- If an affine form has coefficient `1` or `-1` in coordinate `v`, its
value together with all other coordinates determines the point. -/
theorem eq_of_affine_eval_eq_of_eq_off_unit
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : AffineForm ι ℤ) (v : ι)
    (hunit :
      ψ.coefficient v = 1 ∨ ψ.coefficient v = -1)
    {x y : ι → ℕ}
    (heval :
      ψ.eval (fun i => (x i : ℤ)) =
        ψ.eval (fun i => (y i : ℤ)))
    (hoff : ∀ i, i ≠ v → x i = y i) :
    x = y := by
  funext i
  by_cases hiv : i = v
  · subst i
    simp only [AffineForm.eval] at heval
    have hoffsum :
        ∑ j ∈ (Finset.univ.erase v),
            ψ.coefficient j * (x j : ℤ) =
          ∑ j ∈ (Finset.univ.erase v),
            ψ.coefficient j * (y j : ℤ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hoff j (Finset.ne_of_mem_erase hj)]
    have hxsum :
        ∑ j, ψ.coefficient j * (x j : ℤ) =
          (∑ j ∈ (Finset.univ.erase v),
              ψ.coefficient j * (x j : ℤ)) +
            ψ.coefficient v * (x v : ℤ) := by
      symm
      exact Finset.sum_erase_add _ _
        (Finset.mem_univ v)
    have hysum :
        ∑ j, ψ.coefficient j * (y j : ℤ) =
          (∑ j ∈ (Finset.univ.erase v),
              ψ.coefficient j * (y j : ℤ)) +
            ψ.coefficient v * (y v : ℤ) := by
      symm
      exact Finset.sum_erase_add _ _
        (Finset.mem_univ v)
    rw [hxsum, hysum, hoffsum] at heval
    rcases hunit with hunit | hunit
    · rw [hunit] at heval
      norm_num at heval
      exact_mod_cast heval
    · rw [hunit] at heval
      norm_num at heval
      exact_mod_cast heval
  · exact hoff i hiv

/-- A unit-coefficient affine strip of half-width `L` contains at most
`(2L+1) N^(t-1)` points of an `N`-box. -/
theorem card_affineStripInBox_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N L : ℕ) (ψ : AffineForm ι ℤ) (a : ℤ)
    (v : ι)
    (hunit :
      ψ.coefficient v = 1 ∨ ψ.coefficient v = -1) :
    (affineStripInBox N L ψ a).card ≤
      (2 * L + 1) * N ^ (Fintype.card ι - 1) := by
  classical
  let target :
      Finset (({i : ι // i ≠ v} → ℕ) × ℤ) :=
    (natBox (fun _ : {i : ι // i ≠ v} => N)).product
      (Finset.Icc (-(L : ℤ)) (L : ℤ))
  let encode : (ι → ℕ) →
      (({i : ι // i ≠ v} → ℕ) × ℤ) :=
    fun x =>
      (fun i => x i.1,
        ψ.eval (fun i => (x i : ℤ)) - a)
  have hmaps :
      Set.MapsTo encode
        (affineStripInBox N L ψ a : Set (ι → ℕ))
        (target : Set (({i : ι // i ≠ v} → ℕ) × ℤ)) := by
    intro x hx
    have hx' := mem_affineStripInBox.mp hx
    have habsZ :
        |ψ.eval (fun i => (x i : ℤ)) - a| ≤ (L : ℤ) := by
      have hcast :
          (Int.natAbs
              (ψ.eval (fun i => (x i : ℤ)) - a) : ℤ) ≤
            (L : ℤ) := by
        exact_mod_cast hx'.2
      simpa only [Int.natCast_natAbs] using hcast
    change encode x ∈ target
    apply Finset.mem_product.mpr
    dsimp only [encode]
    constructor
    · rw [mem_natBox]
      intro i
      exact mem_natBox.mp hx'.1 i.1
    · simpa only [Finset.mem_Icc] using (abs_le.mp habsZ)
  have hinj :
      Set.InjOn encode
        (affineStripInBox N L ψ a : Set (ι → ℕ)) := by
    intro x _hx y _hy hencode
    apply eq_of_affine_eval_eq_of_eq_off_unit ψ v hunit
    · have hsecond := congrArg Prod.snd hencode
      dsimp [encode] at hsecond
      omega
    · intro i hiv
      have hfirst := congrArg Prod.fst hencode
      exact congrFun hfirst ⟨i, hiv⟩
  have hcard :
      (affineStripInBox N L ψ a).card ≤ target.card :=
    Finset.card_le_card_of_injOn encode hmaps hinj
  have hIcc :
      (Finset.Icc (-(L : ℤ)) (L : ℤ)).card =
        2 * L + 1 := by
    rw [Int.card_Icc]
    norm_num
    rw [show
      (L : ℤ) + 1 + (L : ℤ) =
        ((2 * L + 1 : ℕ) : ℤ) by
          push_cast
          ring]
    exact Int.toNat_natCast _
  calc
    (affineStripInBox N L ψ a).card ≤ target.card := hcard
    _ = (2 * L + 1) * N ^ (Fintype.card ι - 1) := by
      simp [target, hIcc, Fintype.card_subtype_compl, mul_comm]

/-! ## CFZ coefficient and block-diameter facts -/

/-- Every CFZ form has a doubled coordinate with coefficient exactly `1` or
`-1`.  The adjacent undeleted coordinate supplies it. -/
theorem exists_cfzCoefficient_eq_one_or_neg_one
    {k : ℕ} (hk : 2 ≤ k) (q : CFZFormIndex k) :
    ∃ v : CFZVariable k,
      cfzCoefficient q v = 1 ∨
        cfzCoefficient q v = -1 := by
  rcases q with ⟨j, ω⟩
  by_cases hj : (j : ℕ) = 0
  · let i : Fin k := ⟨1, by omega⟩
    have hij : i ≠ j := by
      intro h
      have hval := congrArg Fin.val h
      simp [i, hj] at hval
    let i' : {i : Fin k // i ≠ j} := ⟨i, hij⟩
    refine ⟨(i, ω i'), Or.inl ?_⟩
    rw [cfzCoefficient_selected ⟨j, ω⟩ i']
    change ((1 : ℕ) : ℤ) - ((j : ℕ) : ℤ) = 1
    rw [hj]
    norm_num
  · have hjpos : 0 < (j : ℕ) := Nat.pos_of_ne_zero hj
    let i : Fin k := ⟨(j : ℕ) - 1, by omega⟩
    have hij : i ≠ j := by
      intro h
      have hval := congrArg Fin.val h
      simp [i] at hval
      omega
    let i' : {i : Fin k // i ≠ j} := ⟨i, hij⟩
    refine ⟨(i, ω i'), Or.inr ?_⟩
    rw [cfzCoefficient_selected ⟨j, ω⟩ i']
    change
      (((j : ℕ) - 1 : ℕ) : ℤ) -
          ((j : ℕ) : ℤ) = -1
    rw [Int.ofNat_sub (Nat.one_le_iff_ne_zero.mpr hj)]
    norm_num

/-- The affine value of a CFZ form changes by at most
`card(CFZVariable k) * k * D` inside one side-`D` quotient block. -/
theorem natAbs_cfzAffineForm_eval_sub_eval_le_of_sameQuotientBlock
    {k D : ℕ} (hD : 0 < D)
    (q : CFZFormIndex k)
    {x y : CFZVariable k → ℕ}
    (hxy : SameQuotientBlock D x y) :
    Int.natAbs
        ((cfzAffineForm q).eval (fun v => (x v : ℤ)) -
          (cfzAffineForm q).eval (fun v => (y v : ℤ))) ≤
      Fintype.card (CFZVariable k) * k * D := by
  simp only [AffineForm.eval, cfzAffineForm_constant,
    cfzAffineForm_coefficient, zero_add]
  rw [← Finset.sum_sub_distrib]
  calc
    Int.natAbs
        (∑ v,
          (cfzCoefficient q v * (x v : ℤ) -
            cfzCoefficient q v * (y v : ℤ))) ≤
      ∑ v,
        Int.natAbs
          (cfzCoefficient q v * (x v : ℤ) -
            cfzCoefficient q v * (y v : ℤ)) := by
      exact Int.natAbs_sum_le _ _
    _ = ∑ v,
        Int.natAbs
          (cfzCoefficient q v *
            ((x v : ℤ) - (y v : ℤ))) := by
      apply Finset.sum_congr rfl
      intro v _hv
      congr 2
      ring
    _ ≤ ∑ _v : CFZVariable k, k * D := by
      apply Finset.sum_le_sum
      intro v _hv
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul
        (cfzCoefficient_natAbs_le q v)
        (Nat.le_of_lt
          (natAbs_natCast_sub_natCast_lt_of_sameQuotientBlock
            hD hxy v))
    _ = Fintype.card (CFZVariable k) * k * D := by
      simp [mul_assoc]

/-! ## Carry-change hyperplanes -/

/-- The uniform carry range on the standard CFZ box. -/
def cfzCarryRange (k : ℕ) : ℕ :=
  Fintype.card (CFZVariable k) * k + 1

/-- The maximum affine variation of one CFZ form inside a side-`D`
quotient block. -/
def cfzBlockVariation (k D : ℕ) : ℕ :=
  Fintype.card (CFZVariable k) * k * D

/-- The canonical carry bounds place an affine value between the
corresponding consecutive multiples of `N`. -/
theorem cfzAffineForm_eval_mem_carryStrip
    {k N : ℕ} [NeZero N]
    (q : CFZFormIndex k) (x : CFZVariable k → ℕ) :
    (N : ℤ) * cfzCarry (N := N) q x ≤
        (cfzAffineForm q).eval (fun v => (x v : ℤ)) ∧
      (cfzAffineForm q).eval (fun v => (x v : ℤ)) <
        (N : ℤ) * (cfzCarry (N := N) q x + 1) := by
  let a : ZMod N :=
    apLinearForm k N q.1 q.2
      (cubePointOfNat (N := N) x)
  have hid :=
    cfzAffineForm_eval_eq_val_add_mul_cfzCarry
      (N := N) q x
  have hvalnonneg : (0 : ℤ) ≤ (a.val : ℤ) := by
    positivity
  have hvallt : (a.val : ℤ) < (N : ℤ) := by
    exact_mod_cast ZMod.val_lt a
  change
    (0 : ℤ) ≤
      (apLinearForm k N q.1 q.2
        (cubePointOfNat (N := N) x)).val at hvalnonneg
  change
    ((apLinearForm k N q.1 q.2
        (cubePointOfNat (N := N) x)).val : ℤ) <
      (N : ℤ) at hvallt
  constructor
  · rw [hid]
    omega
  · rw [hid]
    nlinarith

/-- Distinct carries force a multiple of `N` to lie strictly after one
affine value and weakly before the other.  The chosen hyperplane index is
one of the two carries. -/
theorem exists_carryHyperplane_between_cfzAffineForm_evals
    {k N : ℕ} [NeZero N]
    (q : CFZFormIndex k)
    (x y : CFZVariable k → ℕ)
    (hne :
      cfzCarry (N := N) q x ≠
        cfzCarry (N := N) q y) :
    ∃ c : ℤ,
      (c = cfzCarry (N := N) q x ∨
        c = cfzCarry (N := N) q y) ∧
      (((cfzAffineForm q).eval (fun v => (x v : ℤ)) <
            (N : ℤ) * c ∧
          (N : ℤ) * c ≤
            (cfzAffineForm q).eval (fun v => (y v : ℤ))) ∨
        ((cfzAffineForm q).eval (fun v => (y v : ℤ)) <
            (N : ℤ) * c ∧
          (N : ℤ) * c ≤
            (cfzAffineForm q).eval (fun v => (x v : ℤ)))) := by
  let cx := cfzCarry (N := N) q x
  let cy := cfzCarry (N := N) q y
  have hx := cfzAffineForm_eval_mem_carryStrip
    (N := N) q x
  have hy := cfzAffineForm_eval_mem_carryStrip
    (N := N) q y
  rcases lt_or_gt_of_ne hne with hxy | hyx
  · refine ⟨cy, Or.inr rfl, Or.inl ⟨?_, hy.1⟩⟩
    exact hx.2.trans_le
      (Int.mul_le_mul_of_nonneg_left
        (show cx + 1 ≤ cy by omega)
        (by positivity))
  · refine ⟨cx, Or.inl rfl, Or.inr ⟨?_, hx.1⟩⟩
    exact hy.2.trans_le
      (Int.mul_le_mul_of_nonneg_left
        (show cy + 1 ≤ cx by omega)
        (by positivity))

/-- In a linearly ordered triple, the left subinterval has no larger
integer length than the whole interval. -/
theorem natAbs_sub_le_natAbs_sub_of_le_of_le
    {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    Int.natAbs (a - b) ≤ Int.natAbs (a - c) := by
  rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs,
    Int.natCast_natAbs,
    abs_of_nonpos (sub_nonpos.mpr hab),
    abs_of_nonpos (sub_nonpos.mpr (hab.trans hbc))]
  omega

/-- The analogous bound for the right subinterval. -/
theorem natAbs_sub_le_natAbs_sub_of_le_of_le_right
    {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    Int.natAbs (c - b) ≤ Int.natAbs (c - a) := by
  rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs,
    Int.natCast_natAbs,
    abs_of_nonneg (sub_nonneg.mpr hbc),
    abs_of_nonneg (sub_nonneg.mpr (hab.trans hbc))]
  omega

/-- A point is bad for one CFZ form when another point of its quotient
block has a different canonical carry. -/
def CFZCarryBadPoint
    {k N : ℕ} [NeZero N]
    (D : ℕ) (q : CFZFormIndex k)
    (x : CFZVariable k → ℕ) : Prop :=
  x ∈ natBox (fun _ : CFZVariable k => N) ∧
    ∃ y ∈ natBox (fun _ : CFZVariable k => N),
      SameQuotientBlock D x y ∧
        cfzCarry (N := N) q x ≠
          cfzCarry (N := N) q y

/-- The finite set of bad points for one CFZ form. -/
noncomputable def cfzCarryBadPoints
    {k N : ℕ} [NeZero N]
    (D : ℕ) (q : CFZFormIndex k) :
    Finset (CFZVariable k → ℕ) := by
  classical
  exact
    (natBox (fun _ : CFZVariable k => N)).filter
      (CFZCarryBadPoint (N := N) D q)

@[simp]
theorem mem_cfzCarryBadPoints
    {k N : ℕ} [NeZero N]
    {D : ℕ} {q : CFZFormIndex k}
    {x : CFZVariable k → ℕ} :
    x ∈ cfzCarryBadPoints (N := N) D q ↔
      CFZCarryBadPoint (N := N) D q x := by
  classical
  constructor
  · intro hx
    exact (Finset.mem_filter.mp hx).2
  · intro hx
    exact Finset.mem_filter.mpr ⟨hx.1, hx⟩

/-- Natural-box version of the uniform carry bound. -/
theorem natAbs_cfzCarry_of_mem_natBox_le
    {k N : ℕ} [NeZero N]
    (q : CFZFormIndex k)
    {x : CFZVariable k → ℕ}
    (hx : x ∈ natBox (fun _ : CFZVariable k => N)) :
    Int.natAbs (cfzCarry (N := N) q x) ≤
      cfzCarryRange k := by
  let x' : FiniteBox (fun _ : CFZVariable k => N) :=
    fun v => ⟨x v, mem_natBox.mp hx v⟩
  have hbound :=
    natAbs_cfzCarry_finiteBox_le (N := N) q x'
  simpa [cfzCarryRange, x'] using hbound

/-- Every bad point lies in a width-`cfzBlockVariation k D` strip around a
carry hyperplane whose index is in the uniform carry range. -/
theorem exists_carryHyperplane_near_of_badPoint
    {k N D : ℕ} [NeZero N] (hD : 0 < D)
    (q : CFZFormIndex k) (x : CFZVariable k → ℕ)
    (hx : CFZCarryBadPoint (N := N) D q x) :
    ∃ c : ℤ,
      Int.natAbs c ≤ cfzCarryRange k ∧
        x ∈ affineStripInBox N (cfzBlockVariation k D)
          (cfzAffineForm q) ((N : ℤ) * c) := by
  obtain ⟨hxbox, y, hybox, hxy, hcarry⟩ := hx
  obtain ⟨c, hc, hbetween⟩ :=
    exists_carryHyperplane_between_cfzAffineForm_evals
      (N := N) q x y hcarry
  have hdiam :
      Int.natAbs
          ((cfzAffineForm q).eval (fun v => (x v : ℤ)) -
            (cfzAffineForm q).eval (fun v => (y v : ℤ))) ≤
        cfzBlockVariation k D := by
    exact
      natAbs_cfzAffineForm_eval_sub_eval_le_of_sameQuotientBlock
        hD q hxy
  have hcbound :
      Int.natAbs c ≤ cfzCarryRange k := by
    rcases hc with rfl | rfl
    · exact natAbs_cfzCarry_of_mem_natBox_le q hxbox
    · exact natAbs_cfzCarry_of_mem_natBox_le q hybox
  refine ⟨c, hcbound, mem_affineStripInBox.mpr ⟨hxbox, ?_⟩⟩
  rcases hbetween with hbetween | hbetween
  · exact
      (natAbs_sub_le_natAbs_sub_of_le_of_le
        hbetween.1.le hbetween.2).trans hdiam
  · exact
      (natAbs_sub_le_natAbs_sub_of_le_of_le_right
        hbetween.1.le hbetween.2).trans hdiam

/-- If two points in one block have different carries, the entire block is
confined to a single explicit strip of half-width
`2 * cfzBlockVariation k D` around one carry hyperplane. -/
theorem quotientBlock_subset_carryHyperplaneStrip_of_carry_ne
    {k N D : ℕ} [NeZero N] (hD : 0 < D)
    (q : CFZFormIndex k)
    {x y : CFZVariable k → ℕ}
    (hx : x ∈ natBox (fun _ : CFZVariable k => N))
    (hy : y ∈ quotientBlock N D x)
    (hcarry :
      cfzCarry (N := N) q x ≠
        cfzCarry (N := N) q y) :
    ∃ c : ℤ,
      Int.natAbs c ≤ cfzCarryRange k ∧
        quotientBlock N D x ⊆
          affineStripInBox N (2 * cfzBlockVariation k D)
            (cfzAffineForm q) ((N : ℤ) * c) := by
  have hy' := mem_quotientBlock.mp hy
  obtain ⟨c, hc, hbetween⟩ :=
    exists_carryHyperplane_between_cfzAffineForm_evals
      (N := N) q x y hcarry
  have hcbound :
      Int.natAbs c ≤ cfzCarryRange k := by
    rcases hc with rfl | rfl
    · exact natAbs_cfzCarry_of_mem_natBox_le q hx
    · exact natAbs_cfzCarry_of_mem_natBox_le q hy'.1
  have hxnear :
      Int.natAbs
          ((cfzAffineForm q).eval (fun v => (x v : ℤ)) -
            (N : ℤ) * c) ≤
        cfzBlockVariation k D := by
    have hdiam :=
      natAbs_cfzAffineForm_eval_sub_eval_le_of_sameQuotientBlock
        hD q hy'.2
    rcases hbetween with hbetween | hbetween
    · exact
        (natAbs_sub_le_natAbs_sub_of_le_of_le
          hbetween.1.le hbetween.2).trans hdiam
    · exact
        (natAbs_sub_le_natAbs_sub_of_le_of_le_right
          hbetween.1.le hbetween.2).trans hdiam
  refine ⟨c, hcbound, ?_⟩
  intro z hz
  have hz' := mem_quotientBlock.mp hz
  have hzx :
      Int.natAbs
          ((cfzAffineForm q).eval (fun v => (z v : ℤ)) -
            (cfzAffineForm q).eval (fun v => (x v : ℤ))) ≤
        cfzBlockVariation k D := by
    exact
      natAbs_cfzAffineForm_eval_sub_eval_le_of_sameQuotientBlock
        hD q hz'.2.symm
  apply mem_affineStripInBox.mpr
  refine ⟨hz'.1, ?_⟩
  calc
    Int.natAbs
        ((cfzAffineForm q).eval (fun v => (z v : ℤ)) -
          (N : ℤ) * c) =
      Int.natAbs
        (((cfzAffineForm q).eval (fun v => (z v : ℤ)) -
            (cfzAffineForm q).eval (fun v => (x v : ℤ))) +
          ((cfzAffineForm q).eval (fun v => (x v : ℤ)) -
            (N : ℤ) * c)) := by
      congr 1
      ring
    _ ≤
        Int.natAbs
            ((cfzAffineForm q).eval (fun v => (z v : ℤ)) -
              (cfzAffineForm q).eval (fun v => (x v : ℤ))) +
          Int.natAbs
            ((cfzAffineForm q).eval (fun v => (x v : ℤ)) -
              (N : ℤ) * c) :=
      Int.natAbs_add_le _ _
    _ ≤ 2 * cfzBlockVariation k D := by
      omega

/-! ## Explicit bad-point counts -/

/-- Union of the finitely many strips that can contain a bad point for one
CFZ form. -/
noncomputable def cfzCarryHyperplaneEnvelope
    {k N : ℕ} (D : ℕ) (q : CFZFormIndex k) :
    Finset (CFZVariable k → ℕ) := by
  classical
  exact
    (Finset.Icc (-(cfzCarryRange k : ℤ))
        (cfzCarryRange k : ℤ)).biUnion fun c =>
      affineStripInBox N (cfzBlockVariation k D)
        (cfzAffineForm q) ((N : ℤ) * c)

/-- The one-form bad set is contained in its finite hyperplane envelope. -/
theorem cfzCarryBadPoints_subset_hyperplaneEnvelope
    {k N D : ℕ} [NeZero N] (hD : 0 < D)
    (q : CFZFormIndex k) :
    cfzCarryBadPoints (N := N) D q ⊆
      cfzCarryHyperplaneEnvelope (N := N) D q := by
  classical
  intro x hx
  obtain ⟨c, hc, hxstrip⟩ :=
    exists_carryHyperplane_near_of_badPoint
      hD q x (mem_cfzCarryBadPoints.mp hx)
  apply Finset.mem_biUnion.mpr
  refine ⟨c, ?_, hxstrip⟩
  have hcast :
      |c| ≤ (cfzCarryRange k : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hc
  exact Finset.mem_Icc.mpr (abs_le.mp hcast)

/-- Exact cardinality bound for the one-form carry-hyperplane envelope. -/
theorem card_cfzCarryHyperplaneEnvelope_le
    {k N D : ℕ} (hk : 2 ≤ k)
    (q : CFZFormIndex k) :
    (cfzCarryHyperplaneEnvelope (N := N) D q).card ≤
      (2 * cfzCarryRange k + 1) *
        (2 * cfzBlockVariation k D + 1) *
        N ^ (Fintype.card (CFZVariable k) - 1) := by
  classical
  obtain ⟨v, hv⟩ :=
    exists_cfzCoefficient_eq_one_or_neg_one hk q
  have hunit :
      (cfzAffineForm q).coefficient v = 1 ∨
        (cfzAffineForm q).coefficient v = -1 := by
    simpa only [cfzAffineForm_coefficient] using hv
  have hstrip :
      ∀ c : ℤ,
        (affineStripInBox N (cfzBlockVariation k D)
            (cfzAffineForm q) ((N : ℤ) * c)).card ≤
          (2 * cfzBlockVariation k D + 1) *
            N ^ (Fintype.card (CFZVariable k) - 1) :=
    fun c =>
      card_affineStripInBox_le
        N (cfzBlockVariation k D) (cfzAffineForm q)
        ((N : ℤ) * c) v hunit
  calc
    (cfzCarryHyperplaneEnvelope (N := N) D q).card ≤
        ∑ c ∈ Finset.Icc (-(cfzCarryRange k : ℤ))
            (cfzCarryRange k : ℤ),
          (affineStripInBox N (cfzBlockVariation k D)
            (cfzAffineForm q) ((N : ℤ) * c)).card := by
      exact Finset.card_biUnion_le
    _ ≤
        ∑ _c ∈ Finset.Icc (-(cfzCarryRange k : ℤ))
            (cfzCarryRange k : ℤ),
          ((2 * cfzBlockVariation k D + 1) *
            N ^ (Fintype.card (CFZVariable k) - 1)) := by
      exact Finset.sum_le_sum fun c _hc => hstrip c
    _ =
        (2 * cfzCarryRange k + 1) *
          (2 * cfzBlockVariation k D + 1) *
          N ^ (Fintype.card (CFZVariable k) - 1) := by
      have hcard :
          (Finset.Icc (-(cfzCarryRange k : ℤ))
              (cfzCarryRange k : ℤ)).card =
            2 * cfzCarryRange k + 1 := by
        rw [Int.card_Icc]
        norm_num
        rw [show
          (cfzCarryRange k : ℤ) + 1 +
              (cfzCarryRange k : ℤ) =
            ((2 * cfzCarryRange k + 1 : ℕ) : ℤ) by
              push_cast
              ring]
        exact Int.toNat_natCast _
      rw [Finset.sum_const, Nat.nsmul_eq_mul, hcard]
      ring

/-- Exact one-form bad-point bound. -/
theorem card_cfzCarryBadPoints_le
    {k N D : ℕ} [NeZero N]
    (hk : 2 ≤ k) (hD : 0 < D)
    (q : CFZFormIndex k) :
    (cfzCarryBadPoints (N := N) D q).card ≤
      (2 * cfzCarryRange k + 1) *
        (2 * cfzBlockVariation k D + 1) *
        N ^ (Fintype.card (CFZVariable k) - 1) := by
  exact
    (Finset.card_le_card
      (cfzCarryBadPoints_subset_hyperplaneEnvelope hD q)).trans
      (card_cfzCarryHyperplaneEnvelope_le hk q)

/-- `O_k(D N^(t-1))` form of the one-form bad-point bound. -/
theorem card_cfzCarryBadPoints_le_linear
    {k N D : ℕ} [NeZero N]
    (hk : 2 ≤ k) (hD : 0 < D)
    (q : CFZFormIndex k) :
    (cfzCarryBadPoints (N := N) D q).card ≤
      (2 * cfzCarryRange k + 1) *
        (2 * Fintype.card (CFZVariable k) * k + 1) *
        D * N ^ (Fintype.card (CFZVariable k) - 1) := by
  have hbase :=
    card_cfzCarryBadPoints_le
      (N := N) (D := D) hk hD q
  have hvariation :
      2 * cfzBlockVariation k D + 1 ≤
        (2 * Fintype.card (CFZVariable k) * k + 1) * D := by
    simp only [cfzBlockVariation]
    nlinarith
  calc
    (cfzCarryBadPoints (N := N) D q).card ≤
        (2 * cfzCarryRange k + 1) *
          (2 * cfzBlockVariation k D + 1) *
          N ^ (Fintype.card (CFZVariable k) - 1) :=
      hbase
    _ ≤
        (2 * cfzCarryRange k + 1) *
          (2 * Fintype.card (CFZVariable k) * k + 1) *
          D * N ^ (Fintype.card (CFZVariable k) - 1) := by
      calc
        (2 * cfzCarryRange k + 1) *
              (2 * cfzBlockVariation k D + 1) *
              N ^ (Fintype.card (CFZVariable k) - 1) ≤
            (2 * cfzCarryRange k + 1) *
              ((2 * Fintype.card (CFZVariable k) * k + 1) * D) *
              N ^ (Fintype.card (CFZVariable k) - 1) :=
          Nat.mul_le_mul_right _
            (Nat.mul_le_mul_left _ hvariation)
        _ =
            (2 * cfzCarryRange k + 1) *
              (2 * Fintype.card (CFZVariable k) * k + 1) *
              D * N ^ (Fintype.card (CFZVariable k) - 1) := by
          ring

/-- Bad points for at least one form of a finite selected family. -/
noncomputable def cfzFamilyCarryBadPoints
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (D : ℕ) (forms : κ → CFZFormIndex k) :
    Finset (CFZVariable k → ℕ) := by
  classical
  exact Finset.univ.biUnion fun q =>
    cfzCarryBadPoints (N := N) D (forms q)

/-- Exact union bound for an arbitrary finite selected CFZ family. -/
theorem card_cfzFamilyCarryBadPoints_le_linear
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N D : ℕ} [NeZero N]
    (hk : 2 ≤ k) (hD : 0 < D)
    (forms : κ → CFZFormIndex k) :
    (cfzFamilyCarryBadPoints (N := N) D forms).card ≤
      Fintype.card κ *
        ((2 * cfzCarryRange k + 1) *
          (2 * Fintype.card (CFZVariable k) * k + 1) *
          D * N ^ (Fintype.card (CFZVariable k) - 1)) := by
  classical
  calc
    (cfzFamilyCarryBadPoints (N := N) D forms).card ≤
        ∑ q,
          (cfzCarryBadPoints (N := N) D (forms q)).card := by
      exact Finset.card_biUnion_le
    _ ≤
        ∑ _q : κ,
          ((2 * cfzCarryRange k + 1) *
            (2 * Fintype.card (CFZVariable k) * k + 1) *
            D * N ^ (Fintype.card (CFZVariable k) - 1)) := by
      exact Finset.sum_le_sum fun q _hq =>
        card_cfzCarryBadPoints_le_linear hk hD (forms q)
    _ =
        Fintype.card κ *
          ((2 * cfzCarryRange k + 1) *
            (2 * Fintype.card (CFZVariable k) * k + 1) *
            D * N ^ (Fintype.card (CFZVariable k) - 1)) := by
      simp

/-- Outside the family bad set, the full quotient block is a simultaneous
CFZ carry cell, with carry vector given by the anchor point. -/
theorem isCFZCarryCell_quotientBlock_of_not_mem_bad
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N D : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k)
    (x : CFZVariable k → ℕ)
    (hx : x ∈ natBox (fun _ : CFZVariable k => N))
    (hgood :
      x ∉ cfzFamilyCarryBadPoints (N := N) D forms) :
    IsCFZCarryCell (N := N) forms
      (fun q => cfzCarry (N := N) (forms q) x)
      (quotientBlock N D x) := by
  classical
  intro y hy q
  have hy' := mem_quotientBlock.mp hy
  have hcarry :
      cfzCarry (N := N) (forms q) y =
        cfzCarry (N := N) (forms q) x := by
    by_contra hne
    apply hgood
    apply Finset.mem_biUnion.mpr
    refine ⟨q, Finset.mem_univ q, mem_cfzCarryBadPoints.mpr ?_⟩
    exact
      ⟨hx, y, hy'.1, hy'.2,
        fun h => hne h.symm⟩
  rw [cfzAffineForm_eval_eq_val_add_mul_cfzCarry
    (N := N), hcarry]
  rfl

/-! ## Carry-adjusted affine block model -/

/-- The lower corner of the coordinatewise quotient block containing `x`. -/
def quotientBlockBase {ι : Type*} (D : ℕ)
    (x : ι → ℕ) : ι → ℕ :=
  fun i => D * (x i / D)

/-- A positive-side block base lies in the same quotient block. -/
theorem sameQuotientBlock_quotientBlockBase
    {ι : Type*} {D : ℕ} (hD : 0 < D)
    (x : ι → ℕ) :
    SameQuotientBlock D x (quotientBlockBase D x) := by
  intro i
  rw [quotientBlockBase, Nat.mul_comm,
    Nat.mul_div_left _ hD]

/-- The block base is coordinatewise no larger than the original point. -/
theorem quotientBlockBase_le
    {ι : Type*} (D : ℕ) (x : ι → ℕ) (i : ι) :
    quotientBlockBase D x i ≤ x i := by
  simpa [quotientBlockBase, Nat.mul_comm] using
    Nat.div_mul_le_self (x i) D

/-- Hence the block base of a point in the standard box remains in the
standard box. -/
theorem quotientBlockBase_mem_natBox
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N D : ℕ} {x : ι → ℕ}
    (hx : x ∈ natBox (fun _ : ι => N)) :
    quotientBlockBase D x ∈ natBox (fun _ : ι => N) := by
  rw [mem_natBox]
  intro i
  exact (quotientBlockBase_le D x i).trans_lt
    (mem_natBox.mp hx i)

/-- The integer W-tricked affine form with the correction
`-W*N*c` corresponding to a fixed carry `c`. -/
def cfzCarryAdjustedAffineForm
    {k : ℕ} (N W b : ℕ)
    (q : CFZFormIndex k) (c : ℤ) :
    AffineForm (CFZVariable k) ℤ where
  constant :=
    (wTrickedAffineForm W b (cfzAffineForm q)).constant -
      (W : ℤ) * (N : ℤ) * c
  coefficient :=
    (wTrickedAffineForm W b (cfzAffineForm q)).coefficient

@[simp]
theorem cfzCarryAdjustedAffineForm_constant
    {k : ℕ} (N W b : ℕ)
    (q : CFZFormIndex k) (c : ℤ) :
    (cfzCarryAdjustedAffineForm N W b q c).constant =
      (b : ℤ) - (W : ℤ) * (N : ℤ) * c := by
  simp [cfzCarryAdjustedAffineForm]

@[simp]
theorem cfzCarryAdjustedAffineForm_coefficient
    {k : ℕ} (N W b : ℕ)
    (q : CFZFormIndex k) (c : ℤ)
    (v : CFZVariable k) :
    (cfzCarryAdjustedAffineForm N W b q c).coefficient v =
      (W : ℤ) * cfzCoefficient q v := by
  rfl

/-- Evaluation of the carry-adjusted affine form. -/
theorem cfzCarryAdjustedAffineForm_eval
    {k : ℕ} (N W b : ℕ)
    (q : CFZFormIndex k) (c : ℤ)
    (x : CFZVariable k → ℤ) :
    (cfzCarryAdjustedAffineForm N W b q c).eval x =
      (W : ℤ) * (cfzAffineForm q).eval x + b -
        (W : ℤ) * (N : ℤ) * c := by
  calc
    (cfzCarryAdjustedAffineForm N W b q c).eval x =
        (wTrickedAffineForm W b (cfzAffineForm q)).eval x -
          (W : ℤ) * (N : ℤ) * c := by
      simp only [AffineForm.eval,
        cfzCarryAdjustedAffineForm,
        wTrickedAffineForm_constant,
        wTrickedAffineForm_coefficient]
      ring
    _ =
        (W : ℤ) * (cfzAffineForm q).eval x + b -
          (W : ℤ) * (N : ℤ) * c := by
      rw [wTrickedAffineForm_eval]

/-- With the canonical carry, the adjusted affine evaluation is literally
the natural cyclic lift viewed as an integer. -/
theorem cfzCarryAdjustedAffineForm_eval_canonicalCarry
    {k N : ℕ} [NeZero N]
    (W b : ℕ) (q : CFZFormIndex k)
    (x : CFZVariable k → ℕ) :
    (cfzCarryAdjustedAffineForm N W b q
        (cfzCarry (N := N) q x)).eval
        (fun v => (x v : ℤ)) =
      (cfzWTrickedLinearValue W b q
        (cubePointOfNat (N := N) x) : ℤ) := by
  rw [cfzCarryAdjustedAffineForm_eval,
    cfzAffineForm_eval_eq_val_add_mul_cfzCarry
      (N := N)]
  unfold cfzWTrickedLinearValue wTrickedValue
  push_cast
  ring

/-- Natural value of a carry-adjusted affine form.  On a good block its
integer evaluation is nonnegative and this is its exact natural value. -/
def cfzCarryAdjustedAffineValue
    {k : ℕ} (N W b : ℕ)
    (q : CFZFormIndex k) (c : ℤ)
    (x : CFZVariable k → ℕ) : ℕ :=
  Int.toNat
    ((cfzCarryAdjustedAffineForm N W b q c).eval
      (fun v => (x v : ℤ)))

/-- Choosing the actual canonical carry recovers the cyclic CFZ lift
exactly, with no compatibility assumption on any divisor modulus. -/
theorem cfzCarryAdjustedAffineValue_canonicalCarry
    {k N : ℕ} [NeZero N]
    (W b : ℕ) (q : CFZFormIndex k)
    (x : CFZVariable k → ℕ) :
    cfzCarryAdjustedAffineValue N W b q
        (cfzCarry (N := N) q x) x =
      cfzWTrickedLinearValue W b q
        (cubePointOfNat (N := N) x) := by
  unfold cfzCarryAdjustedAffineValue
  rw [cfzCarryAdjustedAffineForm_eval_canonicalCarry]
  exact Int.toNat_natCast _

/-- Carry-adjusted affine value obtained from the canonical carry at the
lower corner of the point's quotient block. -/
def cfzCarryBlockAffineValue
    {k N : ℕ} [NeZero N]
    (D W b : ℕ) (q : CFZFormIndex k)
    (x : CFZVariable k → ℕ) : ℕ :=
  cfzCarryAdjustedAffineValue N W b q
    (cfzCarry (N := N) q (quotientBlockBase D x)) x

/-- Outside the one-form bad set, the carry at the block base equals the
carry at the point. -/
theorem cfzCarry_quotientBlockBase_eq_of_not_bad
    {k N D : ℕ} [NeZero N] (hD : 0 < D)
    (q : CFZFormIndex k)
    {x : CFZVariable k → ℕ}
    (hx : x ∈ natBox (fun _ : CFZVariable k => N))
    (hgood : ¬CFZCarryBadPoint (N := N) D q x) :
    cfzCarry (N := N) q (quotientBlockBase D x) =
      cfzCarry (N := N) q x := by
  by_contra hne
  apply hgood
  exact
    ⟨hx, quotientBlockBase D x,
      quotientBlockBase_mem_natBox hx,
      sameQuotientBlock_quotientBlockBase hD x,
      fun h => hne h.symm⟩

/-- The cyclic lift and the carry-block affine model agree at every good
point. -/
theorem cfzCarryBlockAffineValue_eq_cyclic_of_not_bad
    {k N D : ℕ} [NeZero N] (hD : 0 < D)
    (W b : ℕ) (q : CFZFormIndex k)
    {x : CFZVariable k → ℕ}
    (hx : x ∈ natBox (fun _ : CFZVariable k => N))
    (hgood : ¬CFZCarryBadPoint (N := N) D q x) :
    cfzCarryBlockAffineValue (N := N) D W b q x =
      cfzWTrickedLinearValue W b q
        (cubePointOfNat (N := N) x) := by
  unfold cfzCarryBlockAffineValue
  rw [cfzCarry_quotientBlockBase_eq_of_not_bad
    hD q hx hgood]
  exact cfzCarryAdjustedAffineValue_canonicalCarry
    W b q x

/-- Outside the family bad set, all paired divisibility conditions agree
with the carry-block affine model. -/
theorem pairedDivisibilityIndicator_cfz_eq_carryBlockAffine_of_not_bad
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N D : ℕ} [NeZero N] (hD : 0 < D)
    (W b : ℕ) (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ)
    {x : CFZVariable k → ℕ}
    (hx : x ∈ natBox (fun _ : CFZVariable k => N))
    (hgood :
      x ∉ cfzFamilyCarryBadPoints (N := N) D forms) :
    pairedDivisibilityIndicator
        (fun q y =>
          cfzWTrickedLinearValue W b (forms q)
            (cubePointOfNat (N := N) y))
        z x =
      pairedDivisibilityIndicator
        (fun q y =>
          cfzCarryBlockAffineValue (N := N)
            D W b (forms q) y)
        z x := by
  apply Finset.prod_congr rfl
  intro q _hq
  have hqgood :
      ¬CFZCarryBadPoint (N := N) D (forms q) x := by
    intro hbad
    apply hgood
    apply Finset.mem_biUnion.mpr
    exact
      ⟨q, Finset.mem_univ q,
        mem_cfzCarryBadPoints.mpr hbad⟩
  change
    natDivisibilityIndicator (z q).1
          (cfzWTrickedLinearValue W b (forms q)
            (cubePointOfNat (N := N) x)) *
        natDivisibilityIndicator (z q).2
          (cfzWTrickedLinearValue W b (forms q)
            (cubePointOfNat (N := N) x)) =
      natDivisibilityIndicator (z q).1
          (cfzCarryBlockAffineValue (N := N)
            D W b (forms q) x) *
        natDivisibilityIndicator (z q).2
          (cfzCarryBlockAffineValue (N := N)
            D W b (forms q) x)
  rw [cfzCarryBlockAffineValue_eq_cyclic_of_not_bad
    hD W b (forms q) hx hqgood]

/-! ## A normalized disagreement bound -/

/-- Pull a natural-vector bad set back to the typed finite box. -/
noncomputable def finiteBoxBadSet
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (side : ι → ℕ) (bad : Finset (ι → ℕ)) :
    Finset (FiniteBox side) := by
  classical
  exact Finset.univ.filter fun x =>
    (fun i => (x i : ℕ)) ∈ bad

@[simp]
theorem mem_finiteBoxBadSet
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {side : ι → ℕ} {bad : Finset (ι → ℕ)}
    {x : FiniteBox side} :
    x ∈ finiteBoxBadSet side bad ↔
      (fun i => (x i : ℕ)) ∈ bad := by
  classical
  simp [finiteBoxBadSet]

/-- If the natural bad set lies in the box, its typed pullback has no larger
cardinality. -/
theorem card_finiteBoxBadSet_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (side : ι → ℕ) (bad : Finset (ι → ℕ))
    (_hbad : bad ⊆ natBox side) :
    (finiteBoxBadSet side bad).card ≤ bad.card := by
  classical
  let coePoint : FiniteBox side → (ι → ℕ) :=
    fun x i => (x i : ℕ)
  apply Finset.card_le_card_of_injOn coePoint
  · intro x hx
    exact mem_finiteBoxBadSet.mp hx
  · intro x _hx y _hy hxy
    funext i
    exact Fin.ext (congrFun hxy i)

theorem mean_neg_eq_neg_mean
    {α : Type*} [Fintype α] (F : α → ℝ) :
    mean (fun x => -F x) = -mean F := by
  unfold mean
  exact Finset.expect_neg_distrib Finset.univ F

/-- Two functions that agree off `bad` and differ by at most one everywhere
have means differing by at most the density of `bad`. -/
theorem abs_mean_sub_mean_le_bad
    {α : Type*} [Fintype α] [DecidableEq α]
    (bad : Finset α) (F G : α → ℝ)
    (heq : ∀ x, x ∉ bad → F x = G x)
    (hbound : ∀ x, |F x - G x| ≤ 1) :
    |mean F - mean G| ≤
      (bad.card : ℝ) / Fintype.card α := by
  let I : α → ℝ := finsetIndicator bad
  have hupper :
      mean (fun x => F x - G x) ≤ mean I := by
    apply mean_mono
    intro x
    by_cases hx : x ∈ bad
    · change F x - G x ≤ finsetIndicator bad x
      rw [finsetIndicator_of_mem hx]
      exact le_of_abs_le (hbound x)
    · change F x - G x ≤ finsetIndicator bad x
      rw [finsetIndicator_of_not_mem hx, heq x hx, sub_self]
  have hlower :
      mean (fun x => -I x) ≤
        mean (fun x => F x - G x) := by
    apply mean_mono
    intro x
    by_cases hx : x ∈ bad
    · change -finsetIndicator bad x ≤ F x - G x
      rw [finsetIndicator_of_mem hx]
      exact neg_le_of_abs_le (hbound x)
    · change -finsetIndicator bad x ≤ F x - G x
      rw [finsetIndicator_of_not_mem hx, heq x hx, sub_self,
        neg_zero]
  rw [mean_neg_eq_neg_mean] at hlower
  have hI :
      mean I = (bad.card : ℝ) / Fintype.card α := by
    simpa only [I] using mean_finsetIndicator bad
  rw [hI] at hupper hlower
  rw [← mean_sub F G]
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- Natural-box form of the normalized disagreement estimate. -/
theorem abs_boxMean_sub_boxMean_le_bad
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (side : ι → ℕ) (bad : Finset (ι → ℕ))
    (F G : (ι → ℕ) → ℝ)
    (hbad : bad ⊆ natBox side)
    (heq : ∀ x ∈ natBox side, x ∉ bad → F x = G x)
    (hbound : ∀ x ∈ natBox side, |F x - G x| ≤ 1) :
    |boxMean side F - boxMean side G| ≤
      (bad.card : ℝ) / ∏ i, (side i : ℝ) := by
  rw [boxMean_eq_mean_finiteBox,
    boxMean_eq_mean_finiteBox]
  let typedBad := finiteBoxBadSet side bad
  have htyped :=
    abs_mean_sub_mean_le_bad typedBad
      (fun x : FiniteBox side => F (fun i => (x i : ℕ)))
      (fun x : FiniteBox side => G (fun i => (x i : ℕ)))
      (fun x hx => by
        apply heq (fun i => (x i : ℕ))
        · rw [mem_natBox]
          exact fun i => (x i).isLt
        · simpa only [typedBad, mem_finiteBoxBadSet] using hx)
      (fun x =>
        hbound (fun i => (x i : ℕ))
          (by
            rw [mem_natBox]
            exact fun i => (x i).isLt))
  have hcard :
      (typedBad.card : ℝ) ≤ (bad.card : ℝ) := by
    exact_mod_cast card_finiteBoxBadSet_le side bad hbad
  rw [card_finiteBox] at htyped
  have hdiv :
      (typedBad.card : ℝ) /
          ((∏ i, side i : ℕ) : ℝ) ≤
        (bad.card : ℝ) /
          ((∏ i, side i : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right hcard
      (show
        (0 : ℝ) ≤ ((∏ i, side i : ℕ) : ℝ) by
          positivity)
  exact htyped.trans (by
    simpa only [Nat.cast_prod] using hdiv)

/-- Difference of two paired divisibility indicators is at most one. -/
theorem abs_pairedDivisibilityIndicator_sub_le_one
    {κ X : Type*} [Fintype κ]
    (values₁ values₂ : κ → X → ℕ)
    (z : κ → ℕ × ℕ) (x : X) :
    |pairedDivisibilityIndicator values₁ z x -
      pairedDivisibilityIndicator values₂ z x| ≤ 1 := by
  have h₁nonneg :
      0 ≤ pairedDivisibilityIndicator values₁ z x := by
    unfold pairedDivisibilityIndicator natDivisibilityIndicator
    positivity
  have h₂nonneg :
      0 ≤ pairedDivisibilityIndicator values₂ z x := by
    unfold pairedDivisibilityIndicator natDivisibilityIndicator
    positivity
  have h₁le :
      pairedDivisibilityIndicator values₁ z x ≤ 1 :=
    le_of_abs_le
      (abs_pairedDivisibilityIndicator_le_one values₁ z x)
  have h₂le :
      pairedDivisibilityIndicator values₂ z x ≤ 1 :=
    le_of_abs_le
      (abs_pairedDivisibilityIndicator_le_one values₂ z x)
  rw [abs_le]
  constructor <;> linarith

/-- Global density of the carry-dependent affine block model. -/
noncomputable def cfzCarryBlockPairedModelDensity
    {κ : Type*} [Fintype κ]
    {k N : ℕ} [NeZero N]
    (D W b : ℕ) (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ) : ℝ :=
  boxMean (fun _ : CFZVariable k => N)
    (pairedDivisibilityIndicator
      (fun q x =>
        cfzCarryBlockAffineValue (N := N)
          D W b (forms q) x)
      z)

/-- **Unconditional carry-block bridge.**

The actual cyclic paired-divisibility density differs from the
carry-dependent affine block model only on the family carry-bad set.  No
false periodicity and no compatibility condition such as `D ∣ W*N` is used.
-/
theorem abs_pairedDivisibilityDensity_cfz_sub_carryBlockModel_le_bad
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N D : ℕ} [NeZero N] (hD : 0 < D)
    (W b : ℕ) (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ) :
    |pairedDivisibilityDensity
        (fun q (x : CubePoint k N) =>
          cfzWTrickedLinearValue W b (forms q) x)
        z -
      cfzCarryBlockPairedModelDensity
        (N := N) D W b forms z| ≤
      ((cfzFamilyCarryBadPoints
        (N := N) D forms).card : ℝ) /
        (N : ℝ) ^ Fintype.card (CFZVariable k) := by
  let F : (CFZVariable k → ℕ) → ℝ :=
    pairedDivisibilityIndicator
      (fun q x =>
        cfzWTrickedLinearValue W b (forms q)
          (cubePointOfNat (N := N) x))
      z
  let G : (CFZVariable k → ℕ) → ℝ :=
    pairedDivisibilityIndicator
      (fun q x =>
        cfzCarryBlockAffineValue (N := N)
          D W b (forms q) x)
      z
  have hactual :
      pairedDivisibilityDensity
          (fun q (x : CubePoint k N) =>
            cfzWTrickedLinearValue W b (forms q) x)
          z =
        boxMean (fun _ : CFZVariable k => N) F := by
    unfold pairedDivisibilityDensity
    exact mean_cubePoint_eq_boxMean _
  have hmodel :
      cfzCarryBlockPairedModelDensity
          (N := N) D W b forms z =
        boxMean (fun _ : CFZVariable k => N) G := by
    rfl
  rw [hactual, hmodel]
  have hbox :=
    abs_boxMean_sub_boxMean_le_bad
      (fun _ : CFZVariable k => N)
      (cfzFamilyCarryBadPoints (N := N) D forms)
      F G
      (fun x hx => by
        obtain ⟨q, _hq, hxq⟩ :=
          Finset.mem_biUnion.mp hx
        exact (mem_cfzCarryBadPoints.mp hxq).1)
      (fun x hx hgood =>
        pairedDivisibilityIndicator_cfz_eq_carryBlockAffine_of_not_bad
          hD W b forms z hx hgood)
      (fun x _hx =>
        abs_pairedDivisibilityIndicator_sub_le_one
          (fun q y =>
            cfzWTrickedLinearValue W b (forms q)
              (cubePointOfNat (N := N) y))
          (fun q y =>
            cfzCarryBlockAffineValue (N := N)
              D W b (forms q) y)
          z x)
  simpa only [Finset.prod_const, Finset.card_univ] using hbox

/-- Explicit `O_{k,|κ|}(D/N)` form of the unconditional carry-block bridge. -/
theorem abs_pairedDivisibilityDensity_cfz_sub_carryBlockModel_le_linear
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N D : ℕ} [NeZero N]
    (hk : 2 ≤ k) (hD : 0 < D)
    (W b : ℕ) (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ) :
    |pairedDivisibilityDensity
        (fun q (x : CubePoint k N) =>
          cfzWTrickedLinearValue W b (forms q) x)
        z -
      cfzCarryBlockPairedModelDensity
        (N := N) D W b forms z| ≤
      (Fintype.card κ : ℝ) *
        (2 * cfzCarryRange k + 1) *
        (2 * Fintype.card (CFZVariable k) * k + 1) *
        D * (N : ℝ) ^
          (Fintype.card (CFZVariable k) - 1) /
        (N : ℝ) ^ Fintype.card (CFZVariable k) := by
  have hbridge :=
    abs_pairedDivisibilityDensity_cfz_sub_carryBlockModel_le_bad
      (N := N) hD W b forms z
  have hbad :=
    card_cfzFamilyCarryBadPoints_le_linear
      (N := N) hk hD forms
  calc
    |pairedDivisibilityDensity
        (fun q (x : CubePoint k N) =>
          cfzWTrickedLinearValue W b (forms q) x)
        z -
      cfzCarryBlockPairedModelDensity
        (N := N) D W b forms z| ≤
        ((cfzFamilyCarryBadPoints
          (N := N) D forms).card : ℝ) /
          (N : ℝ) ^ Fintype.card (CFZVariable k) :=
      hbridge
    _ ≤
        ((Fintype.card κ *
          ((2 * cfzCarryRange k + 1) *
            (2 * Fintype.card (CFZVariable k) * k + 1) *
            D * N ^ (Fintype.card (CFZVariable k) - 1)) : ℕ) : ℝ) /
          (N : ℝ) ^ Fintype.card (CFZVariable k) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast hbad
      · positivity
    _ =
        (Fintype.card κ : ℝ) *
          (2 * cfzCarryRange k + 1) *
          (2 * Fintype.card (CFZVariable k) * k + 1) *
          D * (N : ℝ) ^
            (Fintype.card (CFZVariable k) - 1) /
          (N : ℝ) ^ Fintype.card (CFZVariable k) := by
      push_cast
      ring

/-! ## Carry-dependent affine residue model -/

/-- Residue value of the carry-adjusted affine form whose carry is sampled
at the lower corner of the point's quotient block. -/
def cfzCarryBlockAffineResidueValue
    {k N M : ℕ} [NeZero N] [NeZero M]
    (D W b : ℕ) (q : CFZFormIndex k)
    (x : CFZVariable k → ℕ) : ℕ :=
  ((cfzCarryAdjustedAffineForm N W b q
      (cfzCarry (N := N) q
        (quotientBlockBase D x))).evalZMod M
      (fun v => (x v : ZMod M))).val

@[simp]
theorem natCast_cfzCarryBlockAffineResidueValue
    {k N M : ℕ} [NeZero N] [NeZero M]
    (D W b : ℕ) (q : CFZFormIndex k)
    (x : CFZVariable k → ℕ) :
    (cfzCarryBlockAffineResidueValue
        (N := N) (M := M) D W b q x : ZMod M) =
      (cfzCarryAdjustedAffineForm N W b q
        (cfzCarry (N := N) q
          (quotientBlockBase D x))).evalZMod M
        (fun v => (x v : ZMod M)) := by
  exact ZMod.natCast_zmod_val _

/-- On a good point, the cyclic lift and its carry-block affine residue
value agree modulo every modulus `M`.  This is the unconditional modular
replacement for the false global periodicity assertion. -/
theorem natCast_cfzWTrickedLinearValue_eq_carryBlockAffineResidue_of_not_bad
    {k N M D : ℕ} [NeZero N] [NeZero M]
    (hD : 0 < D) (W b : ℕ)
    (q : CFZFormIndex k)
    {x : CFZVariable k → ℕ}
    (hx : x ∈ natBox (fun _ : CFZVariable k => N))
    (hgood : ¬CFZCarryBadPoint (N := N) D q x) :
    (cfzWTrickedLinearValue W b q
        (cubePointOfNat (N := N) x) : ZMod M) =
      (cfzCarryBlockAffineResidueValue
        (N := N) (M := M) D W b q x : ZMod M) := by
  rw [natCast_cfzCarryBlockAffineResidueValue]
  rw [cfzCarry_quotientBlockBase_eq_of_not_bad
    hD q hx hgood]
  calc
    (cfzWTrickedLinearValue W b q
        (cubePointOfNat (N := N) x) : ZMod M) =
        (((cfzCarryAdjustedAffineForm N W b q
          (cfzCarry (N := N) q x)).eval
          (fun v => (x v : ℤ)) : ℤ) : ZMod M) := by
      simpa only [Int.cast_natCast] using
        congrArg (fun n : ℤ => (n : ZMod M))
          (cfzCarryAdjustedAffineForm_eval_canonicalCarry
            (N := N) W b q x).symm
    _ =
        (cfzCarryAdjustedAffineForm N W b q
          (cfzCarry (N := N) q x)).evalZMod M
          (fun v => (x v : ZMod M)) := by
      simpa only [Int.cast_natCast] using
        AffineForm.intCast_eval_eq_evalZMod M
          (cfzCarryAdjustedAffineForm N W b q
            (cfzCarry (N := N) q x))
          (fun v => (x v : ℤ))

/-- Pointwise paired-indicator equality with the carry-dependent exact
affine residue model modulo the global paired LCM. -/
theorem pairedDivisibilityIndicator_cfz_eq_carryBlockAffineResidue_of_not_bad
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N D : ℕ} [NeZero N] (hD : 0 < D)
    (W b : ℕ) (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    {x : CFZVariable k → ℕ}
    (hx : x ∈ natBox (fun _ : CFZVariable k => N))
    (hgood :
      x ∉ cfzFamilyCarryBadPoints (N := N) D forms) :
    pairedDivisibilityIndicator
        (fun q y =>
          cfzWTrickedLinearValue W b (forms q)
            (cubePointOfNat (N := N) y))
        z x =
      pairedDivisibilityIndicator
        (fun q y =>
          cfzCarryBlockAffineResidueValue
            (N := N) (M := pairedDivisorLcm z)
            D W b (forms q) y)
        z x := by
  unfold pairedDivisibilityIndicator
  apply Finset.prod_congr rfl
  intro q _hq
  have hqgood :
      ¬CFZCarryBadPoint (N := N) D (forms q) x := by
    intro hbad
    apply hgood
    apply Finset.mem_biUnion.mpr
    exact
      ⟨q, Finset.mem_univ q,
        mem_cfzCarryBadPoints.mpr hbad⟩
  have hvalue :
      (cfzWTrickedLinearValue W b (forms q)
          (cubePointOfNat (N := N) x) :
            ZMod (pairedDivisorLcm z)) =
        (cfzCarryBlockAffineResidueValue
          (N := N) (M := pairedDivisorLcm z)
          D W b (forms q) x :
            ZMod (pairedDivisorLcm z)) :=
    natCast_cfzWTrickedLinearValue_eq_carryBlockAffineResidue_of_not_bad
      hD W b (forms q) hx hqgood
  change
    natDivisibilityIndicator (z q).1
          (cfzWTrickedLinearValue W b (forms q)
            (cubePointOfNat (N := N) x)) *
        natDivisibilityIndicator (z q).2
          (cfzWTrickedLinearValue W b (forms q)
            (cubePointOfNat (N := N) x)) =
      natDivisibilityIndicator (z q).1
          (cfzCarryBlockAffineResidueValue
            (N := N) (M := pairedDivisorLcm z)
            D W b (forms q) x) *
        natDivisibilityIndicator (z q).2
          (cfzCarryBlockAffineResidueValue
            (N := N) (M := pairedDivisorLcm z)
            D W b (forms q) x)
  rw [natDivisibilityIndicator_eq_of_cast_eq_of_dvd
      (pairedDivisor_left_dvd_lcm z q) hvalue,
    natDivisibilityIndicator_eq_of_cast_eq_of_dvd
      (pairedDivisor_right_dvd_lcm z q) hvalue]

/-- Global carry-dependent exact affine residue model.  Each good quotient
block uses one fixed vector of affine constants; those constants may vary
between blocks, which is harmless for constant-insensitive good-prime Euler
estimates. -/
noncomputable def cfzCarryBlockPairedResidueModelDensity
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (D W b : ℕ) (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)] : ℝ :=
  boxMean (fun _ : CFZVariable k => N)
    (pairedDivisibilityIndicator
      (fun q x =>
        cfzCarryBlockAffineResidueValue
          (N := N) (M := pairedDivisorLcm z)
          D W b (forms q) x)
      z)

/-- **Unconditional cyclic-to-residue bridge.**

The cyclic paired density differs from the carry-dependent exact affine
residue model only on carry-bad blocks.  This is the sound entry point for
blockwise Euler-product estimates: no assumption `pairedDivisorLcm z ∣ W*N`
is present.
-/
theorem abs_pairedDivisibilityDensity_cfz_sub_carryBlockResidueModel_le_bad
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N D : ℕ} [NeZero N] (hD : 0 < D)
    (W b : ℕ) (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)] :
    |pairedDivisibilityDensity
        (fun q (x : CubePoint k N) =>
          cfzWTrickedLinearValue W b (forms q) x)
        z -
      cfzCarryBlockPairedResidueModelDensity
        (N := N) D W b forms z| ≤
      ((cfzFamilyCarryBadPoints
        (N := N) D forms).card : ℝ) /
        (N : ℝ) ^ Fintype.card (CFZVariable k) := by
  let F : (CFZVariable k → ℕ) → ℝ :=
    pairedDivisibilityIndicator
      (fun q x =>
        cfzWTrickedLinearValue W b (forms q)
          (cubePointOfNat (N := N) x))
      z
  let G : (CFZVariable k → ℕ) → ℝ :=
    pairedDivisibilityIndicator
      (fun q x =>
        cfzCarryBlockAffineResidueValue
          (N := N) (M := pairedDivisorLcm z)
          D W b (forms q) x)
      z
  have hactual :
      pairedDivisibilityDensity
          (fun q (x : CubePoint k N) =>
            cfzWTrickedLinearValue W b (forms q) x)
          z =
        boxMean (fun _ : CFZVariable k => N) F := by
    unfold pairedDivisibilityDensity
    exact mean_cubePoint_eq_boxMean _
  have hmodel :
      cfzCarryBlockPairedResidueModelDensity
          (N := N) D W b forms z =
        boxMean (fun _ : CFZVariable k => N) G := by
    rfl
  rw [hactual, hmodel]
  have hbox :=
    abs_boxMean_sub_boxMean_le_bad
      (fun _ : CFZVariable k => N)
      (cfzFamilyCarryBadPoints (N := N) D forms)
      F G
      (fun x hx => by
        obtain ⟨q, _hq, hxq⟩ :=
          Finset.mem_biUnion.mp hx
        exact (mem_cfzCarryBadPoints.mp hxq).1)
      (fun x hx hgood =>
        pairedDivisibilityIndicator_cfz_eq_carryBlockAffineResidue_of_not_bad
          hD W b forms z hx hgood)
      (fun x _hx =>
        abs_pairedDivisibilityIndicator_sub_le_one
          (fun q y =>
            cfzWTrickedLinearValue W b (forms q)
              (cubePointOfNat (N := N) y))
          (fun q y =>
            cfzCarryBlockAffineResidueValue
              (N := N) (M := pairedDivisorLcm z)
              D W b (forms q) y)
          z x)
  simpa only [Finset.prod_const, Finset.card_univ] using hbox

/-- Explicit `O_{k,|κ|}(D/N)` form of the unconditional cyclic-to-residue
bridge. -/
theorem abs_pairedDivisibilityDensity_cfz_sub_carryBlockResidueModel_le_linear
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N D : ℕ} [NeZero N]
    (hk : 2 ≤ k) (hD : 0 < D)
    (W b : ℕ) (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)] :
    |pairedDivisibilityDensity
        (fun q (x : CubePoint k N) =>
          cfzWTrickedLinearValue W b (forms q) x)
        z -
      cfzCarryBlockPairedResidueModelDensity
        (N := N) D W b forms z| ≤
      (Fintype.card κ : ℝ) *
        (2 * cfzCarryRange k + 1) *
        (2 * Fintype.card (CFZVariable k) * k + 1) *
        D * (N : ℝ) ^
          (Fintype.card (CFZVariable k) - 1) /
        (N : ℝ) ^ Fintype.card (CFZVariable k) := by
  have hbridge :=
    abs_pairedDivisibilityDensity_cfz_sub_carryBlockResidueModel_le_bad
      (N := N) hD W b forms z
  have hbad :=
    card_cfzFamilyCarryBadPoints_le_linear
      (N := N) hk hD forms
  calc
    |pairedDivisibilityDensity
        (fun q (x : CubePoint k N) =>
          cfzWTrickedLinearValue W b (forms q) x)
        z -
      cfzCarryBlockPairedResidueModelDensity
        (N := N) D W b forms z| ≤
        ((cfzFamilyCarryBadPoints
          (N := N) D forms).card : ℝ) /
          (N : ℝ) ^ Fintype.card (CFZVariable k) :=
      hbridge
    _ ≤
        ((Fintype.card κ *
          ((2 * cfzCarryRange k + 1) *
            (2 * Fintype.card (CFZVariable k) * k + 1) *
            D * N ^ (Fintype.card (CFZVariable k) - 1)) : ℕ) : ℝ) /
          (N : ℝ) ^ Fintype.card (CFZVariable k) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast hbad
      · positivity
    _ =
        (Fintype.card κ : ℝ) *
          (2 * cfzCarryRange k + 1) *
          (2 * Fintype.card (CFZVariable k) * k + 1) *
          D * (N : ℝ) ^
            (Fintype.card (CFZVariable k) - 1) /
          (N : ℝ) ^ Fintype.card (CFZVariable k) := by
      push_cast
      ring

end Wikipedia.SzemeredisTheorem
