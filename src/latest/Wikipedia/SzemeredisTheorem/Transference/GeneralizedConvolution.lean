import Wikipedia.SzemeredisTheorem.Transference.CutDiscrepancy

/-!
# Generalized convolutions on finite additive groups

For positive arity, the generalized convolution is the normalized average of
a weight over a fiber of the coordinate-sum map. At arity zero the sum map
has only the value zero, so the fiber density is a scaled delta function.
Keeping this scaling makes the pairing identity valid without an arity
exception; the `[0,1]` range statement is correctly restricted to positive
arity.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- The tuple with prescribed coordinate sum `z` and prescribed tail `y`.
The zeroth coordinate is the unique value making the total sum equal `z`. -/
def sumFiberTuple {G : Type*} [AddCommGroup G]
    (n : ℕ) (z : G) (y : Fin n → G) : Fin (n + 1) → G :=
  Fin.cons (z - ∑ i, y i) y

@[simp]
theorem sumFiberTuple_zero {G : Type*} [AddCommGroup G]
    (n : ℕ) (z : G) (y : Fin n → G) :
    sumFiberTuple n z y 0 = z - ∑ i, y i :=
  rfl

@[simp]
theorem sumFiberTuple_succ {G : Type*} [AddCommGroup G]
    (n : ℕ) (z : G) (y : Fin n → G) (i : Fin n) :
    sumFiberTuple n z y i.succ = y i :=
  rfl

@[simp]
theorem sum_sumFiberTuple {G : Type*} [AddCommGroup G]
    (n : ℕ) (z : G) (y : Fin n → G) :
    ∑ i, sumFiberTuple n z y i = z := by
  simp [sumFiberTuple, Fin.sum_univ_succ]

/-- Splitting a nonempty tuple into its coordinate sum and its tail is an
equivalence. -/
def sumFiberEquiv (G : Type*) [AddCommGroup G] (n : ℕ) :
    (Fin (n + 1) → G) ≃ G × (Fin n → G) where
  toFun x := (∑ i, x i, Fin.tail x)
  invFun p := sumFiberTuple n p.1 p.2
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (∑ k, x k) - ∑ j, Fin.tail x j = x 0
      rw [Fin.sum_univ_succ]
      change x 0 + (∑ j : Fin n, x j.succ) -
        ∑ j : Fin n, x j.succ = x 0
      abel
    · rfl
  right_inv p := by
    apply Prod.ext
    · exact sum_sumFiberTuple n p.1 p.2
    · funext j
      rfl

/-- The density, relative to uniform measure on `G`, of the only nonempty
fiber of the zero-coordinate sum map. It equals `|G|` at zero and vanishes
elsewhere. -/
noncomputable def zeroFiberDelta
    {G : Type*} [Fintype G] [AddCommGroup G] (z : G) : ℝ := by
  classical
  exact if z = 0 then (Fintype.card G : ℝ) else 0

@[simp]
theorem zeroFiberDelta_zero
    {G : Type*} [Fintype G] [AddCommGroup G] :
    zeroFiberDelta (G := G) 0 = Fintype.card G := by
  classical
  simp [zeroFiberDelta]

@[simp]
theorem zeroFiberDelta_of_ne
    {G : Type*} [Fintype G] [AddCommGroup G]
    {z : G} (hz : z ≠ 0) :
    zeroFiberDelta z = 0 := by
  classical
  simp [zeroFiberDelta, hz]

theorem zeroFiberDelta_nonneg
    {G : Type*} [Fintype G] [AddCommGroup G] (z : G) :
    0 ≤ zeroFiberDelta z := by
  classical
  simp only [zeroFiberDelta]
  split_ifs
  · positivity
  · exact le_rfl

/-- The normalized fiber convolution of an arbitrary tuple weight.

For `r = n + 1`, this is the average of `w` on the fiber with sum `z`,
parametrized by `sumFiberTuple`. For `r = 0`, the scaled delta convention
preserves the exact disintegration identity. -/
noncomputable def fiberConvolution
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (w : (Fin r → G) → ℝ) (z : G) : ℝ := by
  cases r with
  | zero =>
      exact zeroFiberDelta z * w (fun i => Fin.elim0 i)
  | succ n =>
      exact mean fun y : Fin n → G => w (sumFiberTuple n z y)

@[simp]
theorem fiberConvolution_arity_zero
    {G : Type*} [Fintype G] [AddCommGroup G]
    (w : (Fin 0 → G) → ℝ) (z : G) :
    fiberConvolution 0 w z =
      zeroFiberDelta z * w (fun i => Fin.elim0 i) :=
  rfl

@[simp]
theorem fiberConvolution_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (w : (Fin (n + 1) → G) → ℝ) (z : G) :
    fiberConvolution (n + 1) w z =
      mean fun y : Fin n → G => w (sumFiberTuple n z y) :=
  rfl

/-- The product weight associated to a family of deleted-coordinate tests. -/
def cutTestProduct {G : Type*} {r : ℕ}
    (u : CutTestFamily G r) (x : Fin r → G) : ℝ :=
  ∏ i, u i (eraseCoordinate i x)

@[simp]
theorem cutTestProduct_one {G : Type*} {r : ℕ} (x : Fin r → G) :
    cutTestProduct
      (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ)) x = 1 := by
  simp [cutTestProduct]

theorem cutTestProduct_nonneg
    {G : Type*} {r : ℕ} {u : CutTestFamily G r}
    (hu : IsBoundedCutTest u) (x : Fin r → G) :
    0 ≤ cutTestProduct u x :=
  Finset.prod_nonneg fun i _ => hu.nonneg i (eraseCoordinate i x)

theorem cutTestProduct_le_one
    {G : Type*} {r : ℕ} {u : CutTestFamily G r}
    (hu : IsBoundedCutTest u) (x : Fin r → G) :
    cutTestProduct u x ≤ 1 :=
  Finset.prod_le_one
    (fun i _ => hu.nonneg i (eraseCoordinate i x))
    (fun i _ => hu.le_one i (eraseCoordinate i x))

theorem cutTestProduct_mem_Icc
    {G : Type*} {r : ℕ} {u : CutTestFamily G r}
    (hu : IsBoundedCutTest u) (x : Fin r → G) :
    cutTestProduct u x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨cutTestProduct_nonneg hu x, cutTestProduct_le_one hu x⟩

@[simp]
theorem cutTestProduct_mul
    {G : Type*} {r : ℕ} (u v : CutTestFamily G r)
    (x : Fin r → G) :
    cutTestProduct (fun i y => u i y * v i y) x =
      cutTestProduct u x * cutTestProduct v x := by
  simp [cutTestProduct, Finset.prod_mul_distrib]

/-- The generalized convolution attached to a family of cut tests. -/
noncomputable def generalizedConvolution
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (u : CutTestFamily G r) (z : G) : ℝ :=
  fiberConvolution r (cutTestProduct u) z

@[simp]
theorem generalizedConvolution_arity_zero
    {G : Type*} [Fintype G] [AddCommGroup G]
    (u : CutTestFamily G 0) (z : G) :
    generalizedConvolution 0 u z = zeroFiberDelta z := by
  simp [generalizedConvolution, cutTestProduct]

@[simp]
theorem generalizedConvolution_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (u : CutTestFamily G (n + 1)) (z : G) :
    generalizedConvolution (n + 1) u z =
      mean fun y : Fin n → G =>
        cutTestProduct u (sumFiberTuple n z y) :=
  rfl

theorem fiberConvolution_add
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (w v : (Fin r → G) → ℝ) (z : G) :
    fiberConvolution r (w + v) z =
      fiberConvolution r w z + fiberConvolution r v z := by
  cases r with
  | zero =>
      rw [fiberConvolution_arity_zero, fiberConvolution_arity_zero,
        fiberConvolution_arity_zero]
      simp [mul_add]
  | succ n =>
      rw [fiberConvolution_succ, fiberConvolution_succ,
        fiberConvolution_succ]
      exact mean_add
        (fun y : Fin n → G => w (sumFiberTuple n z y))
        (fun y : Fin n → G => v (sumFiberTuple n z y))

theorem fiberConvolution_smul
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (c : ℝ) (w : (Fin r → G) → ℝ) (z : G) :
    fiberConvolution r (fun x => c * w x) z =
      c * fiberConvolution r w z := by
  cases r with
  | zero =>
      rw [fiberConvolution_arity_zero, fiberConvolution_arity_zero]
      ring
  | succ n =>
      rw [fiberConvolution_succ, fiberConvolution_succ]
      exact mean_smul c (fun y : Fin n → G =>
        w (sumFiberTuple n z y))

@[simp]
theorem fiberConvolution_zero_weight
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (z : G) :
    fiberConvolution r (fun _ => (0 : ℝ)) z = 0 := by
  simpa using fiberConvolution_smul r 0 (fun _ => (1 : ℝ)) z

@[simp]
theorem fiberConvolution_const_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (c : ℝ) (z : G) :
    fiberConvolution (n + 1) (fun _ => c) z = c := by
  rw [fiberConvolution_succ]
  exact mean_const c

theorem fiberConvolution_linearCombination
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (a b : ℝ) (w v : (Fin r → G) → ℝ) (z : G) :
    fiberConvolution r (fun x => a * w x + b * v x) z =
      a * fiberConvolution r w z + b * fiberConvolution r v z := by
  change fiberConvolution r
    ((fun x => a * w x) + (fun x => b * v x)) z = _
  rw [fiberConvolution_add, fiberConvolution_smul,
    fiberConvolution_smul]

theorem fiberConvolution_nonneg_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    {n : ℕ} {w : (Fin (n + 1) → G) → ℝ}
    (hw : ∀ x, 0 ≤ w x) (z : G) :
    0 ≤ fiberConvolution (n + 1) w z := by
  rw [fiberConvolution_succ]
  exact mean_nonneg fun y => hw (sumFiberTuple n z y)

theorem fiberConvolution_le_one_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    {n : ℕ} {w : (Fin (n + 1) → G) → ℝ}
    (hw : ∀ x, w x ≤ 1) (z : G) :
    fiberConvolution (n + 1) w z ≤ 1 := by
  rw [fiberConvolution_succ]
  exact mean_le_of_le_const fun y => hw (sumFiberTuple n z y)

theorem fiberConvolution_mono_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    {n : ℕ} {w v : (Fin (n + 1) → G) → ℝ}
    (hwv : ∀ x, w x ≤ v x) (z : G) :
    fiberConvolution (n + 1) w z ≤ fiberConvolution (n + 1) v z := by
  rw [fiberConvolution_succ, fiberConvolution_succ]
  exact mean_mono fun y => hwv (sumFiberTuple n z y)

theorem generalizedConvolution_nonneg_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    {n : ℕ} {u : CutTestFamily G (n + 1)}
    (hu : IsBoundedCutTest u) (z : G) :
    0 ≤ generalizedConvolution (n + 1) u z :=
  fiberConvolution_nonneg_succ (cutTestProduct_nonneg hu) z

theorem generalizedConvolution_le_one_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    {n : ℕ} {u : CutTestFamily G (n + 1)}
    (hu : IsBoundedCutTest u) (z : G) :
    generalizedConvolution (n + 1) u z ≤ 1 :=
  fiberConvolution_le_one_succ (cutTestProduct_le_one hu) z

theorem generalizedConvolution_mem_Icc
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} (hr : 0 < r) {u : CutTestFamily G r}
    (hu : IsBoundedCutTest u) (z : G) :
    generalizedConvolution r u z ∈ Set.Icc (0 : ℝ) 1 := by
  cases r with
  | zero => simp at hr
  | succ n =>
      exact ⟨generalizedConvolution_nonneg_succ hu z,
        generalizedConvolution_le_one_succ hu z⟩

theorem generalizedConvolution_nonneg
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} (hr : 0 < r) {u : CutTestFamily G r}
    (hu : IsBoundedCutTest u) (z : G) :
    0 ≤ generalizedConvolution r u z :=
  (generalizedConvolution_mem_Icc hr hu z).1

theorem generalizedConvolution_le_one
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} (hr : 0 < r) {u : CutTestFamily G r}
    (hu : IsBoundedCutTest u) (z : G) :
    generalizedConvolution r u z ≤ 1 :=
  (generalizedConvolution_mem_Icc hr hu z).2

@[simp]
theorem generalizedConvolution_one_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (z : G) :
    generalizedConvolution (n + 1)
      (fun _ : Fin (n + 1) => fun _ : Fin n → G => (1 : ℝ)) z = 1 := by
  rw [generalizedConvolution_succ]
  calc
    mean (fun y : Fin n → G =>
        cutTestProduct
          (fun _ : Fin (n + 1) => fun _ : Fin n → G => (1 : ℝ))
          (sumFiberTuple n z y)) =
        mean (fun _ : Fin n → G => (1 : ℝ)) := by
      apply congrArg mean
      funext y
      exact cutTestProduct_one (sumFiberTuple n z y)
    _ = 1 := mean_const 1

@[simp]
theorem generalizedConvolution_zero_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (z : G) :
    generalizedConvolution (n + 1)
      (fun _ : Fin (n + 1) => fun _ : Fin n → G => (0 : ℝ)) z = 0 := by
  rw [generalizedConvolution_succ]
  simp [cutTestProduct]

/-- Disintegration over the zero-coordinate sum map. -/
theorem fiberConvolution_pairing_zero
    {G : Type*} [Fintype G] [AddCommGroup G]
    (w : (Fin 0 → G) → ℝ) (h : G → ℝ) :
    mean (fun x : Fin 0 → G => h (∑ i, x i) * w x) =
      mean (fun z : G => h z * fiberConvolution 0 w z) := by
  classical
  let e : Fin 0 → G := fun i => Fin.elim0 i
  calc
    mean (fun x : Fin 0 → G => h (∑ i, x i) * w x) =
        h 0 * w e := by
      have heq :
          (fun x : Fin 0 → G => h (∑ i, x i) * w x) =
            (fun _ : Fin 0 → G => h 0 * w e) := by
        funext x
        have hx : x = e := Subsingleton.elim _ _
        subst x
        simp [e]
      rw [heq]
      exact mean_const _
    _ = mean (fun z : G => h z * fiberConvolution 0 w z) := by
      rw [mean, Fintype.expect_eq_sum_div_card]
      simp [fiberConvolution_arity_zero, zeroFiberDelta, e]
      field_simp

/-- Disintegration over the coordinate-sum map at positive arity. -/
theorem fiberConvolution_pairing_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (w : (Fin (n + 1) → G) → ℝ) (h : G → ℝ) :
    mean (fun x : Fin (n + 1) → G => h (∑ i, x i) * w x) =
      mean (fun z : G => h z * fiberConvolution (n + 1) w z) := by
  calc
    mean (fun x : Fin (n + 1) → G => h (∑ i, x i) * w x) =
        mean (fun p : G × (Fin n → G) =>
          h p.1 * w (sumFiberTuple n p.1 p.2)) := by
      unfold mean
      apply Fintype.expect_equiv (sumFiberEquiv G n)
      intro x
      change h (∑ i, x i) * w x =
        h (∑ i, x i) *
          w (sumFiberTuple n (∑ i, x i) (Fin.tail x))
      have hx : sumFiberTuple n (∑ i, x i) (Fin.tail x) = x :=
        (sumFiberEquiv G n).left_inv x
      rw [hx]
    _ = mean₂ (fun z : G => fun y : Fin n → G =>
          h z * w (sumFiberTuple n z y)) := by
      simpa [mean, mean₂] using
        (Finset.expect_product (Finset.univ : Finset G)
          (Finset.univ : Finset (Fin n → G))
          (fun p : G × (Fin n → G) =>
            h p.1 * w (sumFiberTuple n p.1 p.2)))
    _ = mean (fun z : G =>
          h z * mean (fun y : Fin n → G =>
            w (sumFiberTuple n z y))) := by
      apply congrArg mean
      funext z
      exact mean_smul (h z) _
    _ = mean (fun z : G =>
          h z * fiberConvolution (n + 1) w z) := by
      rfl

/-- Exact disintegration over the coordinate-sum map, including arity zero. -/
theorem fiberConvolution_pairing
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (w : (Fin r → G) → ℝ) (h : G → ℝ) :
    mean (fun x : Fin r → G => h (∑ i, x i) * w x) =
      mean (fun z : G => h z * fiberConvolution r w z) := by
  cases r with
  | zero => exact fiberConvolution_pairing_zero w h
  | succ n => exact fiberConvolution_pairing_succ n w h

theorem mean_fiberConvolution
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (w : (Fin r → G) → ℝ) :
    mean (fiberConvolution r w) = mean w := by
  have hpair := fiberConvolution_pairing r w (fun _ : G => (1 : ℝ))
  simpa using hpair.symm

theorem mean_generalizedConvolution
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (u : CutTestFamily G r) :
    mean (generalizedConvolution r u) = mean (cutTestProduct u) :=
  mean_fiberConvolution r (cutTestProduct u)

/-- A cut correlation is exactly the pairing of `f-g` with its generalized
convolution. -/
theorem cutCorrelation_eq_mean_mul_generalizedConvolution
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) (u : CutTestFamily G r) :
    cutCorrelation r f g u =
      mean (fun z : G =>
        (f z - g z) * generalizedConvolution r u z) := by
  exact fiberConvolution_pairing r (cutTestProduct u)
    (fun z => f z - g z)

end Wikipedia.SzemeredisTheorem
