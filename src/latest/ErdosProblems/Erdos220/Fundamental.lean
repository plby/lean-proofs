import Mathlib

/-!
# The finite Cauchy inequality used in the Montgomery--Vaughan argument

This file contains a division-free formulation of the prime-local
Cauchy--Schwarz estimate which is iterated, through the Chinese remainder
theorem, in the Montgomery--Vaughan fundamental lemma.  The squared form is
particularly convenient for moment calculations: for six functions on
`ZMod p`, a single linear congruence costs exactly `p ^ 4`.
-/

open scoped BigOperators

namespace Erdos220

section FiniteCauchy

variable {S A B : Type*} [Fintype S] [Fintype A] [Fintype B]

/-- Cauchy--Schwarz for a finite sum whose two coordinate maps are injective.

This is the form needed after solving a CRT coordinate: the solution set of
one nondegenerate equation maps injectively to either of the two variables.
-/
theorem norm_sum_mul_sq_le_of_injective
    (x : S → A) (y : S → B) (hx : Function.Injective x)
    (hy : Function.Injective y) (f : A → ℂ) (g : B → ℂ) :
    ‖∑ s, f (x s) * g (y s)‖ ^ 2 ≤
      (∑ a, ‖f a‖ ^ 2) * ∑ b, ‖g b‖ ^ 2 := by
  classical
  calc
    ‖∑ s, f (x s) * g (y s)‖ ^ 2
        ≤ (∑ s, ‖f (x s) * g (y s)‖) ^ 2 := by
          gcongr
          exact norm_sum_le _ _
    _ = (∑ s, ‖f (x s)‖ * ‖g (y s)‖) ^ 2 := by
          simp_rw [norm_mul]
    _ ≤ (∑ s, ‖f (x s)‖ ^ 2) * ∑ s, ‖g (y s)‖ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
    _ ≤ (∑ a, ‖f a‖ ^ 2) * ∑ b, ‖g b‖ ^ 2 := by
          gcongr
          · rw [← Finset.sum_image (s := Finset.univ) (f := fun a ↦ ‖f a‖ ^ 2)
              hx.injOn]
            exact Finset.sum_le_univ_sum_of_nonneg (fun _ ↦ sq_nonneg _)
          · rw [← Finset.sum_image (s := Finset.univ) (f := fun b ↦ ‖g b‖ ^ 2)
              hy.injOn]
            exact Finset.sum_le_univ_sum_of_nonneg (fun _ ↦ sq_nonneg _)

end FiniteCauchy

section OnePrime

variable {p : ℕ} [NeZero p]

/-- The solutions of a two-variable affine equation modulo `p`. -/
def affineSolution (u v : (ZMod p)ˣ) (c : ZMod p) :=
  {z : ZMod p × ZMod p // u.1 * z.1 + v.1 * z.2 = c}

noncomputable instance (u v : (ZMod p)ˣ) (c : ZMod p) :
    Fintype (affineSolution u v c) := by
  classical
  unfold affineSolution
  infer_instance

private theorem affineSolution_fst_injective (u v : (ZMod p)ˣ) (c : ZMod p) :
    Function.Injective (fun z : affineSolution u v c ↦ z.1.1) := by
  intro z z' hz
  apply Subtype.ext
  change z.1.1 = z'.1.1 at hz
  apply Prod.ext hz
  have hv : v.1 * z.1.2 = v.1 * z'.1.2 := by
    have hz1 : v.1 * z.1.2 = c - u.1 * z.1.1 := by
      linear_combination z.2
    have hz2 : v.1 * z'.1.2 = c - u.1 * z'.1.1 := by
      linear_combination z'.2
    rw [hz1, hz2, hz]
  calc
    z.1.2 = v⁻¹.1 * (v.1 * z.1.2) := by simp
    _ = v⁻¹.1 * (v.1 * z'.1.2) := by rw [hv]
    _ = z'.1.2 := by simp

private theorem affineSolution_snd_injective (u v : (ZMod p)ˣ) (c : ZMod p) :
    Function.Injective (fun z : affineSolution u v c ↦ z.1.2) := by
  intro z z' hz
  apply Subtype.ext
  change z.1.2 = z'.1.2 at hz
  apply Prod.ext
  · have hu : u.1 * z.1.1 = u.1 * z'.1.1 := by
      have hz1 : u.1 * z.1.1 = c - v.1 * z.1.2 := by
        linear_combination z.2
      have hz2 : u.1 * z'.1.1 = c - v.1 * z'.1.2 := by
        linear_combination z'.2
      rw [hz1, hz2, hz]
    calc
      z.1.1 = u⁻¹.1 * (u.1 * z.1.1) := by simp
      _ = u⁻¹.1 * (u.1 * z'.1.1) := by rw [hu]
      _ = z'.1.1 := by simp
  · exact hz

/-- The two-variable, one-prime Cauchy estimate.  No primality assumption is
needed here: it is enough that both coefficients are units. -/
theorem affineSolution_cauchy (u v : (ZMod p)ˣ) (c : ZMod p)
    (f g : ZMod p → ℂ) :
    ‖∑ z : affineSolution u v c, f z.1.1 * g z.1.2‖ ^ 2 ≤
      (∑ a : ZMod p, ‖f a‖ ^ 2) * ∑ b : ZMod p, ‖g b‖ ^ 2 := by
  exact norm_sum_mul_sq_le_of_injective _ _
    (affineSolution_fst_injective u v c)
    (affineSolution_snd_injective u v c) f g

/-! ## Convolution form -/

/-- Unnormalised `L²` norm on a finite residue ring. -/
noncomputable def finiteL2 (f : ZMod p → ℂ) : ℝ :=
  Real.sqrt (∑ x : ZMod p, ‖f x‖ ^ 2)

/-- Unnormalised `L¹` norm on a finite residue ring. -/
noncomputable def finiteL1 (f : ZMod p → ℂ) : ℝ :=
  ∑ x : ZMod p, ‖f x‖

/-- Additive convolution on `ZMod p`. -/
def finiteConv (f g : ZMod p → ℂ) (x : ZMod p) : ℂ :=
  ∑ y : ZMod p, f y * g (x - y)

theorem finiteL2_nonneg (f : ZMod p → ℂ) : 0 ≤ finiteL2 f :=
  Real.sqrt_nonneg _

theorem finiteL2_sq (f : ZMod p → ℂ) :
    finiteL2 f ^ 2 = ∑ x : ZMod p, ‖f x‖ ^ 2 := by
  rw [finiteL2, Real.sq_sqrt]
  positivity

theorem norm_le_finiteL2 (f : ZMod p → ℂ) (x : ZMod p) : ‖f x‖ ≤ finiteL2 f := by
  rw [finiteL2, ← Real.sqrt_sq (norm_nonneg _)]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun y _ ↦ sq_nonneg ‖f y‖) (Finset.mem_univ x))

/-- The endpoint `L² * L² → L∞` convolution inequality. -/
theorem norm_finiteConv_le (f g : ZMod p → ℂ) (x : ZMod p) :
    ‖finiteConv f g x‖ ≤ finiteL2 f * finiteL2 g := by
  calc
    ‖finiteConv f g x‖ ≤ ∑ y : ZMod p, ‖f y * g (x - y)‖ := norm_sum_le _ _
    _ = ∑ y : ZMod p, ‖f y‖ * ‖g (x - y)‖ := by simp_rw [norm_mul]
    _ ≤ Real.sqrt ((∑ y : ZMod p, ‖f y‖ ^ 2) *
        ∑ y : ZMod p, ‖g (x - y)‖ ^ 2) := by
      apply Real.le_sqrt_of_sq_le
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
    _ = finiteL2 f * finiteL2 g := by
      rw [Real.sqrt_mul (by positivity), finiteL2, finiteL2]
      congr 2
      exact Fintype.sum_equiv (Equiv.subLeft x) _ _ (fun _ ↦ rfl)

/-- Convolution with an `L¹` function preserves a pointwise bound. -/
theorem norm_finiteConv_le_of_bound (f g : ZMod p → ℂ) (C : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) (x : ZMod p) :
    ‖finiteConv f g x‖ ≤ C * finiteL1 g := by
  calc
    ‖finiteConv f g x‖ ≤ ∑ y : ZMod p, ‖f y * g (x - y)‖ := norm_sum_le _ _
    _ = ∑ y : ZMod p, ‖f y‖ * ‖g (x - y)‖ := by simp_rw [norm_mul]
    _ ≤ ∑ y : ZMod p, C * ‖g (x - y)‖ := by
      gcongr with y
      exact hC y
    _ = C * finiteL1 g := by
      rw [← Finset.mul_sum]
      congr 1
      exact Fintype.sum_equiv (Equiv.subLeft x) _ _ (fun _ ↦ rfl)

/-- Cauchy--Schwarz in the form `L¹ ≤ sqrt(card) * L²`. -/
theorem finiteL1_le (f : ZMod p → ℂ) :
    finiteL1 f ≤ Real.sqrt p * finiteL2 f := by
  calc
    finiteL1 f ≤ Real.sqrt ((∑ _x : ZMod p, (1 : ℝ) ^ 2) *
        ∑ x : ZMod p, ‖f x‖ ^ 2) := by
      apply Real.le_sqrt_of_sq_le
      simpa [finiteL1] using
        (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : ZMod p ↦ (1 : ℝ))
          (fun x ↦ ‖f x‖))
    _ = Real.sqrt p * finiteL2 f := by
      rw [Real.sqrt_mul (by positivity)]
      simp [finiteL2]

/-- Iterated convolution, with the first function as initial value. -/
def iterConv : (ZMod p → ℂ) → List (ZMod p → ℂ) → ZMod p → ℂ
  | f, [] => f
  | f, g :: gs => iterConv (finiteConv f g) gs

theorem norm_iterConv_le_of_bound (f : ZMod p → ℂ)
    (gs : List (ZMod p → ℂ)) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C)
    (x : ZMod p) :
    ‖iterConv f gs x‖ ≤ C * (gs.map finiteL1).prod := by
  induction gs generalizing f C with
  | nil => simpa [iterConv] using hC x
  | cons g gs ih =>
      simp only [iterConv, List.map_cons, List.prod_cons]
      calc
        ‖iterConv (finiteConv f g) gs x‖ ≤
            (C * finiteL1 g) * (gs.map finiteL1).prod :=
          ih _ _ (norm_finiteConv_le_of_bound f g C hC)
        _ = C * (finiteL1 g * (gs.map finiteL1).prod) := by ring

private theorem prod_finiteL1_nonneg (gs : List (ZMod p → ℂ)) :
    0 ≤ (gs.map finiteL1).prod := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
      simp only [List.map_cons, List.prod_cons]
      exact mul_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) ih

private theorem prod_finiteL2_nonneg (gs : List (ZMod p → ℂ)) :
    0 ≤ (gs.map finiteL2).prod := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
      simp only [List.map_cons, List.prod_cons]
      exact mul_nonneg (finiteL2_nonneg g) ih

private theorem prod_sqrt_nonneg (gs : List (ZMod p → ℂ)) :
    0 ≤ (gs.map fun _ ↦ Real.sqrt p).prod := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
      simp only [List.map_cons, List.prod_cons]
      exact mul_nonneg (Real.sqrt_nonneg _) ih

private theorem prod_finiteL1_le (gs : List (ZMod p → ℂ)) :
    (gs.map finiteL1).prod ≤
      (gs.map fun _ ↦ Real.sqrt p).prod * (gs.map finiteL2).prod := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
      simp only [List.map_cons, List.prod_cons]
      calc
        finiteL1 g * (gs.map finiteL1).prod ≤
            (Real.sqrt p * finiteL2 g) *
              ((gs.map fun _ ↦ Real.sqrt p).prod * (gs.map finiteL2).prod) := by
          exact mul_le_mul (finiteL1_le g) ih (prod_finiteL1_nonneg gs)
            (mul_nonneg (Real.sqrt_nonneg _) (finiteL2_nonneg g))
        _ = (Real.sqrt p * (gs.map fun _ ↦ Real.sqrt p).prod) *
              (finiteL2 g * (gs.map finiteL2).prod) := by ring

/-- The local Montgomery--Vaughan estimate for any number (at least two)
of functions.  For six functions the leading factor is `(sqrt p)^4`. -/
theorem norm_iterConv_le (f g : ZMod p → ℂ) (gs : List (ZMod p → ℂ))
    (x : ZMod p) :
    ‖iterConv f (g :: gs) x‖ ≤
      finiteL2 f * finiteL2 g *
        ((gs.map fun _ ↦ Real.sqrt p).prod * (gs.map finiteL2).prod) := by
  simp only [iterConv]
  calc
    ‖iterConv (finiteConv f g) gs x‖ ≤
        (finiteL2 f * finiteL2 g) * (gs.map finiteL1).prod :=
      norm_iterConv_le_of_bound _ _ _ (norm_finiteConv_le f g) x
    _ ≤ finiteL2 f * finiteL2 g *
        ((gs.map fun _ ↦ Real.sqrt p).prod * (gs.map finiteL2).prod) := by
      exact mul_le_mul_of_nonneg_left (prod_finiteL1_le gs)
        (mul_nonneg (finiteL2_nonneg f) (finiteL2_nonneg g))

/-- Six-function, division-free form of the prime-local fundamental
inequality.  This is the exact `p⁴` factor used in the sixth moment. -/
theorem norm_iterConv_six_sq (f₀ f₁ f₂ f₃ f₄ f₅ : ZMod p → ℂ)
    (x : ZMod p) :
    ‖iterConv f₀ [f₁, f₂, f₃, f₄, f₅] x‖ ^ 2 ≤
      (p : ℝ) ^ 4 *
        ((∑ a, ‖f₀ a‖ ^ 2) * (∑ a, ‖f₁ a‖ ^ 2) *
         (∑ a, ‖f₂ a‖ ^ 2) * (∑ a, ‖f₃ a‖ ^ 2) *
         (∑ a, ‖f₄ a‖ ^ 2) * (∑ a, ‖f₅ a‖ ^ 2)) := by
  have h := norm_iterConv_le f₀ f₁ [f₂, f₃, f₄, f₅] x
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  have hs : (Real.sqrt (p : ℝ)) ^ 2 = p := Real.sq_sqrt (by positivity)
  have hsq :
      ‖iterConv f₀ [f₁, f₂, f₃, f₄, f₅] x‖ ^ 2 ≤
        (finiteL2 f₀ * finiteL2 f₁ *
          (Real.sqrt p * (Real.sqrt p * (Real.sqrt p * (Real.sqrt p * 1))) *
            (finiteL2 f₂ * (finiteL2 f₃ * (finiteL2 f₄ * (finiteL2 f₅ * 1)))))) ^ 2 := by
    nlinarith [norm_nonneg (iterConv f₀ [f₁, f₂, f₃, f₄, f₅] x),
      finiteL2_nonneg f₀, finiteL2_nonneg f₁, finiteL2_nonneg f₂,
      finiteL2_nonneg f₃, finiteL2_nonneg f₄, finiteL2_nonneg f₅,
      Real.sqrt_nonneg (p : ℝ)]
  calc
    _ ≤ (finiteL2 f₀ * finiteL2 f₁ *
          (Real.sqrt p * (Real.sqrt p * (Real.sqrt p * (Real.sqrt p * 1))) *
            (finiteL2 f₂ * (finiteL2 f₃ * (finiteL2 f₄ * (finiteL2 f₅ * 1)))))) ^ 2 :=
      hsq
    _ = _ := by
      simp only [mul_pow, one_pow, finiteL2_sq, hs]
      ring

end OnePrime

/-! ## Tensor-product / CRT iteration

`FundamentalCoordinate` packages one CRT coordinate together with its
prime-local Cauchy estimate.  `FundamentalSystem` forms finite products of
such coordinates.  Unlike a hypothesis asserting the desired global
estimate, the only analytic datum in a coordinate is the one-coordinate
operator bound proved above; the theorem below proves that these local
bounds tensorise even when each of the six functions couples all of its CRT
coordinates.
-/

structure FundamentalCoordinate where
  State : Type
  stateFintype : Fintype State
  Value : Fin 6 → Type
  valueFintype : ∀ i, Fintype (Value i)
  project : ∀ i, State → Value i
  scale : ℝ
  scale_nonneg : 0 ≤ scale
  localBound : ∀ (f : ∀ i, Value i → ℂ),
    ‖stateFintype.elems.sum (fun s ↦ ∏ i, f i (project i s))‖ ≤
      scale * ∏ i, Real.sqrt ((valueFintype i).elems.sum (fun x ↦ ‖f i x‖ ^ 2))

/-- The coordinate inequality with the stored finite enumerations exposed as
ordinary `Fintype` sums. -/
theorem FundamentalCoordinate.localBound_univ (c : FundamentalCoordinate)
    (f : ∀ i, c.Value i → ℂ) :
    letI : Fintype c.State := c.stateFintype
    letI (i : Fin 6) : Fintype (c.Value i) := c.valueFintype i
    ‖∑ s : c.State, ∏ i, f i (c.project i s)‖ ≤
      c.scale * ∏ i, Real.sqrt (∑ x : c.Value i, ‖f i x‖ ^ 2) := by
  letI : Fintype c.State := c.stateFintype
  letI (i : Fin 6) : Fintype (c.Value i) := c.valueFintype i
  have h := c.localBound f
  rw [show c.stateFintype.elems = Finset.univ by
    ext x
    constructor
    · intro hx
      simp
    · intro hx
      exact c.stateFintype.complete x] at h
  simp_rw [show ∀ i, (c.valueFintype i).elems = Finset.univ by
    intro i
    ext x
    constructor
    · intro hx
      simp
    · intro hx
      exact (c.valueFintype i).complete x] at h
  exact h

/-- The local estimate after replacing the stored enumerations by specified
extensionally equal finite enumerations. -/
theorem FundamentalCoordinate.localBound_with (c : FundamentalCoordinate)
    (stateFintype : Fintype c.State)
    (valueFintype : ∀ i, Fintype (c.Value i))
    (f : ∀ i, c.Value i → ℂ) :
    letI : Fintype c.State := stateFintype
    letI (i : Fin 6) : Fintype (c.Value i) := valueFintype i
    ‖∑ s : c.State, ∏ i, f i (c.project i s)‖ ≤
      c.scale * ∏ i, Real.sqrt (∑ x : c.Value i, ‖f i x‖ ^ 2) := by
  letI : Fintype c.State := stateFintype
  letI (i : Fin 6) : Fintype (c.Value i) := valueFintype i
  have h := c.localBound f
  rw [show c.stateFintype.elems = stateFintype.elems by
    ext x
    constructor
    · intro hx
      exact stateFintype.complete x
    · intro hx
      exact c.stateFintype.complete x] at h
  simp_rw [show ∀ i, (c.valueFintype i).elems = (valueFintype i).elems by
    intro i
    ext x
    constructor
    · intro hx
      exact (valueFintype i).complete x
    · intro hx
      exact (c.valueFintype i).complete x] at h
  exact h

inductive FundamentalSystem
  | nil
  | cons (head : FundamentalCoordinate) (tail : FundamentalSystem)

namespace FundamentalSystem

@[reducible] def State : FundamentalSystem → Type
  | nil => Unit
  | cons c t => c.State × State t

@[reducible] def Value : FundamentalSystem → Fin 6 → Type
  | nil, _ => Unit
  | cons c t, i => c.Value i × Value t i

@[reducible] noncomputable def stateElements : (t : FundamentalSystem) → Finset t.State
  | nil => {()}
  | cons c t => c.stateFintype.elems ×ˢ t.stateElements

@[reducible] noncomputable def valueElements : (t : FundamentalSystem) → ∀ i,
    Finset (t.Value i)
  | nil, _ => {()}
  | cons c t, i => (c.valueFintype i).elems ×ˢ t.valueElements i

@[reducible] def project : (t : FundamentalSystem) → ∀ i, t.State → t.Value i
  | nil, _, _ => ()
  | cons c t, i, s => (c.project i s.1, t.project i s.2)

noncomputable def contraction (t : FundamentalSystem) (f : ∀ i, t.Value i → ℂ) : ℂ :=
  t.stateElements.sum fun s ↦ ∏ i, f i (t.project i s)

noncomputable def energy (t : FundamentalSystem) (i : Fin 6)
    (f : t.Value i → ℂ) : ℝ :=
  (t.valueElements i).sum fun x ↦ ‖f x‖ ^ 2

def scale : FundamentalSystem → ℝ
  | nil => 1
  | cons c t => c.scale * t.scale

theorem scale_nonneg : ∀ t : FundamentalSystem, 0 ≤ t.scale
  | nil => by simp [scale]
  | cons c t => mul_nonneg c.scale_nonneg t.scale_nonneg

theorem energy_nonneg (t : FundamentalSystem) (i : Fin 6)
    (f : t.Value i → ℂ) : 0 ≤ t.energy i f := by
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem sqrt_energy_nonneg (t : FundamentalSystem) (i : Fin 6)
    (f : t.Value i → ℂ) : 0 ≤ Real.sqrt (t.energy i f) :=
  Real.sqrt_nonneg _

/-- Montgomery--Vaughan's fundamental Cauchy/CRT inequality in tensor
form.  This is the full six-function result: functions may couple all CRT
coordinates, and the bound is the product of the prime-local scales. -/
theorem fundamental_le (t : FundamentalSystem) (f : ∀ i, t.Value i → ℂ) :
    ‖t.contraction f‖ ≤ t.scale * ∏ i, Real.sqrt (t.energy i (f i)) := by
  induction t with
  | nil =>
      change (∀ i, Unit → ℂ) at f
      unfold contraction scale energy stateElements valueElements project
      simp only [Finset.sum_singleton, one_mul]
      rw [norm_prod]
      simp only [Real.sqrt_sq_eq_abs, abs_norm]
      exact le_rfl
  | cons c t ih =>
      change (∀ i, c.Value i × t.Value i → ℂ) at f
      let hfun : ∀ i, t.Value i → ℂ := fun i y ↦
        (Real.sqrt ((c.valueFintype i).elems.sum (fun x ↦ ‖f i (x, y)‖ ^ 2)) : ℂ)
      have hlocal (s : t.State) :
          ‖c.stateFintype.elems.sum (fun x ↦
              ∏ i, f i (c.project i x, t.project i s))‖ ≤
            c.scale * ∏ i, Real.sqrt ((c.valueFintype i).elems.sum (fun x ↦
              ‖f i (x, t.project i s)‖ ^ 2)) := by
        change ‖c.stateFintype.elems.sum (fun x ↦
            ∏ i, f i (c.project i x, t.project i s))‖ ≤
          c.scale * ∏ i, Real.sqrt ((c.valueFintype i).elems.sum
            (fun x ↦ ‖f i (x, t.project i s)‖ ^ 2))
        exact c.localBound (fun i x ↦ f i (x, t.project i s))
      have hnonneg (s : t.State) :
          0 ≤ ∏ i, Real.sqrt ((c.valueFintype i).elems.sum (fun x ↦
            ‖f i (x, t.project i s)‖ ^ 2)) := by positivity
      have htail_eq : t.contraction hfun =
          ((t.stateElements.sum (fun s ↦ ∏ i, Real.sqrt
            ((c.valueFintype i).elems.sum (fun x ↦
              ‖f i (x, t.project i s)‖ ^ 2))) : ℝ) : ℂ) := by
        simp [contraction, hfun]
      have htail_norm :
          ‖t.contraction hfun‖ = t.stateElements.sum (fun s ↦ ∏ i,
            Real.sqrt ((c.valueFintype i).elems.sum (fun x ↦
              ‖f i (x, t.project i s)‖ ^ 2))) := by
        rw [htail_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
        exact Finset.sum_nonneg fun s _ ↦ hnonneg s
      calc
        ‖(FundamentalSystem.cons c t).contraction f‖ =
            ‖t.stateElements.sum (fun s ↦ c.stateFintype.elems.sum (fun x ↦
              ∏ i, f i (c.project i x, t.project i s)))‖ := by
                unfold contraction
                change ‖(c.stateFintype.elems ×ˢ t.stateElements).sum (fun s ↦
                  ∏ i, f i (c.project i s.1, t.project i s.2))‖ = _
                rw [Finset.sum_product_right]
        _ ≤ t.stateElements.sum (fun s ↦ ‖c.stateFintype.elems.sum (fun x ↦
              ∏ i, f i (c.project i x, t.project i s))‖) := norm_sum_le _ _
        _ ≤ t.stateElements.sum (fun s ↦ c.scale * ∏ i,
              Real.sqrt ((c.valueFintype i).elems.sum (fun x ↦
                ‖f i (x, t.project i s)‖ ^ 2))) := by
                exact Finset.sum_le_sum fun s _ ↦ hlocal s
        _ = c.scale * ‖t.contraction hfun‖ := by
              rw [htail_norm, Finset.mul_sum]
        _ ≤ c.scale * (t.scale * ∏ i, Real.sqrt (t.energy i (hfun i))) := by
              exact mul_le_mul_of_nonneg_left (ih hfun) c.scale_nonneg
        _ = (FundamentalSystem.cons c t).scale *
              ∏ i, Real.sqrt ((FundamentalSystem.cons c t).energy i (f i)) := by
              simp only [scale]
              rw [mul_assoc]
              congr 1
              congr 1
              apply Finset.prod_congr rfl
              intro i _
              congr 1
              simp only [energy, hfun, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (Real.sqrt_nonneg _),
                Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
              change (t.valueElements i).sum (fun y ↦
                (c.valueFintype i).elems.sum (fun x ↦ ‖f i (x, y)‖ ^ 2)) =
                ((c.valueFintype i).elems ×ˢ t.valueElements i).sum
                  (fun z ↦ ‖f i z‖ ^ 2)
              rw [Finset.sum_product_right]

end FundamentalSystem

/-! ## A concrete six-active prime coordinate

This constructor is the maximal-support local CRT coordinate.  The state
variables are the successive partial sums in a fivefold convolution; this
makes the identification with `iterConv` definitional after expanding the
finite products.
-/

section PrimeCoordinate

variable (p : ℕ) [NeZero p]

abbrev SixConvolutionState :=
  ZMod p × ZMod p × ZMod p × ZMod p × ZMod p

def sixConvolutionProject (i : Fin 6) (s : SixConvolutionState p) : ZMod p :=
  match i.1 with
  | 0 => s.2.2.2.2
  | 1 => s.2.2.2.1 - s.2.2.2.2
  | 2 => s.2.2.1 - s.2.2.2.1
  | 3 => s.2.1 - s.2.2.1
  | 4 => s.1 - s.2.1
  | _ => -s.1

private theorem sixConvolution_sum_eq (f : Fin 6 → ZMod p → ℂ) :
    ∑ s : SixConvolutionState p, ∏ i, f i (sixConvolutionProject p i s) =
      iterConv (f 0) [f 1, f 2, f 3, f 4, f 5] 0 := by
  simp only [iterConv, finiteConv]
  rw [show (∑ s : SixConvolutionState p, ∏ i, f i (sixConvolutionProject p i s)) =
      ∑ e : ZMod p, ∑ d : ZMod p, ∑ c : ZMod p, ∑ b : ZMod p, ∑ a : ZMod p,
        f 0 a * f 1 (b - a) * f 2 (c - b) * f 3 (d - c) * f 4 (e - d) * f 5 (-e) by
    simp only [Fintype.sum_prod_type]
    congr 1 with e
    congr 1 with d
    congr 1 with c
    congr 1 with b
    congr 1 with a
    simp [Fin.prod_univ_succ, sixConvolutionProject]
    ring]
  simp_rw [Finset.sum_mul]
  ring

/-- Concrete local coordinate for a prime occurring in all six
denominators.  Its exact scale is `p²`. -/
noncomputable def primeCoordinateSix : FundamentalCoordinate where
  State := SixConvolutionState p
  stateFintype := inferInstance
  Value := fun _ ↦ ZMod p
  valueFintype := fun _ ↦ inferInstance
  project := sixConvolutionProject p
  scale := (p : ℝ) ^ 2
  scale_nonneg := sq_nonneg _
  localBound := by
    intro f
    change ‖∑ s : SixConvolutionState p, ∏ i, f i (sixConvolutionProject p i s)‖ ≤ _
    rw [sixConvolution_sum_eq]
    have h := norm_iterConv_le (f 0) (f 1) [f 2, f 3, f 4, f 5] 0
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
    calc
      _ ≤ finiteL2 (f 0) * finiteL2 (f 1) *
          (Real.sqrt p * (Real.sqrt p * (Real.sqrt p * Real.sqrt p)) *
            (finiteL2 (f 2) * (finiteL2 (f 3) * (finiteL2 (f 4) * finiteL2 (f 5))))) := h
      _ = (p : ℝ) ^ 2 * ∏ i, Real.sqrt (∑ x : ZMod p, ‖f i x‖ ^ 2) := by
        have hs : Real.sqrt (p : ℝ) * Real.sqrt p = p := Real.mul_self_sqrt (by positivity)
        have hscale : Real.sqrt (p : ℝ) * (Real.sqrt p * p) = (p : ℝ) ^ 2 := by
          rw [← mul_assoc, hs]
          ring
        simp only [finiteL2]
        simp [Fin.prod_univ_succ]
        rw [hscale]
        ring

def twoConvolutionProject (i : Fin 6) (a : ZMod p) : ZMod p :=
  match i.1 with
  | 0 => a
  | 1 => -a
  | _ => 0

/-- Concrete coordinate for a prime occurring in the first two factors.
The remaining four coordinates are forced to zero. -/
noncomputable def primeCoordinateTwo : FundamentalCoordinate where
  State := ZMod p
  stateFintype := inferInstance
  Value := fun _ ↦ ZMod p
  valueFintype := fun _ ↦ inferInstance
  project := twoConvolutionProject p
  scale := 1
  scale_nonneg := zero_le_one
  localBound := by
    intro f
    change ‖∑ a : ZMod p, ∏ i, f i (twoConvolutionProject p i a)‖ ≤ _
    have heq : (∑ a : ZMod p, ∏ i, f i (twoConvolutionProject p i a)) =
        finiteConv (f 0) (f 1) 0 * (f 2 0 * f 3 0 * f 4 0 * f 5 0) := by
      simp [finiteConv, Fin.prod_univ_succ, twoConvolutionProject]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    rw [heq, one_mul, norm_mul]
    calc
      ‖finiteConv (f 0) (f 1) 0‖ * ‖f 2 0 * f 3 0 * f 4 0 * f 5 0‖ ≤
          (finiteL2 (f 0) * finiteL2 (f 1)) *
            (finiteL2 (f 2) * finiteL2 (f 3) * finiteL2 (f 4) * finiteL2 (f 5)) := by
        have hconst : ‖f 2 0 * f 3 0 * f 4 0 * f 5 0‖ ≤
            finiteL2 (f 2) * finiteL2 (f 3) * finiteL2 (f 4) * finiteL2 (f 5) := by
          have h2 := norm_le_finiteL2 (f 2) 0
          have h3 := norm_le_finiteL2 (f 3) 0
          have h4 := norm_le_finiteL2 (f 4) 0
          have h5 := norm_le_finiteL2 (f 5) 0
          simp only [norm_mul]
          exact mul_le_mul
            (mul_le_mul
              (mul_le_mul h2 h3 (norm_nonneg _) (finiteL2_nonneg _))
              h4
              (norm_nonneg _)
              (mul_nonneg (finiteL2_nonneg _) (finiteL2_nonneg _)))
            h5
            (norm_nonneg _)
            (mul_nonneg
              (mul_nonneg (finiteL2_nonneg _) (finiteL2_nonneg _))
              (finiteL2_nonneg _))
        exact mul_le_mul (norm_finiteConv_le _ _ _) hconst (norm_nonneg _)
          (mul_nonneg (finiteL2_nonneg _) (finiteL2_nonneg _))
      _ = ∏ i, Real.sqrt (∑ x : ZMod p, ‖f i x‖ ^ 2) := by
        simp only [finiteL2]
        simp [Fin.prod_univ_succ]
        ring

/-- Reindex a prime-local coordinate by a permutation of the six factors. -/
noncomputable def permutePrimeCoordinate
    (S : Type) [Fintype S] (baseProject : Fin 6 → S → ZMod p)
    (scale : ℝ) (hscale : 0 ≤ scale)
    (hbound : ∀ f : Fin 6 → ZMod p → ℂ,
      ‖∑ s : S, ∏ i, f i (baseProject i s)‖ ≤
        scale * ∏ i, Real.sqrt (∑ x : ZMod p, ‖f i x‖ ^ 2))
    (σ : Equiv.Perm (Fin 6)) : FundamentalCoordinate where
  State := S
  stateFintype := inferInstance
  Value := fun _ ↦ ZMod p
  valueFintype := fun _ ↦ inferInstance
  project := fun i s ↦ baseProject (σ.symm i) s
  scale := scale
  scale_nonneg := hscale
  localBound := by
    intro f
    change ‖∑ s : S, ∏ i, f i (baseProject (σ.symm i) s)‖ ≤ _
    have h := hbound (fun i ↦ f (σ i))
    calc
      ‖∑ s : S, ∏ i, f i (baseProject (σ.symm i) s)‖ =
          ‖∑ s : S, ∏ i, f (σ i) (baseProject i s)‖ := by
        congr 2
        funext s
        symm
        exact Fintype.prod_equiv σ _ _ (by simp)
      _ ≤ scale * ∏ i, Real.sqrt (∑ x : ZMod p, ‖f (σ i) x‖ ^ 2) := h
      _ = scale * ∏ i, Real.sqrt (∑ x : ZMod p, ‖f i x‖ ^ 2) := by
        congr 1
        exact Fintype.prod_equiv σ _ _ (by simp)

abbrev ThreeConvolutionState := ZMod p × ZMod p

def threeConvolutionProject (i : Fin 6) (s : ThreeConvolutionState p) : ZMod p :=
  match i.1 with
  | 0 => s.2
  | 1 => s.1 - s.2
  | 2 => -s.1
  | _ => 0

private theorem threeConvolution_sum_eq (f : Fin 6 → ZMod p → ℂ) :
    ∑ s : ThreeConvolutionState p, ∏ i, f i (threeConvolutionProject p i s) =
      iterConv (f 0) [f 1, f 2] 0 * (f 3 0 * f 4 0 * f 5 0) := by
  simp only [iterConv, finiteConv, Fintype.sum_prod_type]
  simp [Fin.prod_univ_succ, threeConvolutionProject]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- Concrete coordinate for a prime occurring in the first three factors. -/
noncomputable def primeCoordinateThree : FundamentalCoordinate where
  State := ThreeConvolutionState p
  stateFintype := inferInstance
  Value := fun _ ↦ ZMod p
  valueFintype := fun _ ↦ inferInstance
  project := threeConvolutionProject p
  scale := Real.sqrt p
  scale_nonneg := Real.sqrt_nonneg _
  localBound := by
    intro f
    change ‖∑ s : ThreeConvolutionState p, ∏ i, f i (threeConvolutionProject p i s)‖ ≤ _
    rw [threeConvolution_sum_eq, norm_mul]
    have hactive := norm_iterConv_le (f 0) (f 1) [f 2] 0
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hactive
    have hconst : ‖f 3 0 * f 4 0 * f 5 0‖ ≤
        finiteL2 (f 3) * finiteL2 (f 4) * finiteL2 (f 5) := by
      have h3 := norm_le_finiteL2 (f 3) 0
      have h4 := norm_le_finiteL2 (f 4) 0
      have h5 := norm_le_finiteL2 (f 5) 0
      simp only [norm_mul]
      exact mul_le_mul (mul_le_mul h3 h4 (norm_nonneg _) (finiteL2_nonneg _)) h5
        (norm_nonneg _) (mul_nonneg (finiteL2_nonneg _) (finiteL2_nonneg _))
    calc
      _ ≤ (finiteL2 (f 0) * finiteL2 (f 1) *
          (Real.sqrt p * finiteL2 (f 2))) *
          (finiteL2 (f 3) * finiteL2 (f 4) * finiteL2 (f 5)) :=
        mul_le_mul hactive hconst (norm_nonneg _)
          (mul_nonneg (mul_nonneg (finiteL2_nonneg _) (finiteL2_nonneg _))
            (mul_nonneg (Real.sqrt_nonneg _) (finiteL2_nonneg _)))
      _ = Real.sqrt p * ∏ i, Real.sqrt (∑ x : ZMod p, ‖f i x‖ ^ 2) := by
        simp only [finiteL2]
        simp [Fin.prod_univ_succ]
        ring

abbrev FourConvolutionState := ZMod p × ZMod p × ZMod p

def fourConvolutionProject (i : Fin 6) (s : FourConvolutionState p) : ZMod p :=
  match i.1 with
  | 0 => s.2.2
  | 1 => s.2.1 - s.2.2
  | 2 => s.1 - s.2.1
  | 3 => -s.1
  | _ => 0

private theorem fourConvolution_sum_eq (f : Fin 6 → ZMod p → ℂ) :
    ∑ s : FourConvolutionState p, ∏ i, f i (fourConvolutionProject p i s) =
      iterConv (f 0) [f 1, f 2, f 3] 0 * (f 4 0 * f 5 0) := by
  simp only [iterConv, finiteConv, Fintype.sum_prod_type]
  simp [Fin.prod_univ_succ, fourConvolutionProject]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- Concrete coordinate for a prime occurring in the first four factors. -/
noncomputable def primeCoordinateFour : FundamentalCoordinate where
  State := FourConvolutionState p
  stateFintype := inferInstance
  Value := fun _ ↦ ZMod p
  valueFintype := fun _ ↦ inferInstance
  project := fourConvolutionProject p
  scale := Real.sqrt p ^ 2
  scale_nonneg := sq_nonneg _
  localBound := by
    intro f
    change ‖∑ s : FourConvolutionState p, ∏ i, f i (fourConvolutionProject p i s)‖ ≤ _
    rw [fourConvolution_sum_eq, norm_mul]
    have hactive := norm_iterConv_le (f 0) (f 1) [f 2, f 3] 0
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hactive
    have hconst : ‖f 4 0 * f 5 0‖ ≤ finiteL2 (f 4) * finiteL2 (f 5) := by
      simp only [norm_mul]
      exact mul_le_mul (norm_le_finiteL2 _ _) (norm_le_finiteL2 _ _)
        (norm_nonneg _) (finiteL2_nonneg _)
    calc
      _ ≤ (finiteL2 (f 0) * finiteL2 (f 1) *
          ((Real.sqrt p * Real.sqrt p) * (finiteL2 (f 2) * finiteL2 (f 3)))) *
          (finiteL2 (f 4) * finiteL2 (f 5)) :=
        mul_le_mul hactive hconst (norm_nonneg _)
          (mul_nonneg (mul_nonneg (finiteL2_nonneg _) (finiteL2_nonneg _))
            (mul_nonneg
              (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
              (mul_nonneg (finiteL2_nonneg _) (finiteL2_nonneg _))))
      _ = Real.sqrt p ^ 2 * ∏ i, Real.sqrt (∑ x : ZMod p, ‖f i x‖ ^ 2) := by
        simp only [finiteL2]
        simp [Fin.prod_univ_succ]
        ring

abbrev FiveConvolutionState := ZMod p × ZMod p × ZMod p × ZMod p

def fiveConvolutionProject (i : Fin 6) (s : FiveConvolutionState p) : ZMod p :=
  match i.1 with
  | 0 => s.2.2.2
  | 1 => s.2.2.1 - s.2.2.2
  | 2 => s.2.1 - s.2.2.1
  | 3 => s.1 - s.2.1
  | 4 => -s.1
  | _ => 0

private theorem fiveConvolution_sum_eq (f : Fin 6 → ZMod p → ℂ) :
    ∑ s : FiveConvolutionState p, ∏ i, f i (fiveConvolutionProject p i s) =
      iterConv (f 0) [f 1, f 2, f 3, f 4] 0 * f 5 0 := by
  simp only [iterConv, finiteConv, Fintype.sum_prod_type]
  simp [Fin.prod_univ_succ, fiveConvolutionProject]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- Concrete coordinate for a prime occurring in the first five factors. -/
noncomputable def primeCoordinateFive : FundamentalCoordinate where
  State := FiveConvolutionState p
  stateFintype := inferInstance
  Value := fun _ ↦ ZMod p
  valueFintype := fun _ ↦ inferInstance
  project := fiveConvolutionProject p
  scale := Real.sqrt p ^ 3
  scale_nonneg := pow_nonneg (Real.sqrt_nonneg _) _
  localBound := by
    intro f
    change ‖∑ s : FiveConvolutionState p, ∏ i, f i (fiveConvolutionProject p i s)‖ ≤ _
    rw [fiveConvolution_sum_eq, norm_mul]
    have hactive := norm_iterConv_le (f 0) (f 1) [f 2, f 3, f 4] 0
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hactive
    calc
      _ ≤ (finiteL2 (f 0) * finiteL2 (f 1) *
          ((Real.sqrt p * (Real.sqrt p * Real.sqrt p)) *
            (finiteL2 (f 2) * (finiteL2 (f 3) * finiteL2 (f 4))))) *
          finiteL2 (f 5) :=
        mul_le_mul hactive (norm_le_finiteL2 _ _) (norm_nonneg _)
          (mul_nonneg (mul_nonneg (finiteL2_nonneg _) (finiteL2_nonneg _))
            (mul_nonneg
              (mul_nonneg (Real.sqrt_nonneg _)
                (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
              (mul_nonneg (finiteL2_nonneg _)
                (mul_nonneg (finiteL2_nonneg _) (finiteL2_nonneg _)))))
      _ = Real.sqrt p ^ 3 * ∏ i, Real.sqrt (∑ x : ZMod p, ‖f i x‖ ^ 2) := by
        have hs : Real.sqrt (p : ℝ) ^ 2 = p := Real.sq_sqrt (by positivity)
        simp only [finiteL2]
        simp [Fin.prod_univ_succ]
        rw [show Real.sqrt (p : ℝ) ^ 3 = Real.sqrt p * p by
          rw [pow_succ, hs, mul_comm]]
        ring

private noncomputable def finsetSupportPerm (s t : Finset (Fin 6))
    (h : s.card = t.card) : Equiv.Perm (Fin 6) :=
  Classical.choose (Equiv.Perm.exists_map_finset_eq s t h)

private theorem finsetSupportPerm_map (s t : Finset (Fin 6))
    (h : s.card = t.card) :
    s.map (finsetSupportPerm s t h).toEmbedding = t :=
  Classical.choose_spec (Equiv.Perm.exists_map_finset_eq s t h)

private theorem fintype_elems_eq {α : Type} (A B : Fintype α) :
    A.elems = B.elems := by
  ext x
  constructor
  · intro hx
    exact B.complete x
  · intro hx
    exact A.complete x

/-- The prime-local Montgomery--Vaughan coordinate for an arbitrary support
of cardinality at least two.  All six value types are `ZMod p`; coordinates
outside `J` are forced to zero.  The scale is exactly
`(sqrt p) ^ (J.card - 2)`. -/
noncomputable def primeCoordinateForSupport (J : Finset (Fin 6))
    (hJ : 2 ≤ J.card) : FundamentalCoordinate :=
  if h2 : J.card = 2 then
    permutePrimeCoordinate p (ZMod p) (twoConvolutionProject p)
      (Real.sqrt p ^ (J.card - 2)) (pow_nonneg (Real.sqrt_nonneg _) _)
      (by
        intro f
        simpa [h2, primeCoordinateTwo] using
          (primeCoordinateTwo p).localBound_with
            (by change Fintype (ZMod p); infer_instance)
            (fun _ ↦ by change Fintype (ZMod p); infer_instance) f)
      (finsetSupportPerm ({0, 1} : Finset (Fin 6)) J (by simp [h2]))
  else if h3 : J.card = 3 then
    permutePrimeCoordinate p (ThreeConvolutionState p) (threeConvolutionProject p)
      (Real.sqrt p ^ (J.card - 2)) (pow_nonneg (Real.sqrt_nonneg _) _)
      (by
        intro f
        simpa [h3, primeCoordinateThree] using
          (primeCoordinateThree p).localBound_with
            (by change Fintype (ThreeConvolutionState p); infer_instance)
            (fun _ ↦ by change Fintype (ZMod p); infer_instance) f)
      (finsetSupportPerm ({0, 1, 2} : Finset (Fin 6)) J (by simp [h3]))
  else if h4 : J.card = 4 then
    permutePrimeCoordinate p (FourConvolutionState p) (fourConvolutionProject p)
      (Real.sqrt p ^ (J.card - 2)) (pow_nonneg (Real.sqrt_nonneg _) _)
      (by
        intro f
        rw [h4]
        change ‖∑ s : FourConvolutionState p,
          ∏ i, f i (fourConvolutionProject p i s)‖ ≤ _
        rw [fourConvolution_sum_eq, norm_mul]
        have hactive := norm_iterConv_le (f 0) (f 1) [f 2, f 3] 0
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          mul_one] at hactive
        have hconst : ‖f 4 0 * f 5 0‖ ≤ finiteL2 (f 4) * finiteL2 (f 5) := by
          simp only [norm_mul]
          exact mul_le_mul (norm_le_finiteL2 _ _) (norm_le_finiteL2 _ _)
            (norm_nonneg _) (finiteL2_nonneg _)
        calc
          _ ≤ (finiteL2 (f 0) * finiteL2 (f 1) *
              ((Real.sqrt p * Real.sqrt p) *
                (finiteL2 (f 2) * finiteL2 (f 3)))) *
              (finiteL2 (f 4) * finiteL2 (f 5)) :=
            mul_le_mul hactive hconst (norm_nonneg _)
              (mul_nonneg (mul_nonneg (finiteL2_nonneg _) (finiteL2_nonneg _))
                (mul_nonneg
                  (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
                  (mul_nonneg (finiteL2_nonneg _) (finiteL2_nonneg _))))
          _ = Real.sqrt p ^ (4 - 2) *
              ∏ i, Real.sqrt (∑ x : ZMod p, ‖f i x‖ ^ 2) := by
            simp only [finiteL2]
            norm_num
            simp [Fin.prod_univ_succ]
            ring)
      (finsetSupportPerm ({0, 1, 2, 3} : Finset (Fin 6)) J (by simp [h4]))
  else if h5 : J.card = 5 then
    permutePrimeCoordinate p (FiveConvolutionState p) (fiveConvolutionProject p)
      (Real.sqrt p ^ (J.card - 2)) (pow_nonneg (Real.sqrt_nonneg _) _)
      (by
        intro f
        simpa [h5, primeCoordinateFive] using
          (primeCoordinateFive p).localBound_with
            (by change Fintype (FiveConvolutionState p); infer_instance)
            (fun _ ↦ by change Fintype (ZMod p); infer_instance) f)
      (finsetSupportPerm ({0, 1, 2, 3, 4} : Finset (Fin 6)) J (by simp [h5]))
  else
    have h6 : J.card = 6 := by
      have hle : J.card ≤ 6 := by simpa using J.card_le_univ
      omega
    permutePrimeCoordinate p (SixConvolutionState p) (sixConvolutionProject p)
      (Real.sqrt p ^ (J.card - 2)) (pow_nonneg (Real.sqrt_nonneg _) _)
      (by
        intro f
        have hs : Real.sqrt (p : ℝ) ^ 2 = p := Real.sq_sqrt (by positivity)
        simpa [h6, primeCoordinateSix, pow_succ, hs, mul_comm, mul_left_comm,
          mul_assoc] using
          (primeCoordinateSix p).localBound_with
            (by change Fintype (SixConvolutionState p); infer_instance)
            (fun _ ↦ by change Fintype (ZMod p); infer_instance) f)
      (finsetSupportPerm ({0, 1, 2, 3, 4, 5} : Finset (Fin 6)) J (by simp [h6]))

@[simp] theorem primeCoordinateForSupport_scale (J : Finset (Fin 6))
    (hJ : 2 ≤ J.card) :
    (primeCoordinateForSupport p J hJ).scale = Real.sqrt p ^ (J.card - 2) := by
  unfold primeCoordinateForSupport
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split <;> rfl

end PrimeCoordinate

end Erdos220
