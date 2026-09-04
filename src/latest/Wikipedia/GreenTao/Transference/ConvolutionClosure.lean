import Wikipedia.GreenTao.Transference.ConvolutionMoments
import Wikipedia.GreenTao.Transference.FaceMoments

/-!
# Multiplicative closure of generalized convolutions

The dense-model proof tests against generalized convolutions.  Products of
these tests remain convex averages of generalized convolutions: two points
in the same coordinate-sum fiber differ by a tuple of sum zero, and fixing
that difference turns the two cut products into one cut product.

This file proves the exact finite identity, packages finite convex mixtures,
and transfers a single cut-discrepancy estimate to every monomial required
by polynomial dense-model duality.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators Polynomial

universe u

/-- A product of two independent means can be reparametrized by a point and
its additive displacement. -/
theorem mean_mul_mean_eq_mean₂_add
    {A : Type*} [Fintype A] [AddCommGroup A]
    (f g : A → ℝ) :
    mean f * mean g =
      mean₂ (fun d : A => fun x : A => f x * g (x + d)) := by
  calc
    mean f * mean g =
        mean₂ (fun x : A => fun y : A => f x * g y) := by
      simpa [mean, mean₂] using
        (Fintype.expect_mul_expect f g)
    _ = mean₂ (fun x : A => fun d : A =>
          f x * g (x + d)) := by
      unfold mean₂
      apply congrArg mean
      funext x
      have htranslate :=
        mean_add_right (fun y : A => f x * g y) x
      have hfun :
          (fun d : A => f x * g (d + x)) =
            fun d : A => f x * g (x + d) := by
        funext d
        rw [add_comm]
      rw [hfun] at htranslate
      exact htranslate.symm
    _ = mean₂ (fun d : A => fun x : A =>
          f x * g (x + d)) :=
      mean₂_comm _

/-- The unique zero-sum `(n+1)`-tuple whose tail is `d`. -/
def zeroSumShift
    {G : Type*} [AddCommGroup G] (n : ℕ)
    (d : Fin n → G) : Fin (n + 1) → G :=
  sumFiberTuple n 0 d

@[simp]
theorem sum_zeroSumShift
    {G : Type*} [AddCommGroup G] (n : ℕ)
    (d : Fin n → G) :
    ∑ i, zeroSumShift n d i = 0 :=
  sum_sumFiberTuple n 0 d

/-- Add a fixed zero-sum displacement to a full fiber tuple. -/
theorem sumFiberTuple_add_zeroSumShift
    {G : Type*} [AddCommGroup G] (n : ℕ)
    (z : G) (x d : Fin n → G) :
    (fun i : Fin (n + 1) =>
      sumFiberTuple n z x i + zeroSumShift n d i) =
        sumFiberTuple n z (fun t => x t + d t) := by
  funext i
  refine Fin.cases ?_ (fun _ => rfl) i
  change
    (z - ∑ t, x t) + (0 - ∑ t, d t) =
      z - ∑ t, (x t + d t)
  rw [Finset.sum_add_distrib]
  abel

/-- For a fixed zero-sum displacement, multiply the two deleted-coordinate
test families after translating the second one. -/
def convolutionProductCutTest
    {G : Type*} [AddCommGroup G] (n : ℕ)
    (u v : CutTestFamily G (n + 1))
    (d : Fin n → G) :
    CutTestFamily G (n + 1) :=
  fun i y =>
    u i y *
      v i (fun t =>
        y t + eraseCoordinate i (zeroSumShift n d) t)

theorem convolutionProductCutTest_bounded
    {G : Type*} [AddCommGroup G] {n : ℕ}
    {u v : CutTestFamily G (n + 1)}
    (hu : IsBoundedCutTest u) (hv : IsBoundedCutTest v)
    (d : Fin n → G) :
    IsBoundedCutTest
      (convolutionProductCutTest n u v d) := by
  constructor
  · intro i y
    exact mul_nonneg (hu.nonneg i y)
      (hv.nonneg i
        (fun t =>
          y t + eraseCoordinate i (zeroSumShift n d) t))
  · intro i y
    exact mul_le_one₀ (hu.le_one i y)
      (hv.nonneg i
        (fun t =>
          y t + eraseCoordinate i (zeroSumShift n d) t))
      (hv.le_one i
        (fun t =>
          y t + eraseCoordinate i (zeroSumShift n d) t))

/-- Pointwise form of the fixed-displacement cut-product identity. -/
theorem cutTestProduct_convolutionProductCutTest
    {G : Type*} [AddCommGroup G] (n : ℕ)
    (u v : CutTestFamily G (n + 1))
    (d : Fin n → G) (x : Fin (n + 1) → G) :
    cutTestProduct
        (convolutionProductCutTest n u v d) x =
      cutTestProduct u x *
        cutTestProduct v
          (fun i => x i + zeroSumShift n d i) := by
  rw [cutTestProduct, cutTestProduct, cutTestProduct]
  simp only [convolutionProductCutTest]
  rw [Finset.prod_mul_distrib]
  apply congrArg
  apply Finset.prod_congr rfl
  intro i _
  congr 1

/-- Tail-coordinate form of the same identity. -/
theorem cutTestProduct_convolutionProductCutTest_sumFiberTuple
    {G : Type*} [AddCommGroup G] (n : ℕ)
    (u v : CutTestFamily G (n + 1))
    (z : G) (d x : Fin n → G) :
    cutTestProduct
        (convolutionProductCutTest n u v d)
        (sumFiberTuple n z x) =
      cutTestProduct u (sumFiberTuple n z x) *
        cutTestProduct v
          (sumFiberTuple n z (fun t => x t + d t)) := by
  rw [cutTestProduct_convolutionProductCutTest,
    sumFiberTuple_add_zeroSumShift]

/-- Exact multiplicative closure: a product of two generalized
convolutions is the normalized average of generalized convolutions indexed
by the zero-sum displacement between their fiber points. -/
theorem generalizedConvolution_mul_eq_mean
    {G : Type*} [Fintype G] [AddCommGroup G] (n : ℕ)
    (u v : CutTestFamily G (n + 1)) (z : G) :
    generalizedConvolution (n + 1) u z *
        generalizedConvolution (n + 1) v z =
      mean (fun d : Fin n → G =>
        generalizedConvolution (n + 1)
          (convolutionProductCutTest n u v d) z) := by
  rw [generalizedConvolution_succ,
    generalizedConvolution_succ,
    mean_mul_mean_eq_mean₂_add]
  unfold mean₂
  apply congrArg mean
  funext d
  rw [generalizedConvolution_succ]
  apply congrArg mean
  funext x
  exact
    (cutTestProduct_convolutionProductCutTest_sumFiberTuple
      n u v z d x).symm

/-! ## Finite convex mixtures -/

/-- A finite convex average of bounded generalized convolutions.  Uniform
averages suffice because every multiplication step below naturally
introduces one more finite uniform parameter. -/
structure ConvolutionMixture
    (G : Type u) [AddCommGroup G] (r : ℕ) where
  ι : Type u
  indexFintype : Fintype ι
  indexNonempty : Nonempty ι
  tests : ι → CutTestFamily G r
  bounded : ∀ a, IsBoundedCutTest (tests a)

namespace ConvolutionMixture

/-- The function represented by a finite convolution mixture. -/
noncomputable def eval
    {G : Type u} [Fintype G] [AddCommGroup G] {r : ℕ}
    (m : ConvolutionMixture G r) : G → ℝ :=
  letI : Fintype m.ι := m.indexFintype
  fun z => mean (fun a => generalizedConvolution r (m.tests a) z)

/-- A single generalized convolution as a one-point mixture. -/
def pure
    {G : Type u} [AddCommGroup G] {r : ℕ}
    (u : CutTestFamily G r) (hu : IsBoundedCutTest u) :
    ConvolutionMixture G r where
  ι := ULift.{u} Unit
  indexFintype := inferInstance
  indexNonempty := inferInstance
  tests := fun _ => u
  bounded := fun _ => hu

@[simp]
theorem eval_pure
    {G : Type u} [Fintype G] [AddCommGroup G] {r : ℕ}
    (u : CutTestFamily G r) (hu : IsBoundedCutTest u)
    (z : G) :
    (pure u hu).eval z = generalizedConvolution r u z := by
  change
    mean (fun _ : ULift.{u} Unit => generalizedConvolution r u z) =
      generalizedConvolution r u z
  exact mean_const _

/-- The constant-one function represented as a generalized convolution at
positive arity. -/
def one
    {G : Type u} [AddCommGroup G] (n : ℕ) :
    ConvolutionMixture G (n + 1) :=
  pure
    (fun _ : Fin (n + 1) =>
      fun _ : Fin n → G => (1 : ℝ))
    isBoundedCutTest_one

@[simp]
theorem eval_one
    {G : Type u} [Fintype G] [AddCommGroup G]
    (n : ℕ) (z : G) :
    (one (G := G) n).eval z = 1 := by
  rw [one, eval_pure, generalizedConvolution_one_succ]

/-- Multiply two mixtures by adjoining the two mixture indices and the
zero-sum displacement parameter from
`generalizedConvolution_mul_eq_mean`. -/
noncomputable def mul
    {G : Type u} [Fintype G] [AddCommGroup G] (n : ℕ)
    (m₁ m₂ : ConvolutionMixture G (n + 1)) :
    ConvolutionMixture G (n + 1) := by
  letI : Fintype m₁.ι := m₁.indexFintype
  letI : Fintype m₂.ι := m₂.indexFintype
  letI : Nonempty m₁.ι := m₁.indexNonempty
  letI : Nonempty m₂.ι := m₂.indexNonempty
  exact
    { ι := m₁.ι × (m₂.ι × (Fin n → G))
      indexFintype := inferInstance
      indexNonempty := inferInstance
      tests := fun p =>
        convolutionProductCutTest n
          (m₁.tests p.1) (m₂.tests p.2.1) p.2.2
      bounded := fun p =>
        convolutionProductCutTest_bounded
          (m₁.bounded p.1) (m₂.bounded p.2.1) p.2.2 }

/-- Evaluation of the product mixture is pointwise multiplication. -/
theorem eval_mul
    {G : Type u} [Fintype G] [AddCommGroup G] (n : ℕ)
    (m₁ m₂ : ConvolutionMixture G (n + 1)) (z : G) :
    (mul n m₁ m₂).eval z = m₁.eval z * m₂.eval z := by
  let : Fintype m₁.ι := m₁.indexFintype
  let : Fintype m₂.ι := m₂.indexFintype
  let : Nonempty m₁.ι := m₁.indexNonempty
  let : Nonempty m₂.ι := m₂.indexNonempty
  change
    mean (fun p : m₁.ι × (m₂.ι × (Fin n → G)) =>
      generalizedConvolution (n + 1)
        (convolutionProductCutTest n
          (m₁.tests p.1) (m₂.tests p.2.1) p.2.2) z) =
      mean (fun a : m₁.ι =>
        generalizedConvolution (n + 1) (m₁.tests a) z) *
      mean (fun b : m₂.ι =>
        generalizedConvolution (n + 1) (m₂.tests b) z)
  calc
    mean (fun p : m₁.ι × (m₂.ι × (Fin n → G)) =>
        generalizedConvolution (n + 1)
          (convolutionProductCutTest n
            (m₁.tests p.1) (m₂.tests p.2.1) p.2.2) z) =
        mean₂ (fun a : m₁.ι =>
          fun p : m₂.ι × (Fin n → G) =>
            generalizedConvolution (n + 1)
              (convolutionProductCutTest n
                (m₁.tests a) (m₂.tests p.1) p.2) z) :=
      by
        simpa [mean, mean₂] using
          (Finset.expect_product'
            (Finset.univ : Finset m₁.ι)
            (Finset.univ :
              Finset (m₂.ι × (Fin n → G)))
            (fun a : m₁.ι =>
              fun p : m₂.ι × (Fin n → G) =>
                generalizedConvolution (n + 1)
                  (convolutionProductCutTest n
                    (m₁.tests a) (m₂.tests p.1) p.2) z))
    _ = mean (fun a : m₁.ι =>
          mean₂ (fun b : m₂.ι => fun d : Fin n → G =>
            generalizedConvolution (n + 1)
              (convolutionProductCutTest n
                (m₁.tests a) (m₂.tests b) d) z)) := by
      unfold mean₂
      apply congrArg mean
      funext a
      simpa [mean, mean₂] using
        (Finset.expect_product'
          (Finset.univ : Finset m₂.ι)
          (Finset.univ : Finset (Fin n → G))
          (fun b : m₂.ι => fun d : Fin n → G =>
            generalizedConvolution (n + 1)
              (convolutionProductCutTest n
                (m₁.tests a) (m₂.tests b) d) z))
    _ = mean₂ (fun a : m₁.ι => fun b : m₂.ι =>
          generalizedConvolution (n + 1) (m₁.tests a) z *
            generalizedConvolution (n + 1) (m₂.tests b) z) := by
      unfold mean₂
      apply congrArg mean
      funext a
      apply congrArg mean
      funext b
      exact
        (generalizedConvolution_mul_eq_mean
          n (m₁.tests a) (m₂.tests b) z).symm
    _ = mean (fun a : m₁.ι =>
          generalizedConvolution (n + 1) (m₁.tests a) z) *
        mean (fun b : m₂.ι =>
          generalizedConvolution (n + 1) (m₂.tests b) z) := by
      simpa [mean, mean₂] using
        (Fintype.expect_mul_expect
          (fun a : m₁.ι =>
            generalizedConvolution (n + 1) (m₁.tests a) z)
          (fun b : m₂.ι =>
            generalizedConvolution (n + 1) (m₂.tests b) z)).symm

/-- Every finite product of bounded generalized convolutions is represented
by a finite convolution mixture. -/
theorem exists_eq_prod_generalizedConvolution
    {G : Type u} [Fintype G] [AddCommGroup G] (r : ℕ) :
    ∀ (m : ℕ) (u : Fin m → CutTestFamily G (r + 1)),
      (∀ a, IsBoundedCutTest (u a)) →
      ∃ q : ConvolutionMixture G (r + 1),
        q.eval =
          fun z => ∏ a,
            generalizedConvolution (r + 1) (u a) z := by
  intro m
  induction m with
  | zero =>
      intro u hu
      refine ⟨one r, ?_⟩
      funext z
      simp
  | succ m ih =>
      intro u hu
      obtain ⟨q, hq⟩ :=
        ih (fun a : Fin m => u a.succ)
          (fun a => hu a.succ)
      let p : ConvolutionMixture G (r + 1) :=
        pure (u 0) (hu 0)
      refine ⟨mul r p q, ?_⟩
      funext z
      rw [eval_mul, eval_pure, congrFun hq z,
        Fin.prod_univ_succ]

/-- Pairing with a mixture is the mixture of the individual pairings. -/
theorem finitePairing_eval
    {G : Type u} [Fintype G] [AddCommGroup G] {r : ℕ}
    (m : ConvolutionMixture G r) (h : G → ℝ) :
    finitePairing h m.eval =
      letI : Fintype m.ι := m.indexFintype
      mean (fun a =>
        finitePairing h
          (generalizedConvolution r (m.tests a))) := by
  let : Fintype m.ι := m.indexFintype
  let : Nonempty m.ι := m.indexNonempty
  change
    mean (fun z : G =>
      h z * mean (fun a : m.ι =>
        generalizedConvolution r (m.tests a) z)) =
      mean (fun a : m.ι =>
        mean (fun z : G =>
          h z * generalizedConvolution r (m.tests a) z))
  calc
    mean (fun z : G =>
        h z * mean (fun a : m.ι =>
          generalizedConvolution r (m.tests a) z)) =
        mean₂ (fun z : G => fun a : m.ι =>
          h z * generalizedConvolution r (m.tests a) z) := by
      unfold mean₂
      apply congrArg mean
      funext z
      exact
        (mean_smul (h z)
          (fun a : m.ι =>
            generalizedConvolution r (m.tests a) z)).symm
    _ = mean₂ (fun a : m.ι => fun z : G =>
          h z * generalizedConvolution r (m.tests a) z) :=
      mean₂_comm _
    _ = _ := rfl

end ConvolutionMixture

/-! ## Consequences for dense-model moments -/

/-- Cut discrepancy controls the pairing with every finite convolution
mixture. -/
theorem CutDiscrepancyLe.abs_finitePairing_convolutionMixture_le
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} {ν : G → ℝ} {ε : ℝ}
    (hcut : CutDiscrepancyLe r ν (fun _ => 1) ε)
    (m : ConvolutionMixture G r) :
    |finitePairing (ν - fun _ => 1) m.eval| ≤ ε := by
  let : Fintype m.ι := m.indexFintype
  let : Nonempty m.ι := m.indexNonempty
  rw [m.finitePairing_eval]
  calc
    |mean (fun a : m.ι =>
        finitePairing (ν - fun _ => 1)
          (generalizedConvolution r (m.tests a)))| ≤
        mean (fun a : m.ι =>
          |finitePairing (ν - fun _ => 1)
            (generalizedConvolution r (m.tests a))|) := by
      exact Finset.abs_expect_le Finset.univ _
    _ ≤ mean (fun _a : m.ι => ε) := by
      apply mean_mono
      intro a
      have ha :=
        hcut.apply_bounded (m.tests a) (m.bounded a)
      rw [cutCorrelation_eq_mean_mul_generalizedConvolution] at ha
      simpa [finitePairing] using ha
    _ = ε := mean_const _

/-- Multiplicative closure upgrades a single cut-discrepancy estimate to
all expanded convolution moments, at no additional error loss. -/
theorem CutDiscrepancyLe.hasConvolutionMomentBound
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} {ν : G → ℝ} {ε : ℝ}
    (hcut : CutDiscrepancyLe (r + 1) ν (fun _ => 1) ε)
    (d : ℕ) :
    HasConvolutionMomentBound r d ν ε := by
  intro m hm u hu
  obtain ⟨q, hq⟩ :=
    ConvolutionMixture.exists_eq_prod_generalizedConvolution
      r m u hu
  have hpair :=
    hcut.abs_finitePairing_convolutionMixture_le q
  have hproduct :
      testMonomial
          (fun a : Fin m =>
            generalizedConvolution (r + 1) (u a))
          (fun a => a) =
        q.eval := by
    rw [hq]
    rfl
  rw [← finitePairing_testMonomial_generalizedConvolution
    r ν u (fun a => a), hproduct]
  exact hpair

/-- For a nonnegative majorant, positive-arity cut discrepancy from one
also gives the absolute first-moment bound needed by polynomial
approximation. -/
theorem CutDiscrepancyLe.centeredAbsoluteMean_le_two_add
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} {ν : G → ℝ} {ε : ℝ}
    (hcut : CutDiscrepancyLe r ν (fun _ => 1) ε)
    (hr : 0 < r) (hν : ∀ x, 0 ≤ ν x) :
    centeredAbsoluteMean ν ≤ 2 + ε := by
  have hmeanAbs := hcut.abs_mean_sub_le hr
  have hmean : mean ν ≤ 1 + ε := by
    rw [mean_const] at hmeanAbs
    linarith [le_abs_self (mean ν - 1)]
  calc
    centeredAbsoluteMean ν ≤ mean ν + 1 :=
      centeredAbsoluteMean_le_mean_add_one hν
    _ ≤ 2 + ε := by linarith

/-- The ordinary CFZ linear-forms condition supplies every convolution
moment needed by the polynomial dense-model theorem. -/
theorem HasLinearFormsCondition.hasConvolutionMomentBound
    {r N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η ε : ℝ}
    (h : HasLinearFormsCondition (r + 2) N ν η)
    (hN : Nat.Coprime N (Nat.factorial (r + 1)))
    (hε : 0 ≤ ε)
    (hηε :
      (2 : ℝ) ^ (2 ^ (r + 1)) * η ≤
        ε ^ (2 ^ (r + 1)))
    (d : ℕ) :
    HasConvolutionMomentBound r d ν ε :=
  (h.cutDiscrepancyLe_one hN hε hηε).hasConvolutionMomentBound d

/-- Direct quantitative dense-model theorem from the ordinary CFZ
linear-forms condition.  The output error displays separately the
polynomial-monomial loss and the positive-part approximation loss. -/
theorem exists_cutDiscrepancy_model_of_linearFormsCondition
    {r N : ℕ} [NeZero N]
    {f ν : ZMod N → ℝ}
    {linearFormsError cutError : ℝ}
    {p : ℝ[X]} {approximationError : ℝ}
    (happrox : 0 ≤ approximationError)
    (hcutError : 0 ≤ cutError)
    (hf0 : ∀ x, 0 ≤ f x)
    (hfν : ∀ x, f x ≤ ν x)
    (hν0 : ∀ x, 0 ≤ ν x)
    (hp :
      ApproximatesPositivePartOnUnitInterval
        p approximationError)
    (hLF :
      HasLinearFormsCondition
        (r + 2) N ν linearFormsError)
    (hN : Nat.Coprime N (Nat.factorial (r + 1)))
    (hconvert :
      (2 : ℝ) ^ (2 ^ (r + 1)) * linearFormsError ≤
        cutError ^ (2 ^ (r + 1))) :
    ∃ g : ZMod N → ℝ, IsUnitBounded g ∧
      CutDiscrepancyLe (r + 1) f g
        (polynomialCoefficientL1 p * cutError +
          approximationError * (2 + cutError)) := by
  have hmajorantCut :
      CutDiscrepancyLe (r + 1) ν (fun _ => 1) cutError :=
    hLF.cutDiscrepancyLe_one hN hcutError hconvert
  exact
    exists_cutDiscrepancy_model_of_convolutionMomentBound
      r happrox hcutError (by positivity)
      hf0 hfν hp
      (hmajorantCut.centeredAbsoluteMean_le_two_add
        (Nat.succ_pos r) hν0)
      (hmajorantCut.hasConvolutionMomentBound p.natDegree)

end Wikipedia.SzemeredisTheorem
