/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.ProfileA11Assembly

/-!
# Finite Gaussian block factorization for HLOZ (A.12)

HLOZ split the centered Gaussian profile at finitely many scales.  The edge
crossing each split cannot literally be discarded.  This file keeps those
connector edges and proves a finite product lower bound for the resulting
restricted path family.  Every block starts at deviation zero; the preceding
block may end anywhere in its box, and one explicit Gaussian connector brings
that endpoint back to zero.
-/

open scoped BigOperators

namespace Erdos1165.GaussianBlockFactorization

noncomputable section

open GaussianSmallBall GaussianProfileReindex

/-- Terminal position of a finite killed Gaussian path. -/
def gaussianBoxPathEndpoint {R steps : ℕ} {x : ℤ}
    (p : GaussianBoxPath R steps x) : ℤ :=
  gaussianBoxPathPosition p (Fin.last steps)

lemma gaussianBoxPathEndpoint_mem {R steps : ℕ} {x : ℤ}
    (p : GaussianBoxPath R steps x) :
    gaussianBoxPathEndpoint p ∈ gaussianBox R :=
  gaussianBoxPathPosition_mem p (Fin.last steps)

/-- Product of the fixed lattice-Gaussian edges along a killed path. -/
def gaussianBoxPathWeight (l : ℕ) :
    {steps : ℕ} → {x : ℤ} → GaussianBoxPath R steps x → ℝ
  | 0, _x, _p => 1
  | _steps + 1, _x, p =>
      gaussianStepWeight l p.2.1.1 *
        gaussianBoxPathWeight (l + 1) p.2.2

lemma gaussianBoxPathWeight_nonneg (l : ℕ)
    {steps : ℕ} {x : ℤ} (p : GaussianBoxPath R steps x) :
    0 ≤ gaussianBoxPathWeight l p := by
  induction steps generalizing l x with
  | zero => simp [gaussianBoxPathWeight]
  | succ steps ih =>
      rw [gaussianBoxPathWeight]
      exact mul_nonneg (gaussianStepWeight_nonneg _ _) (ih (l + 1) p.2.2)

private lemma sum_gaussianPathWeight_zero_of_mem
    {R : ℕ} {x : ℤ} (hx : x ∈ gaussianBox R) :
    (∑ p : GaussianBoxPath R 0 x, gaussianBoxPathWeight l p) = 1 := by
  letI : Unique (GaussianBoxPath R 0 x) := {
    default := ⟨(), hx⟩
    uniq := fun p ↦ Subtype.ext (by cases p.1; rfl) }
  rw [Fintype.sum_unique]
  rfl

private lemma sum_gaussianPathWeight_zero_of_not_mem
    {R : ℕ} {x : ℤ} (hx : x ∉ gaussianBox R) :
    (∑ p : GaussianBoxPath R 0 x, gaussianBoxPathWeight l p) = 0 := by
  letI : IsEmpty (GaussianBoxPath R 0 x) := ⟨fun p ↦ hx p.2⟩
  exact Fintype.sum_empty _

/-- The recursive box partition is exactly the sum of the Gaussian weights
of its finite killed paths. -/
theorem gaussianBoxPartition_eq_sum_pathWeight
    (start steps R : ℕ) (x : ℤ) :
    gaussianBoxPartition start steps R x =
      ∑ p : GaussianBoxPath R steps x, gaussianBoxPathWeight start p := by
  induction steps generalizing start x with
  | zero =>
      by_cases hx : x ∈ gaussianBox R
      · rw [gaussianBoxPartition, if_pos hx,
          sum_gaussianPathWeight_zero_of_mem hx]
      · rw [gaussianBoxPartition, if_neg hx,
          sum_gaussianPathWeight_zero_of_not_mem hx]
  | succ steps ih =>
      by_cases hx : x ∈ gaussianBox R
      · rw [gaussianBoxPartition, if_pos hx,
          GaussianProfileReindex.sum_gaussianBoxPath_succ_of_mem hx]
        simp only [gaussianBoxPathWeight]
        simp_rw [ih]
        simp_rw [Finset.mul_sum]
        simpa using (gaussianBox R).sum_subtype
          (p := fun d : ℤ ↦ d ∈ gaussianBox R) (F := inferInstance) (by simp)
          (fun d ↦ ∑ q : GaussianBoxPath R steps (x + d),
            gaussianStepWeight start d * gaussianBoxPathWeight (start + 1) q)
      · rw [gaussianBoxPartition, if_neg hx,
          GaussianProfileReindex.sum_gaussianBoxPath_succ_of_not_mem hx]

/-- A consecutive Gaussian block, represented by its first edge scale,
number of edges, and fixed deviation radius. -/
structure GaussianBlock where
  start : ℕ
  steps : ℕ
  radius : ℕ

/-- Independent killed paths for a list of blocks. -/
def IndependentGaussianBlockPaths : List GaussianBlock → Type
  | [] => Unit
  | b :: bs => GaussianBoxPath b.radius b.steps 0 ×
      IndependentGaussianBlockPaths bs

noncomputable instance independentGaussianBlockPathsFintype
    (bs : List GaussianBlock) : Fintype (IndependentGaussianBlockPaths bs) := by
  induction bs with
  | nil =>
      change Fintype Unit
      infer_instance
  | cons b bs ih =>
      change Fintype
        (GaussianBoxPath b.radius b.steps 0 × IndependentGaussianBlockPaths bs)
      letI : Fintype (GaussianBoxPath b.radius b.steps 0) :=
        gaussianBoxPathFintype b.radius b.steps 0
      letI : Fintype (IndependentGaussianBlockPaths bs) := ih
      infer_instance

/-- Full weight of independent blocks with every omitted scale restored as
an explicit Gaussian connector from the previous endpoint to zero. -/
def connectedGaussianBlockWeight :
    {bs : List GaussianBlock} → IndependentGaussianBlockPaths bs → ℝ
  | [], _ => 1
  | [b], p => gaussianBoxPathWeight b.start p.1
  | b :: c :: bs, p =>
      gaussianBoxPathWeight b.start p.1 *
        gaussianStepWeight (b.start + b.steps)
          (-gaussianBoxPathEndpoint p.1) *
        connectedGaussianBlockWeight p.2

lemma connectedGaussianBlockWeight_nonneg
    {bs : List GaussianBlock} (p : IndependentGaussianBlockPaths bs) :
    0 ≤ connectedGaussianBlockWeight p := by
  induction bs with
  | nil => simp [connectedGaussianBlockWeight]
  | cons b bs ih =>
      cases bs with
      | nil =>
          simpa [connectedGaussianBlockWeight] using
            gaussianBoxPathWeight_nonneg b.start p.1
      | cons c bs =>
          rw [connectedGaussianBlockWeight]
          exact mul_nonneg
            (mul_nonneg (gaussianBoxPathWeight_nonneg b.start p.1)
              (gaussianStepWeight_nonneg _ _))
            (ih p.2)

/-- Uniform lower bound for one connector edge leaving a block of radius
`R`. -/
def gaussianConnectorFloor (l R : ℕ) : ℝ :=
  Real.exp (-((R : ℝ) ^ 2) / (8 * (l : ℝ) ^ 2)) /
    (2 * Real.sqrt (2 * Real.pi) * l)

lemma gaussianConnectorFloor_nonneg (l R : ℕ) :
    0 ≤ gaussianConnectorFloor l R := by
  unfold gaussianConnectorFloor
  positivity

/-- Additive exponent of the explicit connector floor. -/
def gaussianConnectorCost (l R : ℕ) : ℝ :=
  (R : ℝ) ^ 2 / (8 * (l : ℝ) ^ 2) +
    Real.log (2 * Real.sqrt (2 * Real.pi) * l)

lemma exp_neg_gaussianConnectorCost_eq {l R : ℕ} (hl : 0 < l) :
    Real.exp (-gaussianConnectorCost l R) =
      gaussianConnectorFloor l R := by
  have hden : (0 : ℝ) < 2 * Real.sqrt (2 * Real.pi) * l := by positivity
  unfold gaussianConnectorCost gaussianConnectorFloor
  rw [neg_add, Real.exp_add]
  have hlog : Real.exp (-Real.log
      (2 * Real.sqrt (2 * Real.pi) * (l : ℝ))) =
      (2 * Real.sqrt (2 * Real.pi) * (l : ℝ))⁻¹ := by
    rw [Real.exp_neg, Real.exp_log hden]
  rw [hlog, div_eq_mul_inv]
  congr 1 <;> ring

lemma gaussianConnectorFloor_le {l R : ℕ} {x : ℤ}
    (hl : 0 < l) (hx : x ∈ gaussianBox R) :
    gaussianConnectorFloor l R ≤ gaussianStepWeight l (-x) := by
  have habs := (mem_gaussianBox.mp hx)
  have hsq : ((x : ℝ) ^ 2) ≤ (R : ℝ) ^ 2 := by
    have hxabs : |x| ≤ (R : ℤ) := by
      rw [abs_le]
      exact habs
    have hxabsReal : |(x : ℝ)| ≤ (R : ℝ) := by exact_mod_cast hxabs
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hxabsReal 2
  unfold gaussianConnectorFloor gaussianStepWeight
  have hden : 0 ≤ 2 * Real.sqrt (2 * Real.pi) * (l : ℝ) := by positivity
  apply div_le_div_of_nonneg_right _ hden
  apply Real.exp_le_exp.mpr
  have hl2 : (0 : ℝ) < 8 * (l : ℝ) ^ 2 := by positivity
  rw [Int.cast_neg, neg_sq]
  calc
    -((R : ℝ) ^ 2) / (8 * (l : ℝ) ^ 2) =
        -((R : ℝ) ^ 2 / (8 * (l : ℝ) ^ 2)) := by ring
    _ ≤ -((x : ℝ) ^ 2 / (8 * (l : ℝ) ^ 2)) :=
      neg_le_neg (div_le_div_of_nonneg_right hsq hl2.le)
    _ = -((x : ℝ) ^ 2) / (8 * (l : ℝ) ^ 2) := by ring

/-- Recursive product of the block partition masses and connector floors. -/
def gaussianBlockProductLower : List GaussianBlock → ℝ
  | [] => 1
  | [b] => gaussianBoxPartition b.start b.steps b.radius 0
  | b :: c :: bs =>
      gaussianBoxPartition b.start b.steps b.radius 0 *
      gaussianConnectorFloor (b.start + b.steps) b.radius *
        gaussianBlockProductLower (c :: bs)

/-- Spectral exponent furnished by `gaussianBoxPartition_ge_exp` for one
block, using its own terminal scale as the common variance bound. -/
def gaussianBlockSpectralCost (b : GaussianBlock) : ℝ :=
  1280 * (b.steps : ℝ) * (b.start + b.steps : ℕ) ^ 2 /
    (b.radius : ℝ) ^ 2

/-- Total additive spectral plus connector exponent for a block list. -/
def gaussianBlockTotalCost : List GaussianBlock → ℝ
  | [] => 0
  | [b] => gaussianBlockSpectralCost b
  | b :: c :: bs =>
      gaussianBlockSpectralCost b +
        gaussianConnectorCost (b.start + b.steps) b.radius +
        gaussianBlockTotalCost (c :: bs)

lemma gaussianBlockTotalCost_nonneg (bs : List GaussianBlock)
    (hpositive : ∀ b ∈ bs, 0 < b.start)
    (hradius : ∀ b ∈ bs, 0 < b.radius) :
    0 ≤ gaussianBlockTotalCost bs := by
  induction bs with
  | nil => simp [gaussianBlockTotalCost]
  | cons b bs ih =>
      cases bs with
      | nil =>
          unfold gaussianBlockTotalCost gaussianBlockSpectralCost
          positivity
      | cons c bs =>
          rw [gaussianBlockTotalCost]
          have hbstart := hpositive b (by simp)
          have hbR := hradius b (by simp)
          have htail := ih
            (fun d hd ↦ hpositive d (by simp [hd]))
            (fun d hd ↦ hradius d (by simp [hd]))
          unfold gaussianBlockSpectralCost gaussianConnectorCost
          have hlog : 0 ≤
              Real.log (2 * Real.sqrt (2 * Real.pi) * (b.start + b.steps)) := by
            apply Real.log_nonneg
            have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi) := by
              rw [← Real.sqrt_one]
              apply Real.sqrt_le_sqrt
              nlinarith [Real.pi_gt_three]
            have hscaleNat : 1 ≤ b.start + b.steps := by omega
            have hscale : (1 : ℝ) ≤ b.start + b.steps := by
              exact_mod_cast hscaleNat
            nlinarith
          have hspectral : 0 ≤ gaussianBlockSpectralCost b := by
            unfold gaussianBlockSpectralCost
            positivity
          have hconnector : 0 ≤
              gaussianConnectorCost (b.start + b.steps) b.radius := by
            unfold gaussianConnectorCost
            have hlog' : 0 ≤ Real.log
                (2 * Real.sqrt (2 * Real.pi) *
                  ((b.start + b.steps : ℕ) : ℝ)) := by
              simpa only [Nat.cast_add] using hlog
            exact add_nonneg (by positivity) hlog'
          exact add_nonneg (add_nonneg hspectral hconnector) htail

lemma gaussianBlockProductLower_nonneg : ∀ bs,
    0 ≤ gaussianBlockProductLower bs
  | [] => by simp [gaussianBlockProductLower]
  | [b] => gaussianBoxPartition_nonneg _ _ _ _
  | b :: c :: bs => by
      rw [gaussianBlockProductLower]
      exact mul_nonneg
        (mul_nonneg (gaussianBoxPartition_nonneg _ _ _ _)
          (gaussianConnectorFloor_nonneg _ _))
        (gaussianBlockProductLower_nonneg (c :: bs))

/-- Product-form spectral lower bound for every block and every retained
connector.  This is the quantitative finite engine needed before choosing
the geometric HLOZ split scales. -/
theorem exp_neg_gaussianBlockTotalCost_le
    (bs : List GaussianBlock)
    (hstart : ∀ b ∈ bs, 0 < b.start)
    (hscale : ∀ b ∈ bs,
      (2560 : ℝ) * (b.start + b.steps : ℕ) ^ 2 ≤
        (b.radius : ℝ) ^ 2) :
    Real.exp (-gaussianBlockTotalCost bs) ≤
      gaussianBlockProductLower bs := by
  induction bs with
  | nil => simp [gaussianBlockTotalCost, gaussianBlockProductLower]
  | cons b bs ih =>
      cases bs with
      | nil =>
          rw [gaussianBlockTotalCost, gaussianBlockProductLower]
          have hb0 := gaussianBoxPartition_ge_exp
            (hstart b (by simp))
            (show b.start + b.steps ≤ b.start + b.steps from le_rfl)
            (hscale b (by simp))
          convert hb0 using 1 <;>
            simp only [gaussianBlockSpectralCost, Nat.cast_add] <;> ring
      | cons c bs =>
          rw [gaussianBlockTotalCost, gaussianBlockProductLower]
          have hb0 := gaussianBoxPartition_ge_exp
            (hstart b (by simp)) (show b.start + b.steps ≤
              b.start + b.steps by rfl) (hscale b (by simp))
          have hb : Real.exp (-gaussianBlockSpectralCost b) ≤
              gaussianBoxPartition b.start b.steps b.radius 0 := by
            convert hb0 using 1 <;>
              simp only [gaussianBlockSpectralCost, Nat.cast_add] <;> ring
          have hc := ih
            (fun d hd ↦ hstart d (by simp [hd]))
            (fun d hd ↦ hscale d (by simp [hd]))
          have hbstart := hstart b (by simp)
          have hbend : 0 < b.start + b.steps := by omega
          have hconn := exp_neg_gaussianConnectorCost_eq
            (R := b.radius) hbend
          calc
            Real.exp
                (-(gaussianBlockSpectralCost b +
                  gaussianConnectorCost (b.start + b.steps) b.radius +
                  gaussianBlockTotalCost (c :: bs))) =
                Real.exp (-gaussianBlockSpectralCost b) *
                  Real.exp
                    (-gaussianConnectorCost (b.start + b.steps) b.radius) *
                  Real.exp (-gaussianBlockTotalCost (c :: bs)) := by
              rw [show -(gaussianBlockSpectralCost b +
                    gaussianConnectorCost (b.start + b.steps) b.radius +
                    gaussianBlockTotalCost (c :: bs)) =
                  -gaussianBlockSpectralCost b +
                    -gaussianConnectorCost (b.start + b.steps) b.radius +
                    -gaussianBlockTotalCost (c :: bs) by ring,
                Real.exp_add, Real.exp_add]
            _ ≤ gaussianBoxPartition b.start b.steps b.radius 0 *
                  gaussianConnectorFloor (b.start + b.steps) b.radius *
                  gaussianBlockProductLower (c :: bs) := by
              rw [hconn]
              exact mul_le_mul
                (mul_le_mul_of_nonneg_right hb
                  (gaussianConnectorFloor_nonneg _ _)) hc
                (Real.exp_nonneg _)
                (mul_nonneg (gaussianBoxPartition_nonneg _ _ _ _)
                  (gaussianConnectorFloor_nonneg _ _))

/-- **Finite HLOZ (A.12) block factorization.**

The left side retains an explicit uniformly valid lower bound for every
connector edge.  The right side is the exact finite sum over the restricted
family of connected block paths. -/
theorem gaussianBlockProductLower_le_sum_connected
    (bs : List GaussianBlock)
    (hpositive : ∀ b ∈ bs, 0 < b.start + b.steps) :
    gaussianBlockProductLower bs ≤
      ∑ p : IndependentGaussianBlockPaths bs,
        connectedGaussianBlockWeight p := by
  induction bs with
  | nil =>
      change (1 : ℝ) ≤ ∑ _p : Unit, 1
      simp
  | cons b bs ih =>
      cases bs with
      | nil =>
          rw [gaussianBlockProductLower,
            gaussianBoxPartition_eq_sum_pathWeight]
          change (∑ p : GaussianBoxPath b.radius b.steps 0,
              gaussianBoxPathWeight b.start p) ≤
            ∑ p : GaussianBoxPath b.radius b.steps 0 × Unit,
              gaussianBoxPathWeight b.start p.1
          rw [Fintype.sum_prod_type]
          simp
      | cons c bs =>
          rw [gaussianBlockProductLower]
          have hbpos : 0 < b.start + b.steps :=
            hpositive b (by simp)
          have htail := ih (fun d hd ↦ hpositive d (by simp [hd]))
          have hsumfactor :
              (∑ p : IndependentGaussianBlockPaths (b :: c :: bs),
                  connectedGaussianBlockWeight p) =
                (∑ p : GaussianBoxPath b.radius b.steps 0,
                    gaussianBoxPathWeight b.start p *
                      gaussianStepWeight (b.start + b.steps)
                        (-gaussianBoxPathEndpoint p)) *
                  (∑ q : IndependentGaussianBlockPaths (c :: bs),
                    connectedGaussianBlockWeight q) := by
            change (∑ p : GaussianBoxPath b.radius b.steps 0 ×
                IndependentGaussianBlockPaths (c :: bs),
                gaussianBoxPathWeight b.start p.1 *
                    gaussianStepWeight (b.start + b.steps)
                      (-gaussianBoxPathEndpoint p.1) *
                  connectedGaussianBlockWeight p.2) = _
            rw [Fintype.sum_prod_type]
            simp_rw [← Finset.mul_sum]
            rw [← Finset.sum_mul]
          have hfirst :
              gaussianBoxPartition b.start b.steps b.radius 0 *
                  gaussianConnectorFloor (b.start + b.steps) b.radius ≤
                ∑ p : GaussianBoxPath b.radius b.steps 0,
                  gaussianBoxPathWeight b.start p *
                    gaussianStepWeight (b.start + b.steps)
                      (-gaussianBoxPathEndpoint p) := by
            rw [gaussianBoxPartition_eq_sum_pathWeight, Finset.sum_mul]
            exact Finset.sum_le_sum fun p _ ↦
              mul_le_mul_of_nonneg_left
                (gaussianConnectorFloor_le hbpos
                  (gaussianBoxPathEndpoint_mem p))
                (gaussianBoxPathWeight_nonneg b.start p)
          rw [hsumfactor]
          exact mul_le_mul hfirst htail
            (gaussianBlockProductLower_nonneg (c :: bs))
            (Finset.sum_nonneg fun p _ ↦
              mul_nonneg (gaussianBoxPathWeight_nonneg b.start p)
                (gaussianStepWeight_nonneg _ _))

/-- The spectral and connector costs combine directly into a lower bound for
the full restricted family of connected block paths.  All hypotheses are
finite, deterministic checks on the supplied block list. -/
theorem exp_neg_gaussianBlockTotalCost_le_sum_connected
    (bs : List GaussianBlock)
    (hstart : ∀ b ∈ bs, 0 < b.start)
    (hscale : ∀ b ∈ bs,
      (2560 : ℝ) * (b.start + b.steps : ℕ) ^ 2 ≤
        (b.radius : ℝ) ^ 2) :
    Real.exp (-gaussianBlockTotalCost bs) ≤
      ∑ p : IndependentGaussianBlockPaths bs,
        connectedGaussianBlockWeight p := by
  exact (exp_neg_gaussianBlockTotalCost_le bs hstart hscale).trans
    (gaussianBlockProductLower_le_sum_connected bs fun b hb ↦ by
      have := hstart b hb
      omega)

end

end Erdos1165.GaussianBlockFactorization
