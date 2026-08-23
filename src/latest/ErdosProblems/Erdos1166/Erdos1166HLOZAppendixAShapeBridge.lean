import ErdosProblems.Erdos1166.Erdos1166HLOZProp13FromAppendix

/-!
# Euclidean-disk to square-exit bridge for HLOZ Appendix A

HLOZ (A.1) uses the first exit from the closed Euclidean lattice disk
`D(0, K_j)`, whereas the internal exit-tail module uses the square of integer
radius `ceil (K_j)`.  This file records the shape comparison, including the
rounding.

Both natural-valued exit-time definitions use `0` on paths which never exit.
Consequently the time comparison is pointwise only when square exit exists.
The existing geometric survival estimate proves that the exceptional set is
null, which is exactly enough for the probability comparison.
-/

namespace Erdos1166.HLOZAppendixAShapeBridge

open Filter MeasureTheory Set
open scoped ENNReal

open KilledGreen ExitTail HLOZAppendixA HLOZExitTail
  HLOZProp13FromAppendix

/-- Euclidean norm of a planar lattice site. -/
noncomputable def siteEuclideanNorm (z : Site) : ℝ :=
  Real.sqrt ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2)

/-- The source's closed Euclidean lattice disk `D(0,K)`. -/
def euclideanLatticeDisk (K : ℝ) : Set Site :=
  {z | siteEuclideanNorm z ≤ K}

theorem zero_mem_euclideanLatticeDisk {K : ℝ} (hK : 0 ≤ K) :
    (0, 0) ∈ euclideanLatticeDisk K := by
  simp [euclideanLatticeDisk, siteEuclideanNorm, hK]

/-- The closed Euclidean disk of nonnegative real radius `K` lies in the
closed lattice square of integer radius `ceil K`. -/
theorem euclideanLatticeDisk_subset_squareDisk
    {K : ℝ} :
    euclideanLatticeDisk K ⊆
      (KilledGreen.squareDisk (Nat.ceil K) : Set Site) := by
  intro z hz
  change siteEuclideanNorm z ≤ K at hz
  have hcoord₁ : |(z.1 : ℝ)| ≤ siteEuclideanNorm z := by
    apply Real.abs_le_sqrt
    nlinarith [sq_nonneg (z.2 : ℝ)]
  have hcoord₂ : |(z.2 : ℝ)| ≤ siteEuclideanNorm z := by
    apply Real.abs_le_sqrt
    nlinarith [sq_nonneg (z.1 : ℝ)]
  have hceil : K ≤ (Nat.ceil K : ℝ) := Nat.le_ceil K
  have h₁real : |(z.1 : ℝ)| ≤ (Nat.ceil K : ℝ) :=
    hcoord₁.trans (hz.trans hceil)
  have h₂real : |(z.2 : ℝ)| ≤ (Nat.ceil K : ℝ) :=
    hcoord₂.trans (hz.trans hceil)
  have h₁int : |z.1| ≤ (Nat.ceil K : ℤ) := by
    exact_mod_cast h₁real
  have h₂int : |z.2| ≤ (Nat.ceil K : ℤ) := by
    exact_mod_cast h₂real
  rw [KilledGreen.squareDisk]
  apply Finset.mem_product.mpr
  exact ⟨Finset.mem_Icc.mpr (abs_le.mp h₁int),
    Finset.mem_Icc.mpr (abs_le.mp h₂int)⟩

/-- Natural-valued first exit from the source's Euclidean disk.  As in
`squareExitTimeNat`, the value is `0` on a path which never exits. -/
noncomputable def euclideanExitTime (K : ℝ)
    (ω : ℕ → Direction) : ℕ := by
  classical
  exact if h : ∃ n, walkFrom (0, 0) ω n ∉ euclideanLatticeDisk K then
    Nat.find h
  else 0

def squareExitExists (R : ℕ) (ω : ℕ → Direction) : Prop :=
  ∃ n, walkFrom (0, 0) ω n ∉ squareDisk R

def squareNeverExits (R : ℕ) : Set (ℕ → Direction) :=
  {ω | ∀ n, walkFrom (0, 0) ω n ∈ squareDisk R}

theorem not_squareExitExists_iff_mem_squareNeverExits
    (R : ℕ) (ω : ℕ → Direction) :
    ¬squareExitExists R ω ↔ ω ∈ squareNeverExits R := by
  simp [squareExitExists, squareNeverExits]

/-- On paths that do leave the larger square, the Euclidean exit occurs no
later.  This is the exact deterministic shape comparison. -/
theorem euclideanExitTime_le_squareExitTimeNat
    {K : ℝ} {ω : ℕ → Direction}
    (hexit : squareExitExists (Nat.ceil K) ω) :
    euclideanExitTime K ω ≤
      squareExitTimeNat (Nat.ceil K) (0, 0) ω := by
  classical
  change ∃ n, walkFrom (0, 0) ω n ∉ squareDisk (Nat.ceil K) at hexit
  let hsub := euclideanLatticeDisk_subset_squareDisk (K := K)
  have heuclidean :
      ∃ n, walkFrom (0, 0) ω n ∉ euclideanLatticeDisk K := by
    obtain ⟨n, hn⟩ := hexit
    exact ⟨n, fun hmem ↦ hn (hsub hmem)⟩
  rw [euclideanExitTime, dif_pos heuclidean]
  rw [squareExitTimeNat, dif_pos hexit]
  apply Nat.find_min' heuclidean
  intro hmem
  exact (Nat.find_spec hexit) (hsub hmem)

/-- For nonnegative radius, the finite Euclidean exit time is positive.  Thus
it agrees with the source convention `H_{D(0,K)^c}=inf{k>0:S_k∉D(0,K)}`. -/
theorem euclideanExitTime_pos_of_exit
    {K : ℝ} (hK : 0 ≤ K) {ω : ℕ → Direction}
    (hexit : ∃ n, walkFrom (0, 0) ω n ∉ euclideanLatticeDisk K) :
    0 < euclideanExitTime K ω := by
  classical
  rw [euclideanExitTime, dif_pos hexit]
  apply Nat.pos_of_ne_zero
  intro hzero
  have hspec := Nat.find_spec hexit
  rw [hzero] at hspec
  exact hspec (by simpa [walkFrom, simpleRandomWalk] using
    zero_mem_euclideanLatticeDisk hK)

/-- The set of increment paths which never leave a fixed finite square has
zero canonical probability. -/
theorem measure_squareNeverExits_eq_zero (R : ℕ) :
    incrementLaw (squareNeverExits R) = 0 := by
  refine ENNReal.eq_zero_of_le_mul_pow
      (x := incrementLaw (squareNeverExits R))
      (ε := (1 : NNReal))
      (r := (4 : ENNReal)⁻¹) (by norm_num) ?_
  intro q
  calc
    incrementLaw (squareNeverExits R) ≤
        survivalWeight (squareDisk R : Set Site) (0, 0)
          (q * diffusiveExitBlockLength R) := by
      apply measure_mono
      intro ω hω n hn
      exact hω n
    _ ≤ ((4 : ℝ≥0∞)⁻¹) ^ q :=
      survivalWeight_mulDiffusiveBlock_le R q (0, 0)
    _ = ((1 : NNReal) : ENNReal) * ((4 : ENNReal)⁻¹) ^ q := by simp

theorem ae_squareExitExists (R : ℕ) :
    ∀ᵐ ω ∂incrementLaw, squareExitExists R ω := by
  rw [ae_iff]
  have heq : {ω : ℕ → Direction | ¬squareExitExists R ω} =
      squareNeverExits R := by
    ext ω
    exact not_squareExitExists_iff_mem_squareNeverExits R ω
  rw [heq]
  exact measure_squareNeverExits_eq_zero R

theorem K_nonneg (j : ℕ) : 0 ≤ K j := by
  unfold K
  positivity

/-- Euclidean exit at the published radius is almost surely no later than the
square exit at the explicitly rounded radius `ceil (K j)`. -/
theorem ae_euclideanExitTime_le_exitTime (j : ℕ) :
    ∀ᵐ ω ∂incrementLaw,
      euclideanExitTime (K j) ω ≤ HLOZExitTail.exitTime j ω := by
  filter_upwards [ae_squareExitExists (HLOZExitTail.radius j)] with ω hω
  exact euclideanExitTime_le_squareExitTimeNat hω

/-- The event appearing literally in the published Euclidean-disk estimate
(A.1), expressed using the common `diskGood` threshold interface. -/
def euclideanDiskGood (ε : ℝ) (j : ℕ) : Set (ℕ → Direction) :=
  diskGood
    (fun ω n ↦ maxLocalTime (simpleRandomWalk ω) n)
    (fun j ω ↦ euclideanExitTime (K j) ω) ε j

/-- Monotonicity of maximal local time transfers Euclidean-disk success into
the square-exit success event, modulo the null non-exit set. -/
theorem ae_euclideanDiskGood_le_squareDiskGood (ε : ℝ) (j : ℕ) :
    euclideanDiskGood ε j ≤ᵐ[incrementLaw]
      diskGood
        (fun ω n ↦ maxLocalTime (simpleRandomWalk ω) n)
        HLOZExitTail.exitTime ε j := by
  filter_upwards [ae_euclideanExitTime_le_exitTime j] with ω htime
  intro hgood
  change diskThreshold ε j ≤
      (maxLocalTime (simpleRandomWalk ω)
        (euclideanExitTime (K j) ω) : ℝ) at hgood
  change diskThreshold ε j ≤
      (maxLocalTime (simpleRandomWalk ω)
        (HLOZExitTail.exitTime j ω) : ℝ)
  have hmono := maxLocalTime_mono
    (s := simpleRandomWalk ω) htime
  exact hgood.trans (by exact_mod_cast hmono)

theorem measure_euclideanDiskGood_le_squareDiskGood (ε : ℝ) (j : ℕ) :
    incrementLaw (euclideanDiskGood ε j) ≤
      incrementLaw
        (diskGood
          (fun ω n ↦ maxLocalTime (simpleRandomWalk ω) n)
          HLOZExitTail.exitTime ε j) :=
  measure_mono_ae (ae_euclideanDiskGood_le_squareDiskGood ε j)

/-- The published Euclidean form of the one remaining Appendix-A estimate. -/
def EuclideanAppendixDiskEstimate : Prop :=
  ∀ᶠ j : ℕ in atTop,
    ENNReal.ofReal
        (Real.exp
          (-((j : ℝ) ^
            (3 / 5 + appendixEpsilon / 3 : ℝ)))) <
      incrementLaw (euclideanDiskGood appendixEpsilon j)

/-- Source-facing shape bridge: the published Euclidean-disk estimate (A.1)
implies the square-exit `AppendixDiskEstimate` consumed downstream. -/
theorem appendixDiskEstimate_of_euclidean
    (hsource : EuclideanAppendixDiskEstimate) :
    AppendixDiskEstimate := by
  filter_upwards [hsource] with j hj
  exact hj.trans_le
    (measure_euclideanDiskGood_le_squareDiskGood appendixEpsilon j)

end Erdos1166.HLOZAppendixAShapeBridge
