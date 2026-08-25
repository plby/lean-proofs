import ErdosProblems.Erdos237b.S2ExtraCoordinate
import ErdosProblems.Erdos237b.LinearBoxLimits

/-!
# A finite rectangular certificate for the S2 lower bound

Any disjoint family of extra-coordinate boxes that lies below the product
of two projected Y-weights supplies a convergent lower bound for S2 fibers.
No smoothness, derivative bounds, or uniform fiber asymptotic is required.
-/

namespace Erdos237b

open Finset Filter BoundedGaps.Maynard
open scoped BigOperators

theorem card_extraCoordinate {H K : Finset ℕ} (e : K ≃ Option H) (m : H) :
    Fintype.card K = (univ.erase m).card + 2 := by
  have hc := Fintype.card_congr e
  have hp : 0 < Fintype.card H := Fintype.card_pos_iff.mpr ⟨m⟩
  rw [Fintype.card_option] at hc
  rw [card_erase_of_mem (mem_univ m), card_univ]
  omega

theorem finiteBoxMass_le_s2FiberDiagonal {ι : Type*} {H K : Finset ℕ}
    (e : K ≃ Option H) (m : H) {R D : ℕ} (hD : 2 ≤ D)
    {y : (H → ℕ) → ℝ} (hy : ∀ r, 0 ≤ y r)
    (I : Finset ι) (boxes : ι → Finset (K → ℕ)) (coeff : ι → ℝ)
    (hdisj : (I : Set ι).Pairwise fun i j => Disjoint (boxes i) (boxes j))
    (hle : ∀ i ∈ I, ∀ z ∈ maynardDivisorTupleSupport K R (primorial D),
      z ∈ boxes i → coeff i ≤ y (s2LiftLeft e z) * y (s2LiftRight e m z)) :
    (∑ z ∈ maynardDivisorTupleSupport K R (primorial D),
      finiteBoxWeight I boxes coeff z * reciprocalTotientTupleWeight K z) ≤
      s2FiberSquareDiagonal H R (primorial D) y m := by
  apply le_trans ?_ (extraCoordinate_sum_le_fiberDiagonal e m hD hy)
  apply sum_le_sum
  intro z hz
  apply mul_le_mul_of_nonneg_right ?_ (by unfold reciprocalTotientTupleWeight; positivity)
  exact finiteBoxWeight_le_at I boxes coeff hdisj z _ (mul_nonneg (hy _) (hy _))
    (fun i hi hzi => hle i hi z hz hzi)

theorem exists_s2Fiber_lower_sequence_of_boxes {ι : Type*} {H K : Finset ℕ}
    (e : K ≃ Option H) (m : H) {alpha : ℝ} (halpha : 0 < alpha)
    (y : ℕ → (H → ℕ) → ℝ) (hy : ∀ N r, 0 ≤ y N r)
    (I : Finset ι) (coeff : ι → ℝ) (beta gamma : ι → K → ℝ)
    (hbeta : ∀ i ∈ I, ∀ j, beta i j ∈ Set.Icc (0 : ℝ) 1)
    (hgamma : ∀ i ∈ I, ∀ j, gamma i j ∈ Set.Icc (0 : ℝ) 1)
    (horder : ∀ i ∈ I, ∀ j, beta i j ≤ gamma i j)
    (hsum : ∀ i ∈ I, (∑ j, gamma i j) < 1)
    (hdisj : ∀ᶠ N : ℕ in atTop, (I : Set ι).Pairwise fun i j =>
      Disjoint (engelsmaFractionalTupleShell K alpha (beta i) (gamma i) N)
        (engelsmaFractionalTupleShell K alpha (beta j) (gamma j) N))
    (hle : ∀ᶠ N : ℕ in atTop, ∀ i ∈ I,
      ∀ z ∈ maynardDivisorTupleSupport K (engelsmaMaynardRadius alpha N)
        (engelsmaMaynardModulus N),
      z ∈ engelsmaFractionalTupleShell K alpha (beta i) (gamma i) N →
        coeff i ≤ y N (s2LiftLeft e z) * y N (s2LiftRight e m z)) :
    ∃ b : ℕ → ℝ,
      Tendsto b atTop (nhds (∑ i ∈ I, coeff i * ∏ j, (gamma i j - beta i j))) ∧
      ∀ᶠ N : ℕ in atTop, b N ≤
        s2FiberSquareDiagonal H (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N)
          (y N) m / sieveCoordinateScale alpha N ^ ((univ.erase m).card + 2) := by
  refine ⟨_, tendsto_supported_finite_box_mass halpha I coeff beta gamma
    hbeta hgamma horder hsum, ?_⟩
  filter_upwards [hdisj, hle, eventually_sieveCoordinateScale_pos halpha,
    tendsto_shifted_tripleLogCutoff.eventually_ge_atTop 2] with N hd hl hA hD
  rw [card_extraCoordinate e m]
  exact div_le_div_of_nonneg_right
    (finiteBoxMass_le_s2FiberDiagonal e m hD (hy N) I _ coeff hd hl) (by positivity)

end Erdos237b
