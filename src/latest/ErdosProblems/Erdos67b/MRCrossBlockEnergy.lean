import ErdosProblems.Erdos67b.MRPrimeCofactorMoment

/-!
# Frequency restriction using different prime blocks

A large preceding prime block raises the cofactor to the product moment;
a small current block supplies its own square saving. The two blocks are
independent, as required by the multiscale argument.
-/

open scoped BigOperators Interval
open MeasureTheory

namespace Erdos67b

theorem continuous_logarithmicDirichletPolynomial (S : Finset ℕ) (a : ℕ → ℂ) :
    Continuous (logarithmicDirichletPolynomial S a) := by
  unfold logarithmicDirichletPolynomial logarithmicPhase
  fun_prop

/-- A lower bound for one factor pays for an arbitrary integral power. -/
theorem norm_sq_le_inv_pow_mul_norm_sq_power_mul
    {z w : ℂ} {V : ℝ} (hV : 0 < V) (hz : V ≤ ‖z‖) (k : ℕ) :
    ‖w‖ ^ 2 ≤ (V ^ (2 * k))⁻¹ * ‖z ^ k * w‖ ^ 2 := by
  have hpow := pow_le_pow_left₀ hV.le hz (2 * k)
  rw [mul_comm, ← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos hV _)).mpr
  calc
    ‖w‖ ^ 2 * V ^ (2 * k) ≤ ‖w‖ ^ 2 * ‖z‖ ^ (2 * k) :=
      mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
    _ = ‖z ^ k * w‖ ^ 2 := by
      rw [norm_mul, norm_pow, mul_pow, Nat.mul_comm 2 k, pow_mul]
      ring

/-- Integrable restriction to a measurable frequency class. The large
factor and the small factor may be different functions. -/
theorem intervalIntegral_indicator_norm_sq_mul_le_cross_power
    {F Q R : ℝ → ℂ} (hF : Continuous F) (hQ : Continuous Q) (hR : Continuous R)
    {E : Set ℝ} (hE : MeasurableSet E) {T W V : ℝ}
    (hT : 0 ≤ T) (_hW : 0 ≤ W) (hV : 0 < V)
    (hsmall : ∀ t ∈ E, t ∈ Set.Icc (-T) T → ‖F t‖ ≤ W)
    (hlarge : ∀ t ∈ E, t ∈ Set.Icc (-T) T → V ≤ ‖Q t‖) (k : ℕ) :
    (∫ t in -T..T, E.indicator (fun t ↦ ‖F t * R t‖ ^ 2) t) ≤
      (W ^ 2 * (V ^ (2 * k))⁻¹) * ∫ t in -T..T, ‖Q t ^ k * R t‖ ^ 2 := by
  have hbase : Continuous (fun t ↦ ‖F t * R t‖ ^ 2) := (hF.mul hR).norm.pow 2
  have hmajor : Continuous (fun t ↦
      (W ^ 2 * (V ^ (2 * k))⁻¹) * ‖Q t ^ k * R t‖ ^ 2) := by fun_prop
  have hbaseInt : IntervalIntegrable
      (E.indicator (fun t ↦ ‖F t * R t‖ ^ 2)) volume (-T) T := by
    rw [intervalIntegrable_iff]
    exact (intervalIntegrable_iff.mp (hbase.intervalIntegrable (-T) T)).indicator hE
  have hpoint : ∀ t ∈ Set.Icc (-T) T,
      E.indicator (fun t ↦ ‖F t * R t‖ ^ 2) t ≤
        (W ^ 2 * (V ^ (2 * k))⁻¹) * ‖Q t ^ k * R t‖ ^ 2 := by
    intro t ht
    by_cases htE : t ∈ E
    · rw [Set.indicator_of_mem htE, norm_mul, mul_pow]
      calc
        _ ≤ W ^ 2 * ‖R t‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hsmall t htE ht) 2)
            (sq_nonneg _)
        _ ≤ W ^ 2 * ((V ^ (2 * k))⁻¹ * ‖Q t ^ k * R t‖ ^ 2) :=
          mul_le_mul_of_nonneg_left
            (norm_sq_le_inv_pow_mul_norm_sq_power_mul hV (hlarge t htE ht) k) (sq_nonneg _)
        _ = _ := by ring
    · rw [Set.indicator_of_notMem htE]
      positivity
  have hm := intervalIntegral.integral_mono_on (by linarith : -T ≤ T)
    hbaseInt (hmajor.intervalIntegrable (-T) T) hpoint
  rwa [intervalIntegral.integral_const_mul] at hm

/-- Cross-block energy with the explicit uniform prime-band moment. -/
theorem crossBlockEnergy_le_dyadic_moment
    {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hS : ∀ m ∈ S, 0 < m)
    {a b : ℕ → ℂ} (ha : ∀ p ∈ P, ‖a p‖ ≤ (p : ℝ)⁻¹)
    (hb : ∀ m ∈ S, ‖b m‖ ≤ (m : ℝ)⁻¹)
    {Y X N k : ℕ} (hY : 2 ≤ Y) (hPY : P ⊆ Finset.Icc Y (2 * Y))
    (hX : 0 < X) (hN : 0 < N)
    (hD : natProductImage (primePowerSupport P k) S ⊆ Finset.Icc X N)
    {F : ℝ → ℂ} (hF : Continuous F) {E : Set ℝ} (hE : MeasurableSet E)
    {T W V : ℝ} (hT : 0 ≤ T) (hW : 0 ≤ W) (hV : 0 < V)
    (hsmall : ∀ t ∈ E, t ∈ Set.Icc (-T) T → ‖F t‖ ≤ W)
    (hlarge : ∀ t ∈ E, t ∈ Set.Icc (-T) T →
      V ≤ ‖logarithmicDirichletPolynomial P a t‖) :
    (∫ t in -T..T, E.indicator
      (fun t ↦ ‖F t * logarithmicDirichletPolynomial S b t‖ ^ 2) t) ≤
      (W ^ 2 * (V ^ (2 * k))⁻¹) *
        (8 * Real.exp 12 * (k.factorial : ℝ) ^ 2 * (T / X + Real.pi * N / X)) := by
  apply (intervalIntegral_indicator_norm_sq_mul_le_cross_power hF
    (continuous_logarithmicDirichletPolynomial P a)
    (continuous_logarithmicDirichletPolynomial S b) hE hT hW hV hsmall hlarge k).trans
  exact mul_le_mul_of_nonneg_left
    (primeCofactorPolynomial_dyadic_intervalIntegral_le hP hS ha hb hY hPY hX hN hD hT)
    (by positivity)

/-- A finite measurable cover may overlap: nonnegativity bounds the
covered energy by the sum of the energies of the covering pieces. -/
theorem intervalIntegral_indicator_le_sum_cover
    {ι : Type*} (I : Finset ι) {E : Set ℝ} {A : ι → Set ℝ}
    (hE : MeasurableSet E) (hA : ∀ i ∈ I, MeasurableSet (A i))
    {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ t, 0 ≤ g t)
    {T : ℝ} (hT : 0 ≤ T)
    (hcover : ∀ t ∈ E, t ∈ Set.Icc (-T) T → ∃ i ∈ I, t ∈ A i) :
    (∫ t in -T..T, E.indicator g t) ≤ ∑ i ∈ I, ∫ t in -T..T, (A i).indicator g t := by
  classical
  have hint (B : Set ℝ) (hB : MeasurableSet B) :
      IntervalIntegrable (B.indicator g) volume (-T) T := by
    rw [intervalIntegrable_iff]
    exact (intervalIntegrable_iff.mp (hg.intervalIntegrable (-T) T)).indicator hB
  have hpoint : ∀ t ∈ Set.Icc (-T) T,
      E.indicator g t ≤ ∑ i ∈ I, (A i).indicator g t := by
    intro t ht
    have hnonneg (i : ι) : 0 ≤ (A i).indicator g t := Set.indicator_nonneg (fun _ _ ↦ hg0 _) _
    by_cases htE : t ∈ E
    · obtain ⟨i, hi, hti⟩ := hcover t htE ht
      rw [Set.indicator_of_mem htE]
      calc
        g t = (A i).indicator g t := (Set.indicator_of_mem hti g).symm
        _ ≤ ∑ j ∈ I, (A j).indicator g t :=
          Finset.single_le_sum (fun j _ ↦ hnonneg j) hi
    · rw [Set.indicator_of_notMem htE]
      exact Finset.sum_nonneg (fun i _ ↦ hnonneg i)
  have hsumInt : IntervalIntegrable (fun t ↦ ∑ i ∈ I, (A i).indicator g t)
      volume (-T) T := by
    have heq : (fun t ↦ ∑ i ∈ I, (A i).indicator g t) =
        ∑ i ∈ I, (A i).indicator g := by
      funext t
      simp only [Finset.sum_apply]
    rw [heq]
    exact IntervalIntegrable.sum I (fun i hi ↦ hint (A i) (hA i hi))
  have hm := intervalIntegral.integral_mono_on (by linarith : -T ≤ T)
    (hint E hE) hsumInt hpoint
  rwa [intervalIntegral.integral_finsetSum (fun i hi ↦ hint (A i) (hA i hi))] at hm

/-- Cover a current small-block class by large preceding subblocks and
sum their independently powered cross-block moments. -/
theorem crossBlockEnergy_le_sum_dyadic_moments
    {ι : Type*} (I : Finset ι) (P : ι → Finset ℕ) (S : Finset ℕ)
    (a : ι → ℕ → ℂ) (b : ℕ → ℂ)
    (Y N k : ι → ℕ) (V : ι → ℝ)
    (hP : ∀ i ∈ I, ∀ p ∈ P i, p.Prime) (hS : ∀ m ∈ S, 0 < m)
    (ha : ∀ i ∈ I, ∀ p ∈ P i, ‖a i p‖ ≤ (p : ℝ)⁻¹)
    (hb : ∀ m ∈ S, ‖b m‖ ≤ (m : ℝ)⁻¹)
    (hY : ∀ i ∈ I, 2 ≤ Y i) (hPY : ∀ i ∈ I, P i ⊆ Finset.Icc (Y i) (2 * Y i))
    {X : ℕ} (hX : 0 < X) (hN : ∀ i ∈ I, 0 < N i)
    (hD : ∀ i ∈ I, natProductImage (primePowerSupport (P i) (k i)) S ⊆ Finset.Icc X (N i))
    {F : ℝ → ℂ} (hF : Continuous F) {E : Set ℝ} (hE : MeasurableSet E)
    {T W : ℝ} (hT : 0 ≤ T) (hW : 0 ≤ W) (hV : ∀ i ∈ I, 0 < V i)
    (hsmall : ∀ t ∈ E, t ∈ Set.Icc (-T) T → ‖F t‖ ≤ W)
    (hcover : ∀ t ∈ E, t ∈ Set.Icc (-T) T →
      ∃ i ∈ I, V i ≤ ‖logarithmicDirichletPolynomial (P i) (a i) t‖) :
    (∫ t in -T..T, E.indicator
      (fun t ↦ ‖F t * logarithmicDirichletPolynomial S b t‖ ^ 2) t) ≤
      ∑ i ∈ I, (W ^ 2 * (V i ^ (2 * k i))⁻¹) *
        (8 * Real.exp 12 * ((k i).factorial : ℝ) ^ 2 * (T / X + Real.pi * N i / X)) := by
  classical
  let A : ι → Set ℝ := fun i ↦ E ∩
    {t | V i ≤ ‖logarithmicDirichletPolynomial (P i) (a i) t‖}
  have hA (i : ι) : MeasurableSet (A i) := hE.inter
    (measurableSet_le measurable_const
      (continuous_logarithmicDirichletPolynomial (P i) (a i)).norm.measurable)
  have hbase : Continuous (fun t ↦ ‖F t * logarithmicDirichletPolynomial S b t‖ ^ 2) :=
    (hF.mul (continuous_logarithmicDirichletPolynomial S b)).norm.pow 2
  apply (intervalIntegral_indicator_le_sum_cover I hE (fun i _ ↦ hA i) hbase
    (fun _ ↦ sq_nonneg _) hT (by
      intro t htE ht
      obtain ⟨i, hi, hlarge⟩ := hcover t htE ht
      exact ⟨i, hi, htE, hlarge⟩)).trans
  apply Finset.sum_le_sum
  intro i hi
  apply crossBlockEnergy_le_dyadic_moment (hP i hi) hS (ha i hi) hb
    (hY i hi) (hPY i hi) hX (hN i hi) (hD i hi) hF (hA i) hT hW (hV i hi)
  · intro t htA ht
    exact hsmall t htA.1 ht
  · intro t htA _
    exact htA.2

end Erdos67b
