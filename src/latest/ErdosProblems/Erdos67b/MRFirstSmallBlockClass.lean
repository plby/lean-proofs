import ErdosProblems.Erdos67b.MRSmallBlockEnergy
import ErdosProblems.Erdos67b.MRSmallBlockParameters

/-!
# Energy of an entire first-small-block frequency class

All current subblocks and all large preceding subblocks are summed. The
class bound has the summable size `1 / (j² exp qprev)` under explicit
finite support and scalar separation conditions. Choosing the global
block schedule and estimating the no-small-block class remain separate.
-/

open scoped BigOperators Interval
open Finset MeasureTheory

namespace Erdos67b

theorem weighted_double_sum_le_of_card_budget
    {ι κ : Type*} (I : Finset ι) (J : Finset κ) (f : ι → κ → ℝ)
    {weight scale bound : ℝ} (hw : 0 ≤ weight) (hs : 0 < scale) (hb : 0 ≤ bound)
    (hcard : weight * I.card * J.card ≤ 4 * scale)
    (hpoint : ∀ i ∈ I, ∀ j ∈ J, scale * f i j ≤ bound) :
    weight * (∑ i ∈ I, ∑ j ∈ J, f i j) ≤ 4 * bound := by
  have hsum : (∑ i ∈ I, ∑ j ∈ J, f i j) ≤
      (I.card : ℝ) * (J.card : ℝ) * (bound / scale) := by
    calc
      _ ≤ ∑ _i ∈ I, ∑ _j ∈ J, bound / scale := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        apply (le_div_iff₀ hs).mpr
        simpa only [mul_comm] using hpoint i hi j hj
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  calc
    _ ≤ weight * ((I.card : ℝ) * (J.card : ℝ) * (bound / scale)) :=
      mul_le_mul_of_nonneg_left hsum hw
    _ = (weight * I.card * J.card) * (bound / scale) := by ring
    _ ≤ (4 * scale) * (bound / scale) :=
      mul_le_mul_of_nonneg_right hcard (div_nonneg hb hs.le)
    _ = 4 * bound := by field_simp

/-- Finite current and preceding subblocks, before the scalar covering
cost is absorbed. The preceding frequency classes may overlap. -/
theorem firstSmallBlock_energy_le_double_sum
    {ι κ : Type*} (I : Finset ι) (J : Finset κ)
    (P : κ → Finset ℕ) (S : ι → Finset ℕ)
    (a : κ → ℕ → ℂ) (b : ι → ℕ → ℂ)
    (u : κ → ℝ) (v : ι → ℝ) (F : ι → ℝ → ℂ)
    (hP : ∀ r ∈ J, ∀ p ∈ P r, p.Prime)
    (ha : ∀ r ∈ J, ∀ p ∈ P r, ‖a r p‖ ≤ (p : ℝ)⁻¹)
    (hb : ∀ s ∈ I, ∀ m ∈ S s, ‖b s m‖ ≤ (m : ℝ)⁻¹)
    (hu : ∀ r ∈ J, 1 ≤ u r) (huv : ∀ s ∈ I, ∀ r ∈ J, u r ≤ v s)
    {alpha beta delta : ℝ} (halpha : 0 ≤ alpha) (hdelta : 0 < delta)
    (hcost : ∀ s ∈ I, ∀ r ∈ J, 6 * Real.log (2 * v s) / u r ≤ delta)
    (hgap : delta ≤ beta - alpha)
    (hPlo : ∀ r ∈ J, ∀ p ∈ P r, Real.exp (u r) ≤ p)
    (hPhi : ∀ r ∈ J, ∀ p ∈ P r, (p : ℝ) ≤ 2 * Real.exp (u r))
    {X : ℕ} (hX : 0 < X)
    (hSlo : ∀ s ∈ I, ∀ m ∈ S s, (X : ℝ) / Real.exp (v s) ≤ m)
    (hShi : ∀ s ∈ I, ∀ m ∈ S s, (m : ℝ) ≤ 2 * X / Real.exp (v s))
    (hF : ∀ s ∈ I, Continuous (F s))
    {E : Set ℝ} (hE : MeasurableSet E) {T : ℝ} (hT : 0 ≤ T)
    (hsmall : ∀ s ∈ I, ∀ t ∈ E, t ∈ Set.Icc (-T) T → ‖F s t‖ ≤ Real.exp (-beta * v s))
    (hcover : ∀ t ∈ E, t ∈ Set.Icc (-T) T →
      ∃ r ∈ J, Real.exp (-alpha * u r) ≤ ‖logarithmicDirichletPolynomial (P r) (a r) t‖) :
    (∑ s ∈ I, ∫ t in -T..T, E.indicator
      (fun t ↦ ‖F s t * logarithmicDirichletPolynomial (S s) (b s) t‖ ^ 2) t) ≤
      (32 * Real.exp 12 * (1 + Real.pi) * (T / X + 1)) *
        ∑ s ∈ I, ∑ r ∈ J, Real.exp ((1 + 2 * alpha) * u r - delta * v s) := by
  classical
  let A : κ → Set ℝ := fun r ↦ E ∩
    {t | Real.exp (-alpha * u r) ≤ ‖logarithmicDirichletPolynomial (P r) (a r) t‖}
  have hA (r : κ) : MeasurableSet (A r) := hE.inter
    (measurableSet_le measurable_const
      (continuous_logarithmicDirichletPolynomial (P r) (a r)).norm.measurable)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  have hbase : Continuous
      (fun t ↦ ‖F s t * logarithmicDirichletPolynomial (S s) (b s) t‖ ^ 2) :=
    ((hF s hs).mul (continuous_logarithmicDirichletPolynomial (S s) (b s))).norm.pow 2
  apply (intervalIntegral_indicator_le_sum_cover J hE (fun r _ ↦ hA r) hbase
    (fun _ ↦ sq_nonneg _) hT (by
      intro t htE ht
      obtain ⟨r, hr, hlarge⟩ := hcover t htE ht
      exact ⟨r, hr, htE, hlarge⟩)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  apply crossBlockEnergy_source_decay (hP r hr) (ha r hr) (hb s hs)
    (hu r hr) (huv s hs r hr) halpha hdelta (hcost s hs r hr) hgap
    (hPlo r hr) (hPhi r hr) hX (hSlo s hs) (hShi s hs) (hF s hs) (hA r) hT
  · intro t htA ht
    exact hsmall s hs t htA.1 ht
  · intro t htA _
    exact htA.2

/-- Complete quantitative energy estimate for one first-small-block
frequency class. Its only remaining requirements are explicit supports,
thresholds, a finite cover, and scalar block-separation inequalities. -/
theorem firstSmallBlock_frequencyClass_energy_le
    {ι κ : Type*} (I : Finset ι) (J : Finset κ)
    (P : κ → Finset ℕ) (S : ι → Finset ℕ)
    (a : κ → ℕ → ℂ) (b : ι → ℕ → ℂ)
    (u : κ → ℝ) (v : ι → ℝ) (F : ι → ℝ → ℂ)
    (hP : ∀ r ∈ J, ∀ p ∈ P r, p.Prime)
    (ha : ∀ r ∈ J, ∀ p ∈ P r, ‖a r p‖ ≤ (p : ℝ)⁻¹)
    (hb : ∀ s ∈ I, ∀ m ∈ S s, ‖b s m‖ ≤ (m : ℝ)⁻¹)
    {H q j qprev p alpha beta delta : ℝ}
    (hH : 0 < H) (hq : 0 < q) (hj : 1 ≤ j) (hqprev : 2 ≤ qprev)
    (hblockgap : qprev + 1 ≤ p)
    (hu : ∀ r ∈ J, 1 ≤ u r ∧ u r ≤ qprev)
    (hv : ∀ s ∈ I, p - 1 ≤ v s)
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1 / 4)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hcost : ∀ s ∈ I, ∀ r ∈ J, 6 * Real.log (2 * v s) / u r ≤ delta)
    (hgap : delta ≤ beta - alpha)
    (hcard : H * q * I.card * J.card ≤ 4 * H ^ 3 * q ^ 3)
    (hresolution : H ^ 3 * q ^ 3 ≤ j ^ 6 * Real.exp qprev)
    (hsep : 4 * qprev + 8 * Real.log j ≤ delta * p)
    (hPlo : ∀ r ∈ J, ∀ p ∈ P r, Real.exp (u r) ≤ p)
    (hPhi : ∀ r ∈ J, ∀ p ∈ P r, (p : ℝ) ≤ 2 * Real.exp (u r))
    {X : ℕ} (hX : 0 < X)
    (hSlo : ∀ s ∈ I, ∀ m ∈ S s, (X : ℝ) / Real.exp (v s) ≤ m)
    (hShi : ∀ s ∈ I, ∀ m ∈ S s, (m : ℝ) ≤ 2 * X / Real.exp (v s))
    (hF : ∀ s ∈ I, Continuous (F s))
    {E : Set ℝ} (hE : MeasurableSet E) {T : ℝ} (hT : 0 ≤ T)
    (hsmall : ∀ s ∈ I, ∀ t ∈ E, t ∈ Set.Icc (-T) T → ‖F s t‖ ≤ Real.exp (-beta * v s))
    (hcover : ∀ t ∈ E, t ∈ Set.Icc (-T) T →
      ∃ r ∈ J, Real.exp (-alpha * u r) ≤ ‖logarithmicDirichletPolynomial (P r) (a r) t‖) :
    H * q * (∑ s ∈ I, ∫ t in -T..T, E.indicator
      (fun t ↦ ‖F s t * logarithmicDirichletPolynomial (S s) (b s) t‖ ^ 2) t) ≤
      128 * Real.exp 12 * (1 + Real.pi) * (T / X + 1) / (j ^ 2 * Real.exp qprev) := by
  have huv : ∀ s ∈ I, ∀ r ∈ J, u r ≤ v s := by
    intro s hs r hr
    have hur := (hu r hr).2
    have hvs := hv s hs
    linarith
  have hraw := firstSmallBlock_energy_le_double_sum I J P S a b u v F hP ha hb
    (fun r hr ↦ (hu r hr).1) huv halpha0 hdelta0 hcost hgap hPlo hPhi hX hSlo hShi hF hE hT hsmall hcover
  have hbudget : H * q *
      (∑ s ∈ I, ∑ r ∈ J, Real.exp ((1 + 2 * alpha) * u r - delta * v s)) ≤
        4 * (1 / (j ^ 2 * Real.exp qprev)) := by
    apply weighted_double_sum_le_of_card_budget I J _ (by positivity)
      (show 0 < H ^ 3 * q ^ 3 by positivity) (by positivity) ?_ ?_
    · simpa only [mul_assoc] using hcard
    · intro s hs r hr
      exact firstSmallBlock_scalar_budget hH.le hq.le hj hqprev
        (by linarith [(hu r hr).1]) (hu r hr).2 (hv s hs) halpha0 halpha1
        hdelta0.le hdelta1 hresolution hsep
  let C : ℝ := 32 * Real.exp 12 * (1 + Real.pi) * (T / X + 1)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  calc
    _ ≤ H * q * (C * ∑ s ∈ I, ∑ r ∈ J, Real.exp ((1 + 2 * alpha) * u r - delta * v s)) :=
      mul_le_mul_of_nonneg_left hraw (by positivity)
    _ = C * (H * q * ∑ s ∈ I, ∑ r ∈ J, Real.exp ((1 + 2 * alpha) * u r - delta * v s)) := by ring
    _ ≤ C * (4 * (1 / (j ^ 2 * Real.exp qprev))) := mul_le_mul_of_nonneg_left hbudget hC
    _ = _ := by dsimp only [C]; ring

/-- Finite covering estimate with width-eight cofactor intervals at the
shifted scale; it permits the actual Ramaré rectangle. -/
theorem firstSmallBlock_enlarged_energy_le_double_sum
    {ι κ : Type*} (I : Finset ι) (J : Finset κ)
    (P : κ → Finset ℕ) (S : ι → Finset ℕ)
    (a : κ → ℕ → ℂ) (b : ι → ℕ → ℂ)
    (u : κ → ℝ) (v : ι → ℝ) (F : ι → ℝ → ℂ)
    (hP : ∀ r ∈ J, ∀ p ∈ P r, p.Prime)
    (ha : ∀ r ∈ J, ∀ p ∈ P r, ‖a r p‖ ≤ (p : ℝ)⁻¹)
    (hb : ∀ s ∈ I, ∀ m ∈ S s, ‖b s m‖ ≤ (m : ℝ)⁻¹)
    (hu : ∀ r ∈ J, 1 ≤ u r) (huv : ∀ s ∈ I, ∀ r ∈ J, u r ≤ v s)
    {alpha beta delta : ℝ} (halpha : 0 ≤ alpha) (hbeta : beta ≤ 1 / 4) (hdelta : 0 < delta)
    (hcost : ∀ s ∈ I, ∀ r ∈ J, 6 * Real.log (2 * (v s + 1)) / u r ≤ delta)
    (hgap : delta ≤ beta - alpha)
    (hPlo : ∀ r ∈ J, ∀ p ∈ P r, Real.exp (u r) ≤ p)
    (hPhi : ∀ r ∈ J, ∀ p ∈ P r, (p : ℝ) ≤ 2 * Real.exp (u r))
    {X : ℕ} (hX : 0 < X)
    (hSlo : ∀ s ∈ I, ∀ m ∈ S s, (X : ℝ) / Real.exp (v s + 1) ≤ m)
    (hShi : ∀ s ∈ I, ∀ m ∈ S s, (m : ℝ) ≤ 8 * X / Real.exp (v s + 1))
    (hF : ∀ s ∈ I, Continuous (F s))
    {E : Set ℝ} (hE : MeasurableSet E) {T : ℝ} (hT : 0 ≤ T)
    (hsmall : ∀ s ∈ I, ∀ t ∈ E, t ∈ Set.Icc (-T) T → ‖F s t‖ ≤ Real.exp (-beta * v s))
    (hcover : ∀ t ∈ E, t ∈ Set.Icc (-T) T →
      ∃ r ∈ J, Real.exp (-alpha * u r) ≤ ‖logarithmicDirichletPolynomial (P r) (a r) t‖) :
    (∑ s ∈ I, ∫ t in -T..T, E.indicator
      (fun t ↦ ‖F s t * logarithmicDirichletPolynomial (S s) (b s) t‖ ^ 2) t) ≤
      (128 * Real.exp 13 * (1 + Real.pi) * (T / X + 1)) *
        ∑ s ∈ I, ∑ r ∈ J, Real.exp ((1 + 2 * alpha) * u r - delta * v s) := by
  classical
  let A : κ → Set ℝ := fun r ↦ E ∩
    {t | Real.exp (-alpha * u r) ≤ ‖logarithmicDirichletPolynomial (P r) (a r) t‖}
  have hA (r : κ) : MeasurableSet (A r) := hE.inter
    (measurableSet_le measurable_const
      (continuous_logarithmicDirichletPolynomial (P r) (a r)).norm.measurable)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  have hbase : Continuous
      (fun t ↦ ‖F s t * logarithmicDirichletPolynomial (S s) (b s) t‖ ^ 2) :=
    ((hF s hs).mul (continuous_logarithmicDirichletPolynomial (S s) (b s))).norm.pow 2
  apply (intervalIntegral_indicator_le_sum_cover J hE (fun r _ ↦ hA r) hbase
    (fun _ ↦ sq_nonneg _) hT (by
      intro t htE ht
      obtain ⟨r, hr, hlarge⟩ := hcover t htE ht
      exact ⟨r, hr, htE, hlarge⟩)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  apply crossBlockEnergy_enlarged_decay (hP r hr) (ha r hr) (hb s hs)
    (hu r hr) (huv s hs r hr) halpha hbeta hdelta (hcost s hs r hr) hgap
    (hPlo r hr) (hPhi r hr) hX (hSlo s hs) (hShi s hs) (hF s hs) (hA r) hT
  · intro t htA ht
    exact hsmall s hs t htA.1 ht
  · intro t htA _
    exact htA.2

/-- Enlarged-rectangle energy for an entire first-small frequency class.
The scalar absorption is unchanged; only the local constant increases. -/
theorem firstSmallBlock_enlarged_frequencyClass_energy_le
    {ι κ : Type*} (I : Finset ι) (J : Finset κ)
    (P : κ → Finset ℕ) (S : ι → Finset ℕ)
    (a : κ → ℕ → ℂ) (b : ι → ℕ → ℂ)
    (u : κ → ℝ) (v : ι → ℝ) (F : ι → ℝ → ℂ)
    (hP : ∀ r ∈ J, ∀ p ∈ P r, p.Prime)
    (ha : ∀ r ∈ J, ∀ p ∈ P r, ‖a r p‖ ≤ (p : ℝ)⁻¹)
    (hb : ∀ s ∈ I, ∀ m ∈ S s, ‖b s m‖ ≤ (m : ℝ)⁻¹)
    {H q j qprev p alpha beta delta : ℝ}
    (hH : 0 < H) (hq : 0 < q) (hj : 1 ≤ j) (hqprev : 2 ≤ qprev)
    (hblockgap : qprev + 1 ≤ p)
    (hu : ∀ r ∈ J, 1 ≤ u r ∧ u r ≤ qprev)
    (hv : ∀ s ∈ I, p - 1 ≤ v s)
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1 / 4) (hbeta : beta ≤ 1 / 4)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hcost : ∀ s ∈ I, ∀ r ∈ J, 6 * Real.log (2 * (v s + 1)) / u r ≤ delta)
    (hgap : delta ≤ beta - alpha)
    (hcard : H * q * I.card * J.card ≤ 4 * H ^ 3 * q ^ 3)
    (hresolution : H ^ 3 * q ^ 3 ≤ j ^ 6 * Real.exp qprev)
    (hsep : 4 * qprev + 8 * Real.log j ≤ delta * p)
    (hPlo : ∀ r ∈ J, ∀ p ∈ P r, Real.exp (u r) ≤ p)
    (hPhi : ∀ r ∈ J, ∀ p ∈ P r, (p : ℝ) ≤ 2 * Real.exp (u r))
    {X : ℕ} (hX : 0 < X)
    (hSlo : ∀ s ∈ I, ∀ m ∈ S s, (X : ℝ) / Real.exp (v s + 1) ≤ m)
    (hShi : ∀ s ∈ I, ∀ m ∈ S s, (m : ℝ) ≤ 8 * X / Real.exp (v s + 1))
    (hF : ∀ s ∈ I, Continuous (F s))
    {E : Set ℝ} (hE : MeasurableSet E) {T : ℝ} (hT : 0 ≤ T)
    (hsmall : ∀ s ∈ I, ∀ t ∈ E, t ∈ Set.Icc (-T) T → ‖F s t‖ ≤ Real.exp (-beta * v s))
    (hcover : ∀ t ∈ E, t ∈ Set.Icc (-T) T →
      ∃ r ∈ J, Real.exp (-alpha * u r) ≤ ‖logarithmicDirichletPolynomial (P r) (a r) t‖) :
    H * q * (∑ s ∈ I, ∫ t in -T..T, E.indicator
      (fun t ↦ ‖F s t * logarithmicDirichletPolynomial (S s) (b s) t‖ ^ 2) t) ≤
      512 * Real.exp 13 * (1 + Real.pi) * (T / X + 1) / (j ^ 2 * Real.exp qprev) := by
  have huv : ∀ s ∈ I, ∀ r ∈ J, u r ≤ v s := by
    intro s hs r hr
    have hur := (hu r hr).2
    have hvs := hv s hs
    linarith
  have hraw := firstSmallBlock_enlarged_energy_le_double_sum I J P S a b u v F hP ha hb
    (fun r hr ↦ (hu r hr).1) huv halpha0 hbeta hdelta0 hcost hgap hPlo hPhi hX hSlo hShi hF hE hT hsmall hcover
  have hbudget : H * q *
      (∑ s ∈ I, ∑ r ∈ J, Real.exp ((1 + 2 * alpha) * u r - delta * v s)) ≤
        4 * (1 / (j ^ 2 * Real.exp qprev)) := by
    apply weighted_double_sum_le_of_card_budget I J _ (by positivity)
      (show 0 < H ^ 3 * q ^ 3 by positivity) (by positivity) ?_ ?_
    · simpa only [mul_assoc] using hcard
    · intro s hs r hr
      exact firstSmallBlock_scalar_budget hH.le hq.le hj hqprev
        (by linarith [(hu r hr).1]) (hu r hr).2 (hv s hs) halpha0 halpha1
        hdelta0.le hdelta1 hresolution hsep
  let C : ℝ := 128 * Real.exp 13 * (1 + Real.pi) * (T / X + 1)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  calc
    _ ≤ H * q * (C * ∑ s ∈ I, ∑ r ∈ J, Real.exp ((1 + 2 * alpha) * u r - delta * v s)) :=
      mul_le_mul_of_nonneg_left hraw (by positivity)
    _ = C * (H * q * ∑ s ∈ I, ∑ r ∈ J, Real.exp ((1 + 2 * alpha) * u r - delta * v s)) := by ring
    _ ≤ C * (4 * (1 / (j ^ 2 * Real.exp qprev))) := mul_le_mul_of_nonneg_left hbudget hC
    _ = _ := by dsimp only [C]; ring

end Erdos67b
