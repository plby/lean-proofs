/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1166.Erdos1166HLOZLemma410Race
import ErdosProblems.Erdos1166.Erdos1166PotentialKernelAnalytic

namespace Erdos1166

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace HLOZLemma410PotentialRace

open KilledGreen HLOZLemma410Race

def puncturedDisk (N : ℕ) (z : Site) : Set Site :=
  (squareDisk N : Set Site) ∩ ({z}ᶜ : Set Site)

theorem firstHitBeforePositiveReturnAt_translate_to_zero
    (x y : Site) (n : ℕ) :
    firstHitBeforePositiveReturnAt x y n =
      firstHitBeforePositiveReturnAt 0 (y - x) n := by
  ext ω
  constructor
  · rintro ⟨hend, hfirstY, havoidX⟩
    refine ⟨?_, ?_, ?_⟩
    · have h := congrArg (fun w : Site ↦ w - x) hend
      simpa [walkFrom] using h
    · intro r hr hry
      apply hfirstY r hr
      have h := congrArg (fun w : Site ↦ x + w) hry
      simpa [walkFrom] using h
    · intro r hr hrn hrzero
      apply havoidX r hr hrn
      have h := congrArg (fun w : Site ↦ x + w) hrzero
      simpa [walkFrom] using h
  · rintro ⟨hend, hfirstY, havoidX⟩
    refine ⟨?_, ?_, ?_⟩
    · have h := congrArg (fun w : Site ↦ x + w) hend
      simpa [walkFrom] using h
    · intro r hr hry
      apply hfirstY r hr
      have h := congrArg (fun w : Site ↦ w - x) hry
      simpa [walkFrom] using h
    · intro r hr hrn hrx
      apply havoidX r hr hrn
      have h := congrArg (fun w : Site ↦ w - x) hrx
      simpa [walkFrom] using h

theorem hitBeforePositiveReturnEvent_translate_to_zero (x y : Site) :
    hitBeforePositiveReturnEvent x y =
      hitBeforePositiveReturnEvent 0 (y - x) := by
  unfold hitBeforePositiveReturnEvent
  congr 1
  funext n
  exact firstHitBeforePositiveReturnAt_translate_to_zero x y n

theorem zero_mem_puncturedDisk {N : ℕ} {z : Site} (hz : z ≠ 0) :
    (0 : Site) ∈ puncturedDisk N z := by
  constructor
  · apply Finset.mem_product.mpr
    constructor <;> simp
  · simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hz.symm

theorem puncturedDisk_subset_squareDisk (N : ℕ) (z : Site) :
    puncturedDisk N z ⊆ (squareDisk N : Set Site) :=
  Set.inter_subset_left

theorem puncturedGreen_ne_top (N : ℕ) (z : Site) :
    killedGreen (puncturedDisk N z) 0 0 ≠ ∞ := by
  exact ne_of_lt ((killedGreen_mono (puncturedDisk_subset_squareDisk N z) 0 0).trans_lt
    (diskGreen_lt_top N 0 0))

theorem escapeBeforeReturn_punctured_subset
    {N : ℕ} {z : Site} (hz : z ≠ 0) :
    escapeBeforeReturnEvent (puncturedDisk N z) 0 ⊆
      hitBeforePositiveReturnEvent 0 z ∪
        exitBeforeReturnEvent (squareDisk N : Set Site) 0 ∪
          neverExitEvent (squareDisk N : Set Site) 0 := by
  intro ω hescape
  by_cases hhit : ω ∈ hitBeforePositiveReturnEvent 0 z
  · exact Or.inl (Or.inl hhit)
  by_cases hnever : ω ∈ neverExitEvent (squareDisk N : Set Site) 0
  · exact Or.inr hnever
  apply Or.inl
  apply Or.inr
  refine ⟨?_, ?_⟩
  · intro hreturn
    rcases Set.mem_iUnion.mp hreturn with ⟨j, hj⟩
    let K : ℕ := j + 1
    have hKpos : 0 < K := by simp [K]
    have hstaySquare : ∀ r, r ≤ K → walkFrom 0 ω r ∈ squareDisk N := by
      simpa [K] using hj.1
    have hend : walkFrom 0 ω K = 0 := by simpa [K] using hj.2.1
    have hfirstZero : ∀ r, 0 < r → r < K → walkFrom 0 ω r ≠ 0 := by
      simpa [K] using hj.2.2.2
    by_cases havoidZ : ∀ r, r ≤ K → walkFrom 0 ω r ≠ z
    · apply hescape
      apply Set.mem_iUnion.mpr
      refine ⟨j, ?_⟩
      refine ⟨?_, hj.2.1, hj.2.2.1, hj.2.2.2⟩
      intro r hr
      exact ⟨hj.1 r hr, by
        simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using havoidZ r hr⟩
    · push Not at havoidZ
      rcases havoidZ with ⟨r, hrK, hrz⟩
      let P : ℕ → Prop := fun u ↦ u ≤ K ∧ walkFrom 0 ω u = z
      have hP : ∃ u, P u := ⟨r, hrK, hrz⟩
      let u : ℕ := Nat.find hP
      have huP : P u := Nat.find_spec hP
      have huPos : 0 < u := by
        by_contra hu0
        have : u = 0 := Nat.eq_zero_of_not_pos hu0
        apply hz
        rw [← huP.2, this]
        simp [walkFrom, simpleRandomWalk]
      have huLtK : u < K := by
        apply lt_of_le_of_ne huP.1
        intro huK
        apply hz
        rw [← huP.2, huK, hend]
      apply hhit
      apply Set.mem_iUnion.mpr
      refine ⟨u, huP.2, ?_, ?_⟩
      · intro v hv hvz
        exact (Nat.find_min hP hv) ⟨hv.le.trans huP.1, hvz⟩
      · intro v hvpos hvu hvzero
        exact hfirstZero v hvpos (hvu.trans_lt huLtK) hvzero
  · simpa [neverExitEvent] using hnever

theorem measure_escape_punctured_le_hit_add_exit
    {N : ℕ} {z : Site} (hz : z ≠ 0) :
    incrementLaw (escapeBeforeReturnEvent (puncturedDisk N z) 0) ≤
      incrementLaw (hitBeforePositiveReturnEvent 0 z) +
        incrementLaw (exitBeforeReturnEvent (squareDisk N : Set Site) 0) := by
  calc
    incrementLaw (escapeBeforeReturnEvent (puncturedDisk N z) 0) ≤
        incrementLaw
          (hitBeforePositiveReturnEvent 0 z ∪
            exitBeforeReturnEvent (squareDisk N : Set Site) 0 ∪
              neverExitEvent (squareDisk N : Set Site) 0) :=
      measure_mono (escapeBeforeReturn_punctured_subset hz)
    _ ≤ incrementLaw (hitBeforePositiveReturnEvent 0 z) +
        incrementLaw (exitBeforeReturnEvent (squareDisk N : Set Site) 0) +
          incrementLaw (neverExitEvent (squareDisk N : Set Site) 0) := by
      exact (measure_union_le _ _).trans
        (add_le_add (measure_union_le _ _) le_rfl)
    _ = incrementLaw (hitBeforePositiveReturnEvent 0 z) +
        incrementLaw (exitBeforeReturnEvent (squareDisk N : Set Site) 0) := by
      rw [measure_neverExitEvent_squareDisk_eq_zero]
      simp

theorem measure_escape_punctured_eq_inv_green
    {N : ℕ} {z : Site} (hz : z ≠ 0) :
    incrementLaw (escapeBeforeReturnEvent (puncturedDisk N z) 0) =
      (killedGreen (puncturedDisk N z) 0 0)⁻¹ := by
  rw [← escapeWeight_eq_measure_escapeBeforeReturn]
  exact escapeWeight_eq_inv_killedGreen
    (zero_mem_puncturedDisk hz) (puncturedGreen_ne_top N z)

/-- Correct-direction Green reduction.  An *upper* bound on the punctured
diagonal Green function gives a lower bound on escape from the punctured
domain; subtracting the separately controlled square-exit event leaves the
desired hit-before-positive-return probability. -/
theorem hitBeforePositiveReturn_zero_real_lower_of_puncturedGreen_le
    {N : ℕ} {z : Site} (hz : z ≠ 0) {A : ℝ}
    (hG : (killedGreen (puncturedDisk N z) 0 0).toReal ≤ A) :
    1 / A - incrementLaw.real
        (exitBeforeReturnEvent (squareDisk N : Set Site) 0) ≤
      incrementLaw.real (hitBeforePositiveReturnEvent 0 z) := by
  let G := killedGreen (puncturedDisk N z) 0 0
  have hGfinite : G ≠ ∞ := puncturedGreen_ne_top N z
  have hGzero : G ≠ 0 := killedGreen_diagonal_ne_zero
    (zero_mem_puncturedDisk hz)
  have hGpos : 0 < G.toReal := ENNReal.toReal_pos hGzero hGfinite
  have hinv : 1 / A ≤ G.toReal⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hGpos hG
  have hmeasure := measure_escape_punctured_le_hit_add_exit
    (N := N) hz
  have hreal :
      incrementLaw.real (escapeBeforeReturnEvent (puncturedDisk N z) 0) ≤
        incrementLaw.real (hitBeforePositiveReturnEvent 0 z) +
          incrementLaw.real
            (exitBeforeReturnEvent (squareDisk N : Set Site) 0) := by
    rw [measureReal_def, measureReal_def, measureReal_def]
    rw [← ENNReal.toReal_add (measure_ne_top incrementLaw _)
      (measure_ne_top incrementLaw _)]
    exact (ENNReal.toReal_le_toReal (measure_ne_top incrementLaw _)
      (ENNReal.add_ne_top.mpr ⟨measure_ne_top incrementLaw _,
        measure_ne_top incrementLaw _⟩)).mpr hmeasure
  have hescape :
      incrementLaw.real (escapeBeforeReturnEvent (puncturedDisk N z) 0) =
        G.toReal⁻¹ := by
    rw [measureReal_def, measure_escape_punctured_eq_inv_green hz,
      ENNReal.toReal_inv]
  rw [hescape] at hreal
  linarith

/-- Source-shaped spatial input.  The large outer square is only a finite
approximation to the plane; the asserted upper bound is uniform in that
outer scale and depends logarithmically on the target separation `R`. -/
def HasPuncturedGreenFourLogUpperBound : Prop :=
  ∀ R : ℕ, 2 ≤ R → ∀ z : Site, z ≠ 0 →
    siteSquaredDistance 0 z ≤ R ^ 2 →
      (killedGreen (puncturedDisk (R ^ 64) z) 0 0).toReal ≤
        4 * Real.log R

/-- An optional zero-additive potential-kernel package sufficient for the
sharper `4 log R` Green bound.  This package is deliberately kept separate
from the source-correct affine-logarithmic API below: the bound
`a(z) ≤ 2 log R` is not valid at every small radius. -/
def HasSourcePotentialKernelBounds (a : Site → ℝ) : Prop :=
  KilledGreen.IsPlanarPotentialKernel a ∧ a 0 = 0 ∧
  (∀ N : ℕ, ∀ z : Site, z ≠ 0 →
    (killedGreen (puncturedDisk N z) 0 0).toReal ≤ a z + a (-z)) ∧
  (∀ R : ℕ, 2 ≤ R → ∀ z : Site,
    siteSquaredDistance 0 z ≤ R ^ 2 → a z ≤ 2 * Real.log R) ∧
  (∀ z, a (-z) = a z)

theorem hasPuncturedGreenFourLogUpperBound_of_sourcePotentialKernel
    {a : Site → ℝ} (ha : HasSourcePotentialKernelBounds a) :
    HasPuncturedGreenFourLogUpperBound := by
  intro R hR z hz hdist
  calc
    (killedGreen (puncturedDisk (R ^ 64) z) 0 0).toReal ≤
        a z + a (-z) := ha.2.2.1 (R ^ 64) z hz
    _ = 2 * a z := by rw [ha.2.2.2.2 z]; ring
    _ ≤ 2 * (2 * Real.log R) := by
      exact mul_le_mul_of_nonneg_left (ha.2.2.2.1 R hR z hdist) (by norm_num)
    _ = 4 * Real.log R := by ring

/-- Source-correct punctured-Green estimate with the additive constant which
is unavoidable at small radii. -/
def HasPuncturedGreenAffineLogUpperBound (D : ℝ) : Prop :=
  ∀ R : ℕ, 2 ≤ R → ∀ z : Site, z ≠ 0 →
    siteSquaredDistance 0 z ≤ R ^ 2 →
      (killedGreen (puncturedDisk (R ^ 64) z) 0 0).toReal ≤
        4 * Real.log R + D

theorem hitBeforePositiveReturn_zero_real_lower_eighth_log
    (hGreen : HasPuncturedGreenFourLogUpperBound)
    {R : ℕ} (hR : 2 ≤ R) {z : Site} (hz : z ≠ 0)
    (hdist : siteSquaredDistance 0 z ≤ R ^ 2) :
    1 / (8 * Real.log R) ≤
      incrementLaw.real (hitBeforePositiveReturnEvent 0 z) := by
  have hlog : 0 < Real.log (R : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < R by omega))
  have hRpow : 2 ≤ R ^ 64 := by
    calc
      2 ≤ R := hR
      _ ≤ R ^ 64 := by
        exact Nat.le_pow (a := R) (b := 64) (by norm_num)
  have hexit := exitBeforeReturn_zero_real_le_eight_div_log hRpow
  have hlogPow : Real.log (((R ^ 64 : ℕ) : ℝ)) =
      64 * Real.log (R : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have hexit' : incrementLaw.real
      (exitBeforeReturnEvent (squareDisk (R ^ 64) : Set Site) 0) ≤
        1 / (8 * Real.log R) := by
    calc
      incrementLaw.real
          (exitBeforeReturnEvent (squareDisk (R ^ 64) : Set Site) 0) ≤
          8 / Real.log (((R ^ 64 : ℕ) : ℝ)) := hexit
      _ = 1 / (8 * Real.log R) := by
        rw [hlogPow]
        field_simp
        ring
  have hlower :=
    hitBeforePositiveReturn_zero_real_lower_of_puncturedGreen_le
      (N := R ^ 64) hz (hGreen R hR z hz hdist)
  have halg : 1 / (4 * Real.log R) - 1 / (8 * Real.log R) =
      1 / (8 * Real.log R) := by
    field_simp
    ring
  rw [← halg]
  exact sub_le_iff_le_add.mpr ((sub_le_iff_le_add.mp hlower).trans
    (add_le_add le_rfl hexit'))

/-- The affine-logarithmic version needed by the actual planar potential
kernel.  Once the radius is large enough that `D ≤ 2 log R`, the additive
constant costs only a change from `1/8` to the safe constant `1/24`. -/
theorem hitBeforePositiveReturn_zero_real_lower_twenty_fourth_log
    {D : ℝ} (hGreen : HasPuncturedGreenAffineLogUpperBound D)
    {R : ℕ} (hR : 2 ≤ R) (hD : D ≤ 2 * Real.log R)
    {z : Site} (hz : z ≠ 0)
    (hdist : siteSquaredDistance 0 z ≤ R ^ 2) :
    1 / (24 * Real.log R) ≤
      incrementLaw.real (hitBeforePositiveReturnEvent 0 z) := by
  have hlog : 0 < Real.log (R : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < R by omega))
  have hRpow : 2 ≤ R ^ 64 := by
    calc
      2 ≤ R := hR
      _ ≤ R ^ 64 := Nat.le_pow (a := R) (b := 64) (by norm_num)
  have hexit := exitBeforeReturn_zero_real_le_eight_div_log hRpow
  have hlogPow : Real.log (((R ^ 64 : ℕ) : ℝ)) =
      64 * Real.log (R : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have hexit' : incrementLaw.real
      (exitBeforeReturnEvent (squareDisk (R ^ 64) : Set Site) 0) ≤
        1 / (8 * Real.log R) := by
    calc
      incrementLaw.real
          (exitBeforeReturnEvent (squareDisk (R ^ 64) : Set Site) 0) ≤
          8 / Real.log (((R ^ 64 : ℕ) : ℝ)) := hexit
      _ = 1 / (8 * Real.log R) := by
        rw [hlogPow]
        field_simp
        ring
  let A : ℝ := 4 * Real.log R + D
  have hG := hGreen R hR z hz hdist
  have hApos : 0 < A := by
    have hGfinite : killedGreen (puncturedDisk (R ^ 64) z) 0 0 ≠ ∞ :=
      puncturedGreen_ne_top (R ^ 64) z
    have hGzero : killedGreen (puncturedDisk (R ^ 64) z) 0 0 ≠ 0 :=
      killedGreen_diagonal_ne_zero (zero_mem_puncturedDisk hz)
    have hpos : 0 <
        (killedGreen (puncturedDisk (R ^ 64) z) 0 0).toReal :=
      ENNReal.toReal_pos hGzero hGfinite
    exact hpos.trans_le hG
  have hAupper : A ≤ 6 * Real.log R := by
    dsimp only [A]
    linarith
  have hinv : 1 / (6 * Real.log R) ≤ 1 / A := by
    simpa only [one_div] using one_div_le_one_div_of_le hApos hAupper
  have hlower :=
    hitBeforePositiveReturn_zero_real_lower_of_puncturedGreen_le
      (N := R ^ 64) hz hG
  have halg : 1 / (6 * Real.log R) - 1 / (8 * Real.log R) =
      1 / (24 * Real.log R) := by
    field_simp
    ring
  rw [← halg]
  calc
    1 / (6 * Real.log R) - 1 / (8 * Real.log R) ≤
        1 / A - incrementLaw.real
          (exitBeforeReturnEvent (squareDisk (R ^ 64) : Set Site) 0) :=
      sub_le_sub hinv hexit'
    _ ≤ incrementLaw.real (hitBeforePositiveReturnEvent 0 z) := hlower

theorem siteSquaredDistance_zero_sub (x y : Site) :
    siteSquaredDistance 0 (y - x) = siteSquaredDistance x y := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  simp only [siteSquaredDistance, Prod.fst_zero, Prod.fst_sub,
    Prod.snd_zero, Prod.snd_sub]
  congr 2 <;> congr 1 <;> ring

theorem hasOffOriginHitBeforeReturnLowerBound_eighth_log
    (hGreen : HasPuncturedGreenFourLogUpperBound)
    {R : ℕ} (hR : 2 ≤ R) :
    HasOffOriginHitBeforeReturnLowerBound R
      (ENNReal.ofReal (1 / (8 * Real.log R))) := by
  intro x y hxy hdist
  let z : Site := y - x
  have hz : z ≠ 0 := sub_ne_zero.mpr hxy.symm
  have hdistz : siteSquaredDistance 0 z ≤ R ^ 2 := by
    simpa [z, siteSquaredDistance_zero_sub] using hdist
  rw [hitBeforePositiveReturnEvent_translate_to_zero x y]
  apply (ENNReal.ofReal_le_iff_le_toReal
    (measure_ne_top incrementLaw _)).mpr
  exact hitBeforePositiveReturn_zero_real_lower_eighth_log
    hGreen hR hz hdistz

theorem hasOffOriginHitBeforeReturnLowerBound_twenty_fourth_log
    {D : ℝ} (hGreen : HasPuncturedGreenAffineLogUpperBound D)
    {R : ℕ} (hR : 2 ≤ R) (hD : D ≤ 2 * Real.log R) :
    HasOffOriginHitBeforeReturnLowerBound R
      (ENNReal.ofReal (1 / (24 * Real.log R))) := by
  intro x y hxy hdist
  let z : Site := y - x
  have hz : z ≠ 0 := sub_ne_zero.mpr hxy.symm
  have hdistz : siteSquaredDistance 0 z ≤ R ^ 2 := by
    simpa [z, siteSquaredDistance_zero_sub] using hdist
  rw [hitBeforePositiveReturnEvent_translate_to_zero x y]
  apply (ENNReal.ofReal_le_iff_le_toReal
    (measure_ne_top incrementLaw _)).mpr
  exact hitBeforePositiveReturn_zero_real_lower_twenty_fourth_log
    hGreen hR hD hz hdistz

theorem hasHLOZLemma410PostHitRaceEstimate_eighth_log
    (hGreen : HasPuncturedGreenFourLogUpperBound)
    (window : Site → Finset Site) (m k qCandidate qRace R : ℕ)
    (hR : 2 ≤ R)
    (hwindow : ∀ c x, x ∈ window c → siteSquaredDistance x c ≤ R ^ 2) :
    HasHLOZLemma410PostHitRaceEstimate simpleRandomWalkLaw window
      m k qCandidate qRace
      (fun _ ↦ (1 - ENNReal.ofReal (1 / (8 * Real.log R))) ^ qRace) :=
  hasHLOZLemma410PostHitRaceEstimate_of_offOriginHitBeforeReturn
    window m k qCandidate qRace R _ hwindow
      (hasOffOriginHitBeforeReturnLowerBound_eighth_log hGreen hR)

theorem hasHLOZLemma410PostHitRaceEstimate_exp_eighth_log
    (hGreen : HasPuncturedGreenFourLogUpperBound)
    (window : Site → Finset Site) (m k qCandidate qRace R : ℕ)
    (hR : 2 ≤ R)
    (hwindow : ∀ c x, x ∈ window c → siteSquaredDistance x c ≤ R ^ 2) :
    HasHLOZLemma410PostHitRaceEstimate simpleRandomWalkLaw window
      m k qCandidate qRace
      (fun _ ↦ ENNReal.ofReal
        (Real.exp (-((qRace : ℝ) * (1 / (8 * Real.log R)))))) := by
  have hlog : 0 < Real.log (R : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < R by omega))
  have hlogMono : Real.log 2 ≤ Real.log (R : ℝ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast hR
  have hden : (1 : ℝ) ≤ 8 * Real.log R := by
    nlinarith [Real.log_two_gt_d9]
  have hε0 : 0 ≤ (1 : ℝ) / (8 * Real.log R) := by positivity
  have hε1 : (1 : ℝ) / (8 * Real.log R) ≤ 1 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hlog)).mpr
    simpa using hden
  exact hasHLOZLemma410PostHitRaceEstimate_exp_of_offOriginHitBeforeReturn
    window m k qCandidate qRace R (1 / (8 * Real.log R)) hε0 hε1
      hwindow (hasOffOriginHitBeforeReturnLowerBound_eighth_log hGreen hR)

theorem hasHLOZLemma410PostHitRaceEstimate_exp_twenty_fourth_log
    {D : ℝ} (hGreen : HasPuncturedGreenAffineLogUpperBound D)
    (window : Site → Finset Site) (m k qCandidate qRace R : ℕ)
    (hR : 2 ≤ R) (hD : D ≤ 2 * Real.log R)
    (hwindow : ∀ c x, x ∈ window c → siteSquaredDistance x c ≤ R ^ 2) :
    HasHLOZLemma410PostHitRaceEstimate simpleRandomWalkLaw window
      m k qCandidate qRace
      (fun _ ↦ ENNReal.ofReal
        (Real.exp (-((qRace : ℝ) * (1 / (24 * Real.log R)))))) := by
  have hlog : 0 < Real.log (R : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < R by omega))
  have hlogMono : Real.log 2 ≤ Real.log (R : ℝ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast hR
  have hden : (1 : ℝ) ≤ 24 * Real.log R := by
    nlinarith [Real.log_two_gt_d9]
  have hε0 : 0 ≤ (1 : ℝ) / (24 * Real.log R) := by positivity
  have hε1 : (1 : ℝ) / (24 * Real.log R) ≤ 1 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hlog)).mpr
    simpa using hden
  exact hasHLOZLemma410PostHitRaceEstimate_exp_of_offOriginHitBeforeReturn
    window m k qCandidate qRace R (1 / (24 * Real.log R)) hε0 hε1
      hwindow
      (hasOffOriginHitBeforeReturnLowerBound_twenty_fourth_log hGreen hR hD)

theorem killedGreen_toReal_eq_indicator_add_stepAverage
    {D : Set Site} {x y : Site} (hx : x ∈ D)
    (hfinite : ∀ w, killedGreen D w y ≠ ∞) :
    (killedGreen D x y).toReal =
      (if x = y then 1 else 0) +
        KilledGreen.stepAverage (fun w ↦ (killedGreen D w y).toReal) x := by
  have h := killedGreen_eq_indicator_add_step_sum D x y hx
  have hsum : (∑ d : Direction, killedGreen D (x + directionStep d) y) ≠ ∞ := by
    rw [ENNReal.sum_ne_top]
    intro d hd
    exact hfinite _
  have hmul : (4 : ℝ≥0∞)⁻¹ *
      ∑ d : Direction, killedGreen D (x + directionStep d) y ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) hsum
  have hindicator : (if x = y then (1 : ℝ≥0∞) else 0) ≠ ∞ := by
    split_ifs <;> simp
  have hreal := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add hindicator hmul, ENNReal.toReal_mul,
    ENNReal.toReal_sum (fun d hd ↦ hfinite _)] at hreal
  norm_num at hreal
  by_cases hxy : x = y <;>
    simp [hxy, KilledGreen.stepAverage] at hreal ⊢ <;> exact hreal

theorem finite_subset_square_maximum_principle
    {N : ℕ} {A : Finset Site} {u : Site → ℝ}
    (hAsub : ↑A ⊆ (squareDisk N : Set Site))
    (hharm : ∀ z ∈ A, u z = KilledGreen.stepAverage u z)
    (hout : ∀ z, z ∉ A → u z ≤ 0) :
    ∀ x ∈ A, u x ≤ 0 := by
  intro x hx
  by_contra hnot
  have hxpos : 0 < u x := lt_of_not_ge hnot
  obtain ⟨z, hz, hmax⟩ := Finset.exists_max_image A u ⟨x, hx⟩
  have hzpos : 0 < u z := hxpos.trans_le (hmax x hx)
  have hstep (w : Site) (hw : w ∈ A) (hweq : u w = u z) :
      w + (1, 0) ∈ A ∧ u (w + (1, 0)) = u w := by
    have hwpos : 0 < u w := by simpa [hweq] using hzpos
    have hneighbor (d : Direction) : u (w + directionStep d) ≤ u w := by
      by_cases hd : w + directionStep d ∈ A
      · simpa [hweq] using hmax _ hd
      · exact (hout _ hd).trans hwpos.le
    have h0 := hneighbor (0 : Direction)
    have h1 := hneighbor (1 : Direction)
    have h2 := hneighbor (2 : Direction)
    have h3 := hneighbor (3 : Direction)
    have havg := KilledGreen.stepAverage_eq_four_neighbors u w
    have hwH := hharm w hw
    rw [havg] at hwH
    have heq : u (w + (1, 0)) = u w := by
      simp [directionStep] at h0 h1 h2 h3
      nlinarith [hwH]
    refine ⟨?_, heq⟩
    by_contra heast
    exact (not_lt_of_ge (hout _ heast)) (by simpa [heq] using hwpos)
  have hprop : ∀ j : ℕ, j ≤ 2 * N + 1 →
      z + ((j : ℤ), 0) ∈ A ∧ u (z + ((j : ℤ), 0)) = u z := by
    intro j hj
    induction j with
    | zero =>
        have hz0 : z + (((0 : ℕ) : ℤ), 0) = z := by ext <;> simp
        rw [hz0]
        exact ⟨hz, rfl⟩
    | succ j ih =>
        have hj' : j ≤ 2 * N + 1 := by omega
        rcases ih hj' with ⟨hjmem, hjeq⟩
        have hs := hstep _ hjmem hjeq
        have hadd : z + ((((j + 1 : ℕ) : ℤ)), 0) =
            (z + ((j : ℤ), 0)) + (1, 0) := by
          ext
          · change z.1 + ((j + 1 : ℕ) : ℤ) = z.1 + (j : ℤ) + 1
            push_cast
            ring
          · simp
        rw [hadd]
        exact ⟨hs.1, hs.2.trans hjeq⟩
  have hzSquare : z ∈ squareDisk N := hAsub hz
  have hfarSquare : z + (((2 * N + 1 : ℕ) : ℤ), 0) ∈ squareDisk N :=
    hAsub (hprop (2 * N + 1) le_rfl).1
  rcases Finset.mem_product.mp hzSquare with ⟨hz₁, hz₂⟩
  rcases Finset.mem_Icc.mp hz₁ with ⟨hz₁l, hz₁u⟩
  rcases Finset.mem_product.mp hfarSquare with ⟨hf₁, hf₂⟩
  rcases Finset.mem_Icc.mp hf₁ with ⟨hf₁l, hf₁u⟩
  simp at hf₁u
  omega

theorem finite_subset_square_maximum_principle_le_constant
    {N : ℕ} {A : Finset Site} {u : Site → ℝ} {Q : ℝ}
    (hAsub : ↑A ⊆ (squareDisk N : Set Site))
    (hharm : ∀ z ∈ A, u z = KilledGreen.stepAverage u z)
    (hout : ∀ z, z ∉ A → u z ≤ Q) :
    ∀ x ∈ A, u x ≤ Q := by
  intro x hx
  have hshift := finite_subset_square_maximum_principle
    (A := A) (u := fun z ↦ u z - Q) hAsub
    (fun z hz ↦ by
      rw [KilledGreen.stepAverage_sub, KilledGreen.stepAverage_const,
        hharm z hz])
    (fun z hz ↦ by linarith [hout z hz]) x hx
  linarith

/-- The structural potential-kernel facts used to control the punctured
Green diagonal: the Poisson equation, normalization, symmetry, the standard
triangle inequality, and source-correct affine logarithmic growth. -/
def HasPotentialKernelMetricLogBounds
    (a : Site → ℝ) (C Q : ℝ) : Prop :=
  KilledGreen.IsPlanarPotentialKernel a ∧ a 0 = 0 ∧
  (∀ z, a (-z) = a z) ∧
  (∀ w z, a w ≤ a (w - z) + a z + Q) ∧
  (∀ R : ℕ, 2 ≤ R → ∀ z : Site,
    siteSquaredDistance 0 z ≤ R ^ 2 → a z ≤ 2 * Real.log R + C)

theorem puncturedGreen_toReal_le_two_mul_potential
    {a : Site → ℝ} (ha : KilledGreen.IsPlanarPotentialKernel a)
    (ha0 : a 0 = 0) (heven : ∀ z, a (-z) = a z)
    {Q : ℝ} (htriangle : ∀ w z, a w ≤ a (w - z) + a z + Q)
    (N : ℕ) {z : Site} (hz : z ≠ 0) :
    (killedGreen (puncturedDisk N z) 0 0).toReal ≤ 2 * a z + Q := by
  let A : Finset Site := (squareDisk N).filter fun w ↦ w ≠ z
  have hAeq : (A : Set Site) = puncturedDisk N z := by
    ext w
    simp [A, puncturedDisk]
  have hAsub : (A : Set Site) ⊆ (squareDisk N : Set Site) := by
    intro w hw
    exact (Finset.mem_filter.mp hw).1
  let g : Site → ℝ := fun w ↦ a (w - z) - a w + a z
  let u : Site → ℝ := fun w ↦
    (killedGreen (puncturedDisk N z) w 0).toReal - g w
  have hfinite : ∀ w, killedGreen (puncturedDisk N z) w 0 ≠ ∞ := by
    intro w
    exact ne_of_lt ((killedGreen_mono (puncturedDisk_subset_squareDisk N z)
      w 0).trans_lt (diskGreen_lt_top N w 0))
  have hgstep : ∀ w, w ∈ A →
      KilledGreen.stepAverage g w =
        g w - (if w = 0 then 1 else 0) := by
    intro w hw
    have hwz : w ≠ z := (Finset.mem_filter.mp hw).2
    have hwsub : w - z ≠ 0 := sub_ne_zero.mpr hwz
    have hshift : KilledGreen.stepAverage (fun v ↦ a (v - z)) w =
        KilledGreen.stepAverage a (w - z) := by
      unfold KilledGreen.stepAverage
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      exact congrArg a (by abel)
    change KilledGreen.stepAverage
        (fun v ↦ (a (v - z) - a v) + a z) w = _
    rw [KilledGreen.stepAverage_add, KilledGreen.stepAverage_sub,
      KilledGreen.stepAverage_const, hshift, ha (w - z), ha w]
    simp only [if_neg hwsub, add_zero]
    dsimp only [g]
    ring
  have huharm : ∀ w ∈ A, u w = KilledGreen.stepAverage u w := by
    intro w hw
    have hwD : w ∈ puncturedDisk N z := by simpa [← hAeq] using hw
    have hG := killedGreen_toReal_eq_indicator_add_stepAverage
      hwD hfinite
    have hg := hgstep w hw
    change (killedGreen (puncturedDisk N z) w 0).toReal - g w = _
    rw [KilledGreen.stepAverage_sub]
    linarith
  have huout : ∀ w, w ∉ A → u w ≤ Q := by
    intro w hw
    have hwD : w ∉ puncturedDisk N z := by
      intro hwD
      apply hw
      simpa [← hAeq] using hwD
    have hGzero : killedGreen (puncturedDisk N z) w 0 = 0 :=
      killedGreen_eq_zero_of_start_not_mem hwD
    change (killedGreen (puncturedDisk N z) w 0).toReal - g w ≤ Q
    rw [hGzero]
    change 0 - (a (w - z) - a w + a z) ≤ Q
    linarith [htriangle w z]
  have hzeroA : (0 : Site) ∈ A := by
    apply Finset.mem_filter.mpr
    exact ⟨by
      apply Finset.mem_product.mpr
      constructor <;> simp, hz.symm⟩
  have hu0 := finite_subset_square_maximum_principle_le_constant
    hAsub huharm huout 0 hzeroA
  change (killedGreen (puncturedDisk N z) 0 0).toReal -
      (a (0 - z) - a 0 + a z) ≤ Q at hu0
  rw [zero_sub, ha0, heven] at hu0
  linarith

theorem hasPuncturedGreenAffineLogUpperBound_of_metricLogBounds
    {a : Site → ℝ} {C Q : ℝ}
    (ha : HasPotentialKernelMetricLogBounds a C Q) :
    HasPuncturedGreenAffineLogUpperBound (2 * C + Q) := by
  intro R hR z hz hdist
  calc
    (killedGreen (puncturedDisk (R ^ 64) z) 0 0).toReal ≤ 2 * a z + Q :=
      puncturedGreen_toReal_le_two_mul_potential
        ha.1 ha.2.1 ha.2.2.1 ha.2.2.2.1 (R ^ 64) hz
    _ ≤ 2 * (2 * Real.log R + C) + Q := by
      simpa [add_comm] using add_le_add_right
        (mul_le_mul_of_nonneg_left (ha.2.2.2.2 R hR z hdist)
          (show (0 : ℝ) ≤ 2 by norm_num)) Q
    _ = 4 * Real.log R + (2 * C + Q) := by ring

theorem hasPotentialKernelMetricLogBounds_of_finitePotentialKernel_tendsto
    {a : Site → ℝ} {C Q : ℝ}
    (hlim : ∀ z, Filter.Tendsto
      (fun N ↦ KilledGreen.finitePotentialKernel N z)
      Filter.atTop (nhds (a z)))
    (heven : ∀ z, a (-z) = a z)
    (htriangle : ∀ w z, a w ≤ a (w - z) + a z + Q)
    (hlog : ∀ R : ℕ, 2 ≤ R → ∀ z : Site,
      siteSquaredDistance 0 z ≤ R ^ 2 → a z ≤ 2 * Real.log R + C) :
    HasPotentialKernelMetricLogBounds a C Q := by
  exact ⟨KilledGreen.isPlanarPotentialKernel_of_finitePotentialKernel_tendsto hlim,
    KilledGreen.finitePotentialKernel_limit_zero hlim, heven, htriangle, hlog⟩

theorem hasOffOriginHitBeforeReturnLowerBound_of_metricLogBounds
    {a : Site → ℝ} {C Q : ℝ}
    (ha : HasPotentialKernelMetricLogBounds a C Q)
    {R : ℕ} (hR : 2 ≤ R) (hCQ : 2 * C + Q ≤ 2 * Real.log R) :
    HasOffOriginHitBeforeReturnLowerBound R
      (ENNReal.ofReal (1 / (24 * Real.log R))) :=
  hasOffOriginHitBeforeReturnLowerBound_twenty_fourth_log
    (hasPuncturedGreenAffineLogUpperBound_of_metricLogBounds ha) hR hCQ

theorem hasHLOZLemma410PostHitRaceEstimate_exp_of_metricLogBounds
    {a : Site → ℝ} {C Q : ℝ}
    (ha : HasPotentialKernelMetricLogBounds a C Q)
    (window : Site → Finset Site) (m k qCandidate qRace R : ℕ)
    (hR : 2 ≤ R) (hCQ : 2 * C + Q ≤ 2 * Real.log R)
    (hwindow : ∀ c x, x ∈ window c → siteSquaredDistance x c ≤ R ^ 2) :
    HasHLOZLemma410PostHitRaceEstimate simpleRandomWalkLaw window
      m k qCandidate qRace
      (fun _ ↦ ENNReal.ofReal
        (Real.exp (-((qRace : ℝ) * (1 / (24 * Real.log R)))))) :=
  hasHLOZLemma410PostHitRaceEstimate_exp_twenty_fourth_log
    (hasPuncturedGreenAffineLogUpperBound_of_metricLogBounds ha)
    window m k qCandidate qRace R hR hCQ hwindow

private theorem siteNormInf_le_of_squaredDistance_zero_le
    {z : Site} {R : ℕ} (hdist : siteSquaredDistance 0 z ≤ R ^ 2) :
    HeatKernel.siteNormInf z ≤ R := by
  have coordinate_le (q : ℕ)
      (hq : q ^ 2 ≤ siteSquaredDistance 0 z) : q ≤ R := by
    by_contra h
    have hRq : R < q := Nat.lt_of_not_ge h
    have hsq : R ^ 2 < q ^ 2 := by nlinarith
    omega
  apply max_le
  · apply coordinate_le z.1.natAbs
    simp only [siteSquaredDistance, Prod.fst_zero, Prod.snd_zero,
      Int.natAbs_neg, zero_sub]
    omega
  · apply coordinate_le z.2.natAbs
    simp only [siteSquaredDistance, Prod.fst_zero, Prod.snd_zero,
      Int.natAbs_neg, zero_sub]
    omega

/-- The completely constructed planar potential kernel satisfies the
source-correct analytic package.  The constants come from the checked
global upper bound and quasi-triangle inequality in
`Erdos1166PotentialKernelAnalytic`. -/
theorem planarPotentialKernel_metricLogBounds :
    HasPotentialKernelMetricLogBounds
      PotentialConvergence.planarPotentialKernel 20 2500 := by
  refine ⟨PotentialConvergence.planarPotentialKernel_isPlanar,
    PotentialConvergence.planarPotentialKernel_zero,
    PotentialConvergence.planarPotentialKernel_neg,
    PotentialConvergence.planarPotentialKernel_quasiTriangle, ?_⟩
  intro R hR z hdist
  by_cases hz : z = 0
  · subst z
    rw [PotentialConvergence.planarPotentialKernel_zero]
    have hlog : 0 ≤ Real.log (R : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ R by omega)
    positivity
  · have hnorm0 : 0 < HeatKernel.siteNormInf z :=
      PotentialConvergence.siteNormInf_pos_of_ne_zero hz
    have hupper :=
      PotentialConvergence.planarPotentialKernel_log_upper z hnorm0
    have hnorm : HeatKernel.siteNormInf z ≤ R :=
      siteNormInf_le_of_squaredDistance_zero_le hdist
    have hlogMono :
        Real.log (HeatKernel.siteNormInf z : ℝ) ≤
          Real.log (R : ℝ) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast hnorm
    have hlog0 : 0 ≤ Real.log (R : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ R by omega)
    have hcoef : 2 / Real.pi ≤ 2 := by
      have hp : 1 ≤ Real.pi :=
        (by norm_num : (1 : ℝ) ≤ 3).trans Real.pi_gt_three.le
      have hdiv := (div_le_one Real.pi_pos).2 hp
      calc
        2 / Real.pi = 2 * (1 / Real.pi) := by ring
        _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left hdiv (by norm_num)
        _ = 2 := by ring
    have hc0 : 0 ≤ 2 / Real.pi := by positivity
    calc
      PotentialConvergence.planarPotentialKernel z ≤
          (2 / Real.pi) * Real.log (HeatKernel.siteNormInf z : ℝ) + 20 := hupper
      _ ≤ (2 / Real.pi) * Real.log (R : ℝ) + 20 := by
        gcongr
      _ ≤ 2 * Real.log (R : ℝ) + 20 := by
        gcongr

/-- Fully unconditional off-origin one-cycle input, valid beyond the explicit
radius at which the fixed analytic constants are absorbed. -/
theorem planar_offOriginHitBeforeReturnLowerBound
    {R : ℕ} (hR : 2 ≤ R) (hlarge : 2540 ≤ 2 * Real.log R) :
    HasOffOriginHitBeforeReturnLowerBound R
      (ENNReal.ofReal (1 / (24 * Real.log R))) := by
  exact hasOffOriginHitBeforeReturnLowerBound_of_metricLogBounds
    planarPotentialKernel_metricLogBounds hR (by norm_num at hlarge ⊢; exact hlarge)

/-- Fully unconditional post-hit race estimate at every sufficiently large
radius. -/
theorem planar_hlozLemma410PostHitRaceEstimate_exp
    (window : Site → Finset Site) (m k qCandidate qRace R : ℕ)
    (hR : 2 ≤ R) (hlarge : 2540 ≤ 2 * Real.log R)
    (hwindow : ∀ c x, x ∈ window c → siteSquaredDistance x c ≤ R ^ 2) :
    HasHLOZLemma410PostHitRaceEstimate simpleRandomWalkLaw window
      m k qCandidate qRace
      (fun _ ↦ ENNReal.ofReal
        (Real.exp (-((qRace : ℝ) * (1 / (24 * Real.log R)))))) := by
  exact hasHLOZLemma410PostHitRaceEstimate_exp_of_metricLogBounds
    planarPotentialKernel_metricLogBounds window m k qCandidate qRace R
      hR (by norm_num at hlarge ⊢; exact hlarge) hwindow

end HLOZLemma410PotentialRace
end Erdos1166
