/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos294.SharpMajor
import ErdosProblems.Erdos294.SharpMinor
import ErdosProblems.Erdos294.SharpTail

/-! # Prescribed local limit at constant width -/

open Filter Finset Real
open scoped BigOperators Topology

namespace Erdos294.SharpLocalLimit

open Erdos297 Erdos297.ActiveLcm Erdos297.FiniteHoeffding
open Erdos297.GoodFactorization Erdos297.LocalLimit Erdos297.MajorArc
open Erdos294.SharpMajor Erdos294.SharpMinor
open Erdos294.SharpParameters Erdos294.SharpSupply Erdos294.SharpTail

noncomputable section

attribute [local instance] Classical.propDecidable

theorem eventually_prescribed_exactReciprocalMass :
    ∀ᶠ N : ℕ in atTop, ∀ (p : ℕ → ℝ) (z : ℕ),
      (∀ n ∈ sharpGoodSet N, 1 / logLogScale N ≤ p n) →
      (∀ n ∈ sharpGoodSet N, p n ≤ 1 / 2) →
      (∑ n ∈ sharpGoodSet N, p n / n =
        (z : ℝ) / activeLcm (sharpGoodSet N)) →
      1 / (4 * (activeLcm (sharpGoodSet N) : ℝ)) ≤
        exactReciprocalMass (sharpGoodSet N) p
          (z / (activeLcm (sharpGoodSet N) : ℚ)) := by
  filter_upwards [eventually_one_le_sharpM_and_sharpM_le_N,
      eventually_tail_bound, SharpMajor.eventually_prescribed_majorArc_lower,
      SharpMinor.eventually_prescribed_minorArc_bound, eventually_pos_scales]
      with N hM htail hmajor hminor hscales
  intro p z hpLower hpUpper hmean
  let I := sharpGoodSet N
  let Q := activeLcm I
  let _ : NeZero Q := ⟨activeLcm_ne_zero I⟩
  have hI : I ⊆ goodDenominators N (sharpM N) (sharpS N) := by
    simp [I, sharpGoodSet]
  have hIcc : I ⊆ Icc (sharpM N) N :=
    hI.trans (goodDenominators_subset_Icc N (sharpM N) (sharpS N))
  have hIpos : ∀ n ∈ I, 0 < n := fun n hn ↦
    goodDenominator_pos hM.1 (hI hn)
  have hIdiv : ∀ n ∈ I, n ∣ Q := fun n hn ↦ by
    simpa [Q] using dvd_activeLcm_of_mem_of_pos hIpos hn
  have hLLpos : 0 < logLogScale N := zero_lt_one.trans hscales.2.2.1
  have hp0 : ∀ n ∈ I, 0 ≤ p n := by
    intro n hn
    exact (one_div_pos.mpr hLLpos).le.trans
      (hpLower n (by simpa [I] using hn))
  have hp1 : ∀ n ∈ I, p n ≤ 1 := by
    intro n hn
    exact (hpUpper n (by simpa [I] using hn)).trans (by norm_num)
  have hmean' : subsetMean I p (fun n : ℕ ↦ (n : ℝ)⁻¹) =
      (z : ℝ) / Q := by
    simpa [I, Q, subsetMean, div_eq_mul_inv] using hmean
  have htailFull := htail I p hIcc hp0 hp1
  have htailActive :
      offLatticeMass I (fun n ↦ Q / n) p z Q ≤ 1 / (4 * (Q : ℝ)) := by
    have hbridge := offLatticeMass_le_reciprocalEventMass_of_commonMultiple
      (activeLcm_pos I) I hIpos hIdiv p hp0 hp1 (z := z)
    have htoFull : offLatticeMass I (fun n ↦ Q / n) p z Q ≤
        1 / (4 * (smoothLcm (sharpS N) : ℝ)) := by
      refine hbridge.trans ?_
      simpa [hmean', Q] using htailFull
    refine htoFull.trans ?_
    apply one_div_le_one_div_of_le
    · exact mul_pos (by norm_num) (by exact_mod_cast activeLcm_pos I)
    · exact mul_le_mul_of_nonneg_left
        (by exact_mod_cast activeLcm_le_smoothLcm hM.1 hI) (by norm_num)
  have hmajor' : (3 / 4 : ℝ) ≤ 1 +
      (MajorArc.fourierBlock (majorFrequencies Q (sharpM N)) I
        (fun n ↦ (Q / n : ZMod Q)) p (z : ZMod Q)).re := by
    simpa [SharpMajor.prescribedMajorBlock, I, Q] using
      hmajor p z hpLower hpUpper hmean
  have hminor' :
      ‖MajorArc.fourierBlock (minorFrequencies Q (sharpM N)) I
        (fun n ↦ (Q / n : ZMod Q)) p (z : ZMod Q)‖ ≤ 1 / 4 := by
    simpa [SharpMinor.prescribedMinorBlock, I, Q] using
      hminor p z hpLower hpUpper
  have hresult := liuSawhney_proposition_3_2 (activeLcm_pos I)
    (majorFrequencies Q (sharpM N)) (minorFrequencies Q (sharpM N))
    I hIpos hIdiv p hp0 hp1 (disjoint_major_minor Q (sharpM N))
    (major_union_minor Q (sharpM N))
    (by simpa [LocalLimit.fourierBlock, MajorArc.fourierBlock] using hmajor')
    (by simpa [LocalLimit.fourierBlock, MajorArc.fourierBlock] using hminor')
    htailActive
  simpa [I, Q] using hresult

end

end Erdos294.SharpLocalLimit

#print axioms Erdos294.SharpLocalLimit.eventually_prescribed_exactReciprocalMass
