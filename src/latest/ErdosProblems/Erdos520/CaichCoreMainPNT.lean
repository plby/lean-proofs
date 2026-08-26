import ErdosProblems.Erdos520.CaichCoreMainCleanup
import ErdosProblems.Erdos520.CaichLambda23Cutoffs

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos
namespace Problem520

/-!
# Floor-safe prime input for the core averaged main term

The real short-window mass from `CaichCoreMainCleanup` is a sub-sum of the
natural floor interval treated in `CaichLambda23Cutoffs`.  Consequently the
effective-PNT theorem there supplies the exact hypothesis of the core-energy
comparison, with only the explicit logarithmic ratio shown below.
-/

/-- Restricting the natural floor interval to one prime block can only
decrease its reciprocal mass. -/
theorem caichShortWindowReciprocalMass_le_cutoffReciprocalSum
    {X x a b : ℕ} {z : ℝ} (hX : 1 ≤ X) (hz : 0 < z) :
    caichShortWindowReciprocalMass (X : ℝ) x a b z ≤
      freshReciprocalSum (caichLambdaLowerCutoff x X z)
        (caichLambdaUpperCutoff x z) := by
  classical
  have hXR : (0 : ℝ) < (X : ℝ) := by positivity
  have hfactor : 0 < 1 + 1 / (X : ℝ) := by positivity
  have hlowerNonneg :
      0 ≤ (x : ℝ) / (z * (1 + 1 / (X : ℝ))) := by positivity
  unfold caichShortWindowReciprocalMass freshReciprocalSum
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rw [Finset.mem_filter] at hp
    have hpBlock := mem_freshPrimes.mp hp.1
    have hpWindow := hp.2
    apply mem_freshPrimes.mpr
    refine ⟨hpBlock.1, ?_, ?_⟩
    · have hfloor :
          (caichLambdaLowerCutoff x X z : ℝ) ≤
            (x : ℝ) / (z * (1 + 1 / (X : ℝ))) := by
        unfold caichLambdaLowerCutoff
        exact Nat.floor_le hlowerNonneg
      exact_mod_cast hfloor.trans_lt hpWindow.1
    · unfold caichLambdaUpperCutoff
      exact Nat.le_floor hpWindow.2
  · intro p hp hnot
    positivity

/-- The floor-safe reciprocal estimate gives the core block bound.  The
coefficient retains the exact ratio `log b / log y`; a thin-block geometry
lemma can subsequently replace it by a uniform constant. -/
theorem caichCoreAveragedBlockMain_le_of_cutoffReciprocal
    {X x y a b : ℕ}
    (hX : 1 ≤ X) (hx : 0 < x) (hy : 2 ≤ y)
    (ha : 1 ≤ a) (hab : a ≤ b) (hb : 2 ≤ b)
    (omega : Omega)
    (hcutoff : ∀ z ∈
      Ioc ((x : ℝ) / (b : ℝ)) ((x : ℝ) / (a : ℝ)),
      0 < z →
      freshReciprocalSum (caichLambdaLowerCutoff x X z)
          (caichLambdaUpperCutoff x z) ≤
        3 / ((X : ℝ) * Real.log (y : ℝ))) :
    caichCoreAveragedBlockMain (X : ℝ) omega x a b ≤
      (3 * Real.log (b : ℝ) / Real.log (y : ℝ)) *
        (x : ℝ) * realSmoothBlockEnergy a b omega := by
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogB : 0 < Real.log (b : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < b by omega))
  let C : ℝ := 3 * Real.log (b : ℝ) / Real.log (y : ℝ)
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  apply caichCoreAveragedBlockMain_le_realSmoothBlockEnergy
    (by positivity) hx ha hab hb hC omega
  intro z hz
  have hzpos : 0 < z := by
    have hxb : (0 : ℝ) ≤ (x : ℝ) / (b : ℝ) := by positivity
    exact hxb.trans_lt hz.1
  have hmass := caichShortWindowReciprocalMass_le_cutoffReciprocalSum
    (X := X) (x := x) (a := a) (b := b) hX hzpos
  have hprime := hcutoff z hz hzpos
  calc
    caichShortWindowReciprocalMass (X : ℝ) x a b z ≤
        freshReciprocalSum (caichLambdaLowerCutoff x X z)
          (caichLambdaUpperCutoff x z) := hmass
    _ ≤ 3 / ((X : ℝ) * Real.log (y : ℝ)) := hprime
    _ = C / ((X : ℝ) * Real.log (b : ℝ)) := by
      dsimp only [C]
      field_simp
      <;> ring

/-- Effective PNT supplies the reciprocal-window estimate uniformly in all
parameters in the polylogarithmic Caich regime. -/
theorem eventually_caichShortWindowReciprocalMass_le_of_effectiveStatement
    (hPNT : EffectivePrimeCountingStatement) (A : ℕ) :
    ∀ᶠ y : ℕ in atTop, ∀ {x X a b : ℕ} {z : ℝ},
      0 < z → 2 ≤ X →
      y ≤ caichLambdaLowerCutoff x X z →
      (X : ℝ) ≤ Real.log (y : ℝ) ^ A →
      2 * X ≤ caichLambdaLowerCutoff x X z →
      caichShortWindowReciprocalMass (X : ℝ) x a b z ≤
        3 / ((X : ℝ) * Real.log (y : ℝ)) := by
  have hcutoff :=
    eventually_caichLambdaCutoff_reciprocal_le_of_effectiveStatement hPNT A
  filter_upwards [hcutoff] with y hy x X a b z hz hX hylower hXpoly hlarge
  exact (caichShortWindowReciprocalMass_le_cutoffReciprocalSum
    (by omega) hz).trans (hy hz hX hylower hXpoly hlarge)

end Problem520
end Erdos
