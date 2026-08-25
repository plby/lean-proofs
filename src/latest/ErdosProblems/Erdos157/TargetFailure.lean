import ErdosProblems.Erdos157.PrimeTripleRealization
import ErdosProblems.Erdos157.IndependentAssignments
import ErdosProblems.Erdos157.CoverageMass

/-! A failure bound for one target integer, using disjoint prime triples. -/

namespace Erdos157.Elementary

open Polynomial PolynomialCharacters AuxiliaryModuli FiniteFiberCounts

variable (K : Type*) [Field K] [DecidableEq K] [Fintype K] [CharP K 2]

abbrev LevelParameters (k : ℕ) := LevelLabel K k → LocalChoice K k

noncomputable def LocallyRepresented (τ : MaskChoice K) (k : ℕ) (ω : LevelParameters K k) (m : ℕ) : Prop :=
  ∃ f₁ f₂ f₃ : LevelLabel K k,
    localValue K τ k f₁ (ω f₁) + localValue K τ k f₂ (ω f₂) + localValue K τ k f₃ (ω f₃) = m

theorem fiberEntries_injective (k : ℕ) (hk : 4 ≤ k) (v : (AdjoinRoot (product K k))ˣ)
    {n : ℕ} (e : Fin n ≃ {T : PrimeTriple K (levelDegree k) // levelTripleResidue k k T = v}) :
    Function.Injective (Function.uncurry (fun j s => primeTripleEntry K (e j).1 s)) := by
  rintro ⟨j, s⟩ ⟨l, t⟩ heq
  change primeTripleEntry K (e j).1 s = primeTripleEntry K (e l).1 t at heq
  by_cases hj : j = l
  · subst l
    have hs := primeTripleEntry_injective K (e j).1 heq
    exact Prod.ext rfl hs
  · have hne : (e j).1 ≠ (e l).1 := by
      intro h
      exact hj (e.injective (Subtype.ext h))
    have hd := levelTripleResidue_fiber_pairwise_disjoint k hk v (e j).2 (e l).2 hne
    exact (Finset.disjoint_left.mp hd (primeTripleEntry_mem K (e j).1 s)
      (heq.symm ▸ primeTripleEntry_mem K (e l).1 t)).elim

theorem target_failure_density (τ : MaskChoice K) (k : ℕ) (hk : 4 ≤ k)
    (d : ∀ i : Fin k, BlockTarget K i)
    (hhit : MaskTargetHit K (fun i => τ i) (targetMoments K d))
    (z : ℕ) (hzlo : 3 ≤ z) (hzhi : z ≤ 3 * Fintype.card K ^ (3 * k)) :
    finiteDensity (fun ω : LevelParameters K k =>
      ¬ LocallyRepresented K τ k ω (levelTargetValue K d + blockPlace K 0 k * z)) ≤
        Real.exp (-fiberThreshold (K := K) k / (Fintype.card (LocalChoice K k) : ℝ) ^ 3) := by
  classical
  obtain ⟨t, hmom, hgood⟩ := hhit
  let v := (unitLogEquiv K k).symm
    (fun i => (targetMoments K d).logarithm i - Masks.maskSum (t i) (τ i))
  let I := {T : PrimeTriple K (levelDegree k) // levelTripleResidue k k T = v}
  letI : Fintype I := Fintype.ofFinite _
  let n := Fintype.card I
  let e : Fin n ≃ I := (Fintype.equivFin I).symm
  let f := fun j s => primeTripleEntry K (e j).1 s
  have hf : Function.Injective (Function.uncurry f) := fiberEntries_injective K k hk v e
  choose c hc using (fun j : Fin n => realize_primeTriple K τ k d t hmom (e j).1 (e j).2 z hzlo hzhi)
  have hmono : finiteDensity (fun ω : LevelParameters K k =>
      ¬ LocallyRepresented K τ k ω (levelTargetValue K d + blockPlace K 0 k * z)) ≤
      finiteDensity (fun ω : LevelParameters K k => ∀ j, ¬ ∀ s, ω (f j s) = c j s) := by
    apply finiteDensity_mono
    intro ω hω j hj
    apply hω
    refine ⟨f j 0, f j 1, f j 2, ?_⟩
    rw [hj 0, hj 1, hj 2]
    exact hc j
  have hsupply : fiberThreshold (K := K) k ≤ (n : ℝ) := by
    change fiberThreshold (K := K) k ≤ (Nat.card I : ℝ) at hgood
    simpa only [Nat.card_eq_fintype_card] using hgood
  have hmass : fiberThreshold (K := K) k / (Fintype.card (LocalChoice K k) : ℝ) ^ 3 ≤
      (n : ℝ) / (Fintype.card (LocalChoice K k) : ℝ) ^ 3 :=
    div_le_div_of_nonneg_right hsupply (by positivity)
  calc
    _ ≤ _ := hmono
    _ ≤ Real.exp (-(n : ℝ) / (Fintype.card (LocalChoice K k) : ℝ) ^ 3) := by
      simpa only [Fintype.card_fin] using finiteDensity_disjoint_assignments f hf c
    _ ≤ _ := Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg hmass)

theorem target_failure_coefficientField (τ : MaskChoice CoefficientField) (k : ℕ) (hk : 400 ≤ k)
    (d : ∀ i : Fin k, BlockTarget CoefficientField i)
    (hhit : MaskTargetHit CoefficientField (fun i => τ i) (targetMoments CoefficientField d))
    (z : ℕ) (hzlo : 3 ≤ z) (hzhi : z ≤ 3 * Fintype.card CoefficientField ^ (3 * k)) :
    finiteDensity (fun ω : LevelParameters CoefficientField k =>
      ¬ LocallyRepresented CoefficientField τ k ω
        (levelTargetValue CoefficientField d + blockPlace CoefficientField 0 k * z)) ≤
        Real.exp (-(2 : ℝ) ^ (k ^ 2)) := by
  calc
    _ ≤ _ := target_failure_density CoefficientField τ k (by omega) d hhit z hzlo hzhi
    _ ≤ _ := Real.exp_le_exp.mpr (by
      simpa only [neg_div] using neg_le_neg (coverage_trial_mass k hk))

end Erdos157.Elementary
