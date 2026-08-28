import Wikipedia.NoExoticSixSphere.RelativeModTwoSmallSequence

/-!
# Original cochain representatives for the genuine connecting homomorphism

Concrete cocycles give the same native class as categorical cycles.
The original short exact cochain row supplies a lift and a lifted
coboundary, and its actual connecting map is their genuine class.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SingularCohomologyFree

namespace NoExoticSixSphere.CochainConnecting

variable (K : CochainComplex (ModuleCat.{0} ℤ) ℕ)

/-- The concrete cocycle constructor agrees with the original categorical cycle constructor. -/
theorem cyclesMk_eq (p : ℕ) (a : Cocycle K p) :
    K.cyclesMk a.val (p + 1) (next_nat p) (cocycle_condition K p a) =
      ((K.sc p).moduleCatCyclesIso.inv).hom a := by
  apply (ModuleCat.mono_iff_injective (K.iCycles p)).mp inferInstance
  have h₁ := K.i_cyclesMk a.val (p + 1) (next_nat p) (cocycle_condition K p a)
  have h₂ := congrArg (fun m => m.hom a) ((K.sc p).moduleCatCyclesIso_inv_iCycles)
  exact h₁.trans h₂.symm

/-- The original concrete cocycle class is the original categorical cycle class. -/
theorem cocycleClass_eq_homologyπ (p : ℕ) (a : Cocycle K p) :
    cocycleClass K p a = (K.homologyπ p).hom
      (K.cyclesMk a.val (p + 1) (next_nat p) (cocycle_condition K p a)) := by
  rw [cyclesMk_eq]
  exact (congrArg (fun m => m.hom a) ((K.sc p).moduleCatCyclesIso_inv_π)).symm

variable {S : ShortComplex (CochainComplex (ModuleCat.{0} ℤ) ℕ)} (hS : S.ShortExact)

/-- The actual connecting map has the original lift--coboundary representative formula. -/
theorem connecting_cocycleClass (p : ℕ) (a : Cocycle S.X₃ p)
    (b : S.X₂.X p) (hb : (S.g.f p).hom b = a.val) (c : Cocycle S.X₁ (p + 1))
    (hc : (S.f.f (p + 1)).hom c.val = (S.X₂.d p (p + 1)).hom b) :
    (hS.δ p (p + 1) rfl).hom (cocycleClass S.X₃ p a) = cocycleClass S.X₁ (p + 1) c := by
  have hδ := hS.δ_apply p (p + 1) rfl a.val (cocycle_condition S.X₃ p a) b hb c.val hc
    (p + 2) (next_nat (p + 1))
  exact (congrArg (hS.δ p (p + 1) rfl).hom (cocycleClass_eq_homologyπ S.X₃ p a)).trans
    (hδ.trans (cocycleClass_eq_homologyπ S.X₁ (p + 1) c).symm)

/-- Short exactness constructs both actual lifts and their genuine connecting class. -/
theorem exists_connecting_lift (p : ℕ) (a : Cocycle S.X₃ p) :
    ∃ (b : S.X₂.X p) (_hb : (S.g.f p).hom b = a.val) (c : Cocycle S.X₁ (p + 1)),
      (S.f.f (p + 1)).hom c.val = (S.X₂.d p (p + 1)).hom b ∧
      (hS.δ p (p + 1) rfl).hom (cocycleClass S.X₃ p a) = cocycleClass S.X₁ (p + 1) c := by
  have hd := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS p
  let : Epi (S.g.f p) := hd.epi_g
  obtain ⟨b, hb⟩ := (ModuleCat.epi_iff_surjective (S.g.f p)).mp inferInstance a.val
  have hz : (S.g.f (p + 1)).hom ((S.X₂.d p (p + 1)).hom b) = 0 := by
    have he := congrArg (fun m => m.hom b) (S.g.comm p (p + 1))
    exact he.symm.trans ((congrArg (S.X₃.d p (p + 1)).hom hb).trans (cocycle_condition S.X₃ p a))
  have hd' := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS (p + 1)
  obtain ⟨c, hc⟩ := (ShortComplex.moduleCat_exact_iff _).mp hd'.exact _ hz
  have hcz : (S.X₁.d (p + 1) (p + 2)).hom c = 0 :=
    hS.d_eq_zero_of_f_eq_d_apply p (p + 1) b c hc (p + 2)
  let z := mkCocycle S.X₁ (p + 1) c hcz
  exact ⟨b, hb, z, hc, connecting_cocycleClass hS p a b hb z hc⟩

end NoExoticSixSphere.CochainConnecting
