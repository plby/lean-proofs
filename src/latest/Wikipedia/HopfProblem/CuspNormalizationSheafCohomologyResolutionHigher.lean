import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionExtLow

/-!
# Vanishing above a length-two acyclic resolution

This is vanishing of genuine `Ext`, deduced by two applications of
the actual long exact sequence.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyResolution

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

namespace AugmentedResolution

variable (R : AugmentedResolution C) (P : C)

/-- With actual termwise acyclicity, a length-two resolution has no
genuine cohomology above degree two. -/
theorem ext_subsingleton_above_two
    (hA : ∀ n : ℕ, Subsingleton (Ext P R.complex.X₁ (n + 1)))
    (hB : ∀ n : ℕ, Subsingleton (Ext P R.complex.X₂ (n + 1)))
    (hD : ∀ n : ℕ, Subsingleton (Ext P R.complex.X₃ (n + 1))) (n : ℕ) :
    Subsingleton (Ext P R.F (n + 3)) := by
  let := hA (n + 2)
  let := hB (n + 1)
  let := hD n
  have hK : Subsingleton (Ext P R.K (n + 2)) := by
    constructor
    intro x y
    obtain ⟨x', rfl⟩ := connecting_surjective P R.second_shortExact (n + 1) x
    obtain ⟨y', rfl⟩ := connecting_surjective P R.second_shortExact (n + 1) y
    exact congrArg (connecting P R.second_shortExact (n + 1)) (Subsingleton.elim x' y')
  constructor
  intro x y
  obtain ⟨x', rfl⟩ := connecting_surjective P R.first_shortExact (n + 2) x
  obtain ⟨y', rfl⟩ := connecting_surjective P R.first_shortExact (n + 2) y
  exact congrArg (connecting P R.first_shortExact (n + 2)) (hK.elim x' y')

/-- Formula for the degree-two comparison on actual connecting
representatives. -/
theorem extTwoIso_connecting [Subsingleton (Ext P R.complex.X₁ 1)]
    [Subsingleton (Ext P R.complex.X₁ 2)] [Subsingleton (Ext P R.complex.X₂ 1)] :
    AddCommGrpCat.ofHom (R.connectingTwo P) ≫ (R.extTwoIso P).hom =
      cokernel.π ((R.extZeroComplex P).g) := by
  have : Epi (R.extTwoCokernelComplex P).g :=
    (AddCommGrpCat.epi_iff_surjective _).mpr (R.connectingTwo_surjective P)
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (R.extTwoCokernelComplex_exact P).gIsCokernel
    (colimit.isColimit (parallelPair ((R.extZeroComplex P).g) 0)) WalkingParallelPair.one

end AugmentedResolution

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyResolution
