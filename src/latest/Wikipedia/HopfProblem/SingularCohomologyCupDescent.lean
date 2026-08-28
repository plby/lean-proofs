import Wikipedia.HopfProblem.SingularCohomologyFreeCycles
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductBilinear

/-!
# Bilinear descent to actual cochain homology

A bilinear operation on genuine cocycles that annihilates an incoming
coboundary in either argument descends to the actual categorical homology
objects of the cochain complexes.  This is the quotient construction used
for the singular cup product; no freeness assumption is involved.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SingularCohomologyCup

open SingularCohomologyFree

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule
  PeriodTorusHigherHomology.integerLinearMapModule

variable (K : CochainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)

/-- The literal incoming coboundaries, as a submodule of the actual cocycle kernel. -/
abbrev cohomologyBoundaries : Submodule ℤ (Cocycle K n) :=
  FirstHurewicz.ChainHomology.ShortBoundaries (K.sc n)

variable {M : Type*} [AddCommGroup M] [Module ℤ M]

/-- Maps on categorical cohomology are determined by their values on genuine cocycles. -/
theorem cohomologyLinearMap_ext {f g : K.homology n →ₗ[ℤ] M}
    (h : ∀ c : Cocycle K n, f (cocycleClass K n c) = g (cocycleClass K n c)) : f = g := by
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := cocycleClass_surjective K n x
  exact h c

variable (f : Cocycle K n →ₗ[ℤ] M)
  (hf : ∀ b : K.X (n - 1), f (coboundaryCocycle K n b) = 0)

include hf in
/-- Annihilating the actual incoming coboundaries kills the full canonical boundary submodule. -/
theorem cohomologyBoundaries_le_ker : cohomologyBoundaries K n ≤ LinearMap.ker f := by
  rintro c ⟨b, hb⟩
  have hc : cocycleClass K n c = 0 :=
    (FirstHurewicz.ChainHomology.shortCycleClass_eq_zero_iff (K.sc n) c).mpr
      ⟨b, congrArg Subtype.val hb⟩
  obtain ⟨b', hb'⟩ := (cocycleClass_eq_zero_iff K n c).mp hc
  have he : coboundaryCocycle K n b' = c := Subtype.ext hb'
  exact (congrArg f he).symm.trans (hf b')

/-- Canonical descent from genuine cocycles to actual categorical cohomology. -/
def cohomologyDesc : K.homology n →ₗ[ℤ] M :=
  ((cohomologyBoundaries K n).liftQ f (cohomologyBoundaries_le_ker K n f hf)).comp
    (K.sc n).moduleCatHomologyIso.hom.hom

@[simp] theorem cohomologyDesc_cocycleClass (c : Cocycle K n) :
    cohomologyDesc K n f hf (cocycleClass K n c) = f c := by
  have h := congrArg (fun q => q.hom (Submodule.Quotient.mk c))
    (K.sc n).moduleCatHomologyIso.inv_hom_id
  exact congrArg ((cohomologyBoundaries K n).liftQ f
    (cohomologyBoundaries_le_ker K n f hf)) h

theorem cohomologyDesc_comp_cocycleClass :
    (cohomologyDesc K n f hf).comp (cocycleClass K n) = f := by
  apply LinearMap.ext
  intro c
  exact cohomologyDesc_cocycleClass K n f hf c

/-- The actual cocycle-class formula uniquely specifies descent. -/
theorem cohomologyDesc_unique (g : K.homology n →ₗ[ℤ] M)
    (hg : ∀ c : Cocycle K n, g (cocycleClass K n c) = f c) :
    g = cohomologyDesc K n f hf := by
  apply cohomologyLinearMap_ext K n
  intro c
  rw [hg, cohomologyDesc_cocycleClass]

section Bilinear

variable (L : CochainComplex (ModuleCat.{0} ℤ) ℕ) (m : ℕ)
  (F : Cocycle K n →ₗ[ℤ] Cocycle L m →ₗ[ℤ] M)
  (hFright : ∀ (a : Cocycle K n) (b : L.X (m - 1)),
    F a (coboundaryCocycle L m b) = 0)
  (hFleft : ∀ (a : K.X (n - 1)) (b : Cocycle L m),
    F (coboundaryCocycle K n a) b = 0)

/-- Descent in the right input retains linear dependence on the left cocycle. -/
def bilinearCohomologyDescRight : Cocycle K n →ₗ[ℤ] (L.homology m →ₗ[ℤ] M) where
  toFun a := cohomologyDesc L m (F a) (hFright a)
  map_add' a b := by
    apply cohomologyLinearMap_ext L m
    intro c
    simp only [LinearMap.add_apply, cohomologyDesc_cocycleClass]
    exact congrArg (fun g : Cocycle L m →ₗ[ℤ] M => g c) (F.map_add a b)
  map_smul' r a := by
    apply cohomologyLinearMap_ext L m
    intro c
    simp only [LinearMap.smul_apply, RingHom.id_apply, cohomologyDesc_cocycleClass]
    exact congrArg (fun g : Cocycle L m →ₗ[ℤ] M => g c) (F.map_smul r a)

@[simp] theorem bilinearCohomologyDescRight_cocycleClass
    (a : Cocycle K n) (b : Cocycle L m) :
    bilinearCohomologyDescRight K n L m F hFright a (cocycleClass L m b) = F a b :=
  cohomologyDesc_cocycleClass L m (F a) (hFright a) b

include hFleft in
theorem bilinearCohomologyDescRight_coboundary (a : K.X (n - 1)) :
    bilinearCohomologyDescRight K n L m F hFright (coboundaryCocycle K n a) = 0 := by
  apply cohomologyLinearMap_ext L m
  intro b
  rw [bilinearCohomologyDescRight_cocycleClass, LinearMap.zero_apply]
  exact hFleft a b

/-- Descent in both inputs uses the two actual incoming-coboundary conditions. -/
def bilinearCohomologyDesc : K.homology n →ₗ[ℤ] (L.homology m →ₗ[ℤ] M) :=
  cohomologyDesc K n (bilinearCohomologyDescRight K n L m F hFright)
    (bilinearCohomologyDescRight_coboundary K n L m F hFright hFleft)

/-- The descended bilinear map is the original operation on both genuine representatives. -/
@[simp] theorem bilinearCohomologyDesc_cocycleClass
    (a : Cocycle K n) (b : Cocycle L m) :
    bilinearCohomologyDesc K n L m F hFright hFleft
        (cocycleClass K n a) (cocycleClass L m b) = F a b := by
  rw [bilinearCohomologyDesc, cohomologyDesc_cocycleClass,
    bilinearCohomologyDescRight_cocycleClass]

/-- Equality on both genuine cocycle representatives proves equality on actual cohomology. -/
theorem bilinearCohomologyMap_ext
    {f g : K.homology n →ₗ[ℤ] L.homology m →ₗ[ℤ] M}
    (h : ∀ (a : Cocycle K n) (b : Cocycle L m),
      f (cocycleClass K n a) (cocycleClass L m b) =
        g (cocycleClass K n a) (cocycleClass L m b)) : f = g := by
  apply cohomologyLinearMap_ext K n
  intro a
  exact cohomologyLinearMap_ext L m (h a)

end Bilinear
end Wikipedia.HopfProblem.SingularCohomologyCup
