import Wikipedia.HopfProblem.SingularMayerVietorisQuasiIsoCriteria
import Wikipedia.HopfProblem.SingularMayerVietorisSmallChainsBasis
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# Actual chain formality for projective integral homology

The zero-differential complex here has the actual homology modules of the
original complex as its objects. Projectivity supplies linear choices of
cycle representatives. The resulting chain map is proved to be a
quasi-isomorphism using concrete cycles and actual boundaries. When the
chain modules are also projective, Mathlib's nonnegative-projective-complex
theorem upgrades that proved comparison to an actual chain-homotopy
equivalence.

No Künneth theorem or tensor-homology identification is assumed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ChainFormality

open SingularMayerVietoris.ModuleHomology

variable (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)

/-- The actual homology modules, placed in their original degrees with zero
differentials. This is an actual chain complex, not a substitute homology group. -/
def homologyComplex : ChainComplex (ModuleCat.{0} ℤ) ℕ where
  X n := K.homology n
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

@[simp] theorem homologyComplex_X (n : ℕ) : (homologyComplex K).X n = K.homology n := rfl

@[simp] theorem homologyComplex_d (i j : ℕ) : (homologyComplex K).d i j = 0 := rfl

/-- The actual homology maps define a chain map between the zero-differential
homology complexes, without choosing cycle representatives. -/
def homologyComplexMap {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : K ⟶ L) :
    homologyComplex K ⟶ homologyComplex L where
  f n := HomologicalComplex.homologyMap f n
  comm' _ _ _ := comp_zero.trans zero_comp.symm

@[simp] theorem homologyComplexMap_f {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f : K ⟶ L) (n : ℕ) :
    (homologyComplexMap f).f n = HomologicalComplex.homologyMap f n := rfl

/-- A concrete cycle is killed by every outgoing differential, including
those that vanish because of the shape of the complex. -/
theorem cycle_d (n j : ℕ) (c : Cycle K n) : (K.d n j).hom c.1 = 0 := by
  by_cases hnj : (ComplexShape.down ℕ).Rel n j
  · have hc := c.2
    change (K.d n ((ComplexShape.down ℕ).next n)).hom c.1 = 0 at hc
    rw [(ComplexShape.down ℕ).next_eq' hnj] at hc
    exact hc
  · exact congrArg (fun f : K.X n ⟶ K.X j => f.hom c.1) (K.shape n j hnj)

variable [∀ n, Module.Projective ℤ (K.homology n)]

/-- A linear choice of actual cycles representing every actual homology class. -/
def cycleSection (n : ℕ) : K.homology n →ₗ[ℤ] Cycle K n :=
  Classical.choose (Module.projective_lifting_property (cycleClass K n)
    (LinearMap.id : K.homology n →ₗ[ℤ] K.homology n) (cycleClass_surjective K n))

theorem cycleClass_comp_cycleSection (n : ℕ) :
    (cycleClass K n).comp (cycleSection K n) = LinearMap.id :=
  Classical.choose_spec (Module.projective_lifting_property (cycleClass K n)
    (LinearMap.id : K.homology n →ₗ[ℤ] K.homology n) (cycleClass_surjective K n))

@[simp] theorem cycleClass_cycleSection (n : ℕ) (c : K.homology n) :
    cycleClass K n (cycleSection K n c) = c :=
  LinearMap.congr_fun (cycleClass_comp_cycleSection K n) c

/-- Realize the zero-differential homology complex by chosen genuine cycles
in the original complex. -/
def realization : homologyComplex K ⟶ K where
  f n := ModuleCat.ofHom ((Cycle K n).subtype.comp (cycleSection K n))
  comm' i j hij := by
    apply Eq.trans (b := 0)
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact cycle_d K i j (cycleSection K i c)
    · exact zero_comp.symm

@[simp] theorem realization_f_apply (n : ℕ) (c : K.homology n) :
    ((realization K).f n).hom c = (cycleSection K n c).1 := rfl

/-- The realization is a proved quasi-isomorphism: every cycle differs from
its chosen representative by a boundary, and a chosen representative can be
a boundary only when its homology class is zero. -/
theorem realization_quasiIso : QuasiIso (realization K) := by
  apply quasiIso_of_cycle_boundary_lifting (realization K)
  · intro n c
    let z : Cycle (homologyComplex K) n :=
      mkCycle (homologyComplex K) n (cycleClass K n c) rfl
    refine ⟨z, ?_⟩
    have he : cycleClass K n c = cycleClass K n (cycleSection K n (cycleClass K n c)) :=
      (cycleClass_cycleSection K n (cycleClass K n c)).symm
    obtain ⟨b, hb⟩ := (cycleClass_eq_iff K n c
      (cycleSection K n (cycleClass K n c))).mp he
    exact ⟨b, hb⟩
  · intro n c b hb
    have hz : cycleClass K n (cycleSection K n c.1) = 0 :=
      (cycleClass_eq_zero_iff K n _).mpr ⟨b, hb⟩
    have hc : c.1 = 0 := (cycleClass_cycleSection K n c.1).symm.trans hz
    refine ⟨0, ?_⟩
    change (0 : K.homology n) = c.1
    exact hc.symm

/-- The cycle map of the realization is exactly the chosen cycle section. -/
theorem mapCycles_realization (n : ℕ) (c : Cycle (homologyComplex K) n) :
    mapCycles (realization K) n c = cycleSection K n c.1 := by
  apply Subtype.ext
  exact mapCycles_val (realization K) n c

/-- Realization preserves the original homology marking, independently of
the choices of cycle representatives. -/
theorem homologyMap_realization_cycleClass (n : ℕ) (c : Cycle (homologyComplex K) n) :
    (HomologicalComplex.homologyMap (realization K) n).hom
      (cycleClass (homologyComplex K) n c) = c.1 :=
  (homologyMap_cycleClass (realization K) n c).trans
    ((congrArg (cycleClass K n) (mapCycles_realization K n c)).trans
      (cycleClass_cycleSection K n c.1))

/-- The realization induces an isomorphism on the actual categorical
homology objects, even without projectivity of the chain modules. -/
def homologyRealizationIso (n : ℕ) : (homologyComplex K).homology n ≅ K.homology n := by
  letI := realization_quasiIso K
  exact isoOfQuasiIsoAt (realization K) n

@[simp] theorem homologyRealizationIso_hom (n : ℕ) :
    (homologyRealizationIso K n).hom = HomologicalComplex.homologyMap (realization K) n := rfl

@[simp] theorem homologyRealizationIso_cycleClass (n : ℕ)
    (c : Cycle (homologyComplex K) n) :
    (homologyRealizationIso K n).hom.hom (cycleClass (homologyComplex K) n c) = c.1 :=
  homologyMap_realization_cycleClass K n c

/-- Although cycle sections need not be natural on chains, the induced
identification of the actual homology groups is natural. -/
theorem homologyRealizationIso_naturality
    {L : ChainComplex (ModuleCat.{0} ℤ) ℕ} [∀ n, Module.Projective ℤ (L.homology n)]
    (f : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap (homologyComplexMap f) n ≫ (homologyRealizationIso L n).hom =
      (homologyRealizationIso K n).hom ≫ HomologicalComplex.homologyMap f n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := cycleClass_surjective (homologyComplex K) n x
  exact (congrArg (homologyRealizationIso L n).hom.hom
    (homologyMap_cycleClass (homologyComplexMap f) n c)).trans
      ((homologyRealizationIso_cycleClass L n _).trans
        ((mapCycles_val (homologyComplexMap f) n c).trans
          (congrArg (HomologicalComplex.homologyMap f n).hom
            (homologyRealizationIso_cycleClass K n c).symm)))

variable [∀ n, Module.Projective ℤ (K.X n)]

/-- The comparison of projective nonnegative complexes is an actual homotopy
equivalence, by the proved quasi-isomorphism and Mathlib's projective-complex theorem. -/
theorem realization_isHomotopyEquivalence :
    HomologicalComplex.homotopyEquivalences (ModuleCat.{0} ℤ) (ComplexShape.down ℕ)
      (realization K) := by
  let (n : ℕ) : CategoryTheory.Projective ((homologyComplex K).X n) :=
    inferInstanceAs (CategoryTheory.Projective (K.homology n))
  let (n : ℕ) : CategoryTheory.Projective (K.X n) := inferInstance
  exact (ChainComplex.quasiIso_iff_of_projective (realization K)).mp (realization_quasiIso K)

/-- An actual chain-homotopy equivalence from the zero-differential actual
homology complex to the original projective complex. -/
def homologyHomotopyEquiv : HomotopyEquiv (homologyComplex K) K :=
  Classical.choose (realization_isHomotopyEquivalence K)

@[simp] theorem homologyHomotopyEquiv_hom :
    (homologyHomotopyEquiv K).hom = realization K :=
  Classical.choose_spec (realization_isHomotopyEquivalence K)

section Singular

variable (X : Type) [TopologicalSpace X]
  [∀ n, Module.Projective ℤ ((FirstHurewicz.singularComplex X).homology n)]

/-- Actual integral singular chains have a homotopy equivalence to their
zero-differential homology complex whenever their actual homology is projective.
No extra freeness hypothesis on singular chains is needed: their proved
simplex basis supplies projectivity in every degree. -/
def singularHomologyHomotopyEquiv :
    HomotopyEquiv (homologyComplex (FirstHurewicz.singularComplex X))
      (FirstHurewicz.singularComplex X) := by
  letI (n : ℕ) : Module.Projective ℤ ((FirstHurewicz.singularComplex X).X n) :=
    Module.Projective.of_basis (FirstHurewicz.chainBasis X n)
  exact homologyHomotopyEquiv (FirstHurewicz.singularComplex X)

@[simp] theorem singularHomologyHomotopyEquiv_hom :
    (singularHomologyHomotopyEquiv X).hom = realization (FirstHurewicz.singularComplex X) := by
  let (n : ℕ) : Module.Projective ℤ ((FirstHurewicz.singularComplex X).X n) :=
    Module.Projective.of_basis (FirstHurewicz.chainBasis X n)
  exact homologyHomotopyEquiv_hom (FirstHurewicz.singularComplex X)

end Singular

end Wikipedia.HopfProblem.ChainFormality
