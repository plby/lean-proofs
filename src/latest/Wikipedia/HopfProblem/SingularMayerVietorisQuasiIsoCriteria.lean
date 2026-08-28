import Wikipedia.HopfProblem.FirstHurewiczChains
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Cycle and boundary criteria for actual homology isomorphisms

The cycle classes in this file take values in Mathlib's categorical homology
of the original chain complex. The canonical module homology isomorphism is
used only to describe representatives and boundaries. The final criterion
turns chain-level lifting statements into `QuasiIso`; it does not assume
excision, a Mayer--Vietoris sequence, or a homology isomorphism.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SingularMayerVietoris.ModuleHomology

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule

variable (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)

/-- The concrete kernel of the outgoing differential of the actual complex. -/
abbrev Cycle (n : ℕ) := LinearMap.ker (K.d n ((ComplexShape.down ℕ).next n)).hom

instance cycleModule (n : ℕ) : Module ℤ (Cycle K n) := (Cycle K n).module

theorem next_nat (n : ℕ) : (ComplexShape.down ℕ).next n = n - 1 := by
  cases n <;> simp

theorem cycle_condition (n : ℕ) (c : Cycle K n) :
    (K.d n (n - 1)).hom c.1 = 0 := by
  rw [← next_nat n]
  exact c.2

/-- A cycle specified by the ordinary `n` to `n - 1` differential. -/
def mkCycle (n : ℕ) (c : K.X n) (hc : (K.d n (n - 1)).hom c = 0) : Cycle K n :=
  ⟨c, by
    change (K.d n ((ComplexShape.down ℕ).next n)).hom c = 0
    rw [next_nat n]
    exact hc⟩

@[simp] theorem mkCycle_val (n : ℕ) (c : K.X n)
    (hc : (K.d n (n - 1)).hom c = 0) : (mkCycle K n c hc).1 = c := rfl

/-- The canonical class in the actual categorical homology object. -/
def cycleClass (n : ℕ) : Cycle K n →ₗ[ℤ] K.homology n :=
  FirstHurewicz.ChainHomology.shortCycleClass (K.sc n)

theorem cycleClass_surjective (n : ℕ) : Function.Surjective (cycleClass K n) :=
  FirstHurewicz.ChainHomology.shortCycleClass_surjective (K.sc n)

theorem cycleClass_eq_zero_iff (n : ℕ) (c : Cycle K n) :
    cycleClass K n c = 0 ↔ ∃ b : K.X (n + 1), (K.d (n + 1) n).hom b = c.1 := by
  refine (FirstHurewicz.ChainHomology.shortCycleClass_eq_zero_iff (K.sc n) c).trans ?_
  change (∃ b : K.X ((ComplexShape.down ℕ).prev n),
    (K.d ((ComplexShape.down ℕ).prev n) n).hom b = c.1) ↔ _
  rw [ChainComplex.prev]

theorem cycleClass_eq_iff (n : ℕ) (c d : Cycle K n) :
    cycleClass K n c = cycleClass K n d ↔
      ∃ b : K.X (n + 1), (K.d (n + 1) n).hom b = c.1 - d.1 := by
  simpa only [map_sub, sub_eq_zero, Submodule.coe_sub] using
    cycleClass_eq_zero_iff K n (c - d)

/-- Every actual boundary is a cycle, also in degree zero. -/
def boundaryCycle (n : ℕ) (b : K.X (n + 1)) : Cycle K n :=
  mkCycle K n ((K.d (n + 1) n).hom b)
    (congrArg (fun f : K.X (n + 1) ⟶ K.X (n - 1) => f.hom b)
      (K.d_comp_d (n + 1) n (n - 1)))

@[simp] theorem boundaryCycle_val (n : ℕ) (b : K.X (n + 1)) :
    (boundaryCycle K n b).1 = (K.d (n + 1) n).hom b := rfl

@[simp] theorem cycleClass_boundary (n : ℕ) (b : K.X (n + 1)) :
    cycleClass K n (boundaryCycle K n b) = 0 :=
  (cycleClass_eq_zero_iff K n _).mpr ⟨b, rfl⟩

variable {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : L ⟶ K)

abbrev shortMap (n : ℕ) : L.sc n ⟶ K.sc n :=
  (HomologicalComplex.shortComplexFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).map f

/-- The actual cycle map, expressed through the canonical concrete kernels. -/
def mapCycles (n : ℕ) : Cycle L n →ₗ[ℤ] Cycle K n :=
  ((L.sc n).moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap (shortMap f n) ≫
    (K.sc n).moduleCatCyclesIso.hom).hom

@[simp] theorem mapCycles_val (n : ℕ) (c : Cycle L n) :
    (mapCycles f n c).1 = (f.f n).hom c.1 := by
  have hcat : (L.sc n).moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap (shortMap f n) ≫
      (K.sc n).moduleCatCyclesIso.hom ≫ (K.sc n).moduleCatLeftHomologyData.i =
      (L.sc n).moduleCatLeftHomologyData.i ≫ (shortMap f n).τ₂ := by
    rw [(K.sc n).moduleCatCyclesIso_hom_i, ShortComplex.cyclesMap_i,
      (L.sc n).moduleCatCyclesIso_inv_iCycles_assoc]
  exact congrArg (fun g => g.hom c) hcat

/-- Cycle representatives commute with Mathlib's actual homology map. -/
theorem homologyMap_cycleClass (n : ℕ) (c : Cycle L n) :
    (HomologicalComplex.homologyMap f n).hom (cycleClass L n c) =
      cycleClass K n (mapCycles f n c) := by
  have hcat : (L.sc n).moduleCatLeftHomologyData.π ≫
      (L.sc n).moduleCatHomologyIso.inv ≫ ShortComplex.homologyMap (shortMap f n) =
      ((L.sc n).moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap (shortMap f n) ≫
        (K.sc n).moduleCatCyclesIso.hom) ≫ (K.sc n).moduleCatLeftHomologyData.π ≫
          (K.sc n).moduleCatHomologyIso.inv := by
    simp only [Category.assoc, ← (L.sc n).moduleCatCyclesIso_inv_π_assoc,
      ← (K.sc n).moduleCatCyclesIso_inv_π, Iso.hom_inv_id_assoc]
    rw [ShortComplex.homologyπ_naturality]
  exact congrArg (fun g => g.hom c) hcat

/-- Lifting cycles modulo actual boundaries gives surjectivity on actual homology. -/
theorem homologyMap_surjective_of_cycle_lifting (n : ℕ)
    (hlift : ∀ c : Cycle K n, ∃ z : Cycle L n, ∃ b : K.X (n + 1),
      (K.d (n + 1) n).hom b = (c.1 : K.X n) - (f.f n).hom z.1) :
    Function.Surjective (HomologicalComplex.homologyMap f n).hom := by
  intro h
  obtain ⟨c, rfl⟩ := cycleClass_surjective K n h
  obtain ⟨z, b, hb⟩ := hlift c
  refine ⟨cycleClass L n z, ?_⟩
  rw [homologyMap_cycleClass]
  apply Eq.symm
  apply (cycleClass_eq_iff K n c (mapCycles f n z)).mpr
  exact ⟨b, by simpa only [mapCycles_val] using hb⟩

/-- Reflecting actual boundaries gives injectivity on actual homology. -/
theorem homologyMap_injective_of_boundary_lifting (n : ℕ)
    (hlift : ∀ c : Cycle L n, ∀ b : K.X (n + 1),
      (K.d (n + 1) n).hom b = (f.f n).hom c.1 →
        ∃ a : L.X (n + 1), (L.d (n + 1) n).hom a = c.1) :
    Function.Injective (HomologicalComplex.homologyMap f n).hom := by
  intro x y hxy
  obtain ⟨c, rfl⟩ := cycleClass_surjective L n x
  obtain ⟨d, rfl⟩ := cycleClass_surjective L n y
  have hz : (HomologicalComplex.homologyMap f n).hom (cycleClass L n (c - d)) = 0 := by
    simp only [map_sub]
    rw [hxy, sub_self]
  rw [homologyMap_cycleClass] at hz
  obtain ⟨b, hb⟩ := (cycleClass_eq_zero_iff K n (mapCycles f n (c - d))).mp hz
  apply (cycleClass_eq_iff L n c d).mpr
  exact hlift (c - d) b (hb.trans (mapCycles_val f n (c - d)))

/-- The two chain-level lifting conditions give a quasi-isomorphism in one degree. -/
theorem quasiIsoAt_of_cycle_boundary_lifting (n : ℕ)
    (hsurj : ∀ c : Cycle K n, ∃ z : Cycle L n, ∃ b : K.X (n + 1),
      (K.d (n + 1) n).hom b = (c.1 : K.X n) - (f.f n).hom z.1)
    (hinj : ∀ c : Cycle L n, ∀ b : K.X (n + 1),
      (K.d (n + 1) n).hom b = (f.f n).hom c.1 →
        ∃ a : L.X (n + 1), (L.d (n + 1) n).hom a = c.1) : QuasiIsoAt f n := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ⟨homologyMap_injective_of_boundary_lifting f n hinj,
    homologyMap_surjective_of_cycle_lifting f n hsurj⟩

/-- A criterion using only cycles and boundaries of the original two complexes. -/
theorem quasiIso_of_cycle_boundary_lifting
    (hsurj : ∀ n, ∀ c : Cycle K n, ∃ z : Cycle L n, ∃ b : K.X (n + 1),
      (K.d (n + 1) n).hom b = (c.1 : K.X n) - (f.f n).hom z.1)
    (hinj : ∀ n, ∀ c : Cycle L n, ∀ b : K.X (n + 1),
      (K.d (n + 1) n).hom b = (f.f n).hom c.1 →
        ∃ a : L.X (n + 1), (L.d (n + 1) n).hom a = c.1) : QuasiIso f := by
  rw [quasiIso_iff]
  intro n
  exact quasiIsoAt_of_cycle_boundary_lifting f n (hsurj n) (hinj n)

/-- An injective chain map reflects the cycle condition whenever its image
differs from a cycle by an actual boundary. -/
theorem cycle_of_boundary_relation (n : ℕ)
    (hf : Function.Injective (f.f (n - 1)).hom)
    (c : K.X n) (hc : (K.d n (n - 1)).hom c = 0)
    (z : L.X n) (b : K.X (n + 1))
    (hb : (K.d (n + 1) n).hom b = c - (f.f n).hom z) :
    (L.d n (n - 1)).hom z = 0 := by
  have hdd : (K.d n (n - 1)).hom ((K.d (n + 1) n).hom b) = 0 :=
    congrArg (fun g : K.X (n + 1) ⟶ K.X (n - 1) => g.hom b)
      (K.d_comp_d (n + 1) n (n - 1))
  have he := congrArg (K.d n (n - 1)).hom hb
  rw [hdd, map_sub, hc, zero_sub] at he
  have hz : (K.d n (n - 1)).hom ((f.f n).hom z) = 0 := neg_eq_zero.mp he.symm
  apply hf
  rw [map_zero]
  exact (congrArg (fun g : L.X n ⟶ K.X (n - 1) => g.hom z)
    (f.comm n (n - 1))).symm.trans hz

/-- A chain-level criterion suited to inclusions of subcomplexes. The first
lifting condition need not supply a cycle in the source: injectivity of the
chain components proves that it is one. -/
theorem quasiIso_of_injective_chain_conditions
    (hf : ∀ n, Function.Injective (f.f n).hom)
    (hsurj : ∀ n, ∀ c : K.X n, (K.d n (n - 1)).hom c = 0 →
      ∃ z : L.X n, ∃ b : K.X (n + 1),
        (K.d (n + 1) n).hom b = c - (f.f n).hom z)
    (hinj : ∀ n, ∀ c : L.X n, (L.d n (n - 1)).hom c = 0 →
      ∀ b : K.X (n + 1), (K.d (n + 1) n).hom b = (f.f n).hom c →
        ∃ a : L.X (n + 1), (L.d (n + 1) n).hom a = c) : QuasiIso f := by
  apply quasiIso_of_cycle_boundary_lifting f
  · intro n c
    obtain ⟨z, b, hb⟩ := hsurj n c.1 (cycle_condition K n c)
    refine ⟨mkCycle L n z ?_, b, hb⟩
    exact cycle_of_boundary_relation f n (hf (n - 1)) c.1 (cycle_condition K n c) z b hb
  · intro n c b hb
    exact hinj n c.1 (cycle_condition L n c) b hb

end Wikipedia.HopfProblem.SingularMayerVietoris.ModuleHomology
