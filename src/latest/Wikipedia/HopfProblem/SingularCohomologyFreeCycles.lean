import Wikipedia.HopfProblem.FirstHurewiczChains
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Concrete cocycles and classes in actual cochain homology

The concrete cocycles are kernels of the outgoing differential of an
arbitrary nonnegative integral cochain complex.  Their classes lie in
Mathlib's actual categorical homology object, using its canonical
short-complex kernel/quotient comparison.  Equality of classes is
exactly equality modulo an actual incoming coboundary.

At degree zero the predecessor convention is harmless: the apparent
`0 → 0` differential is zero by the complex shape.  Cochain maps act on
the literal representatives by their given degree components.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SingularCohomologyFree

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule

variable (K : CochainComplex (ModuleCat.{0} ℤ) ℕ)

/-- The actual concrete kernel of the outgoing cochain differential. -/
abbrev Cocycle (n : ℕ) :=
  LinearMap.ker (K.d n ((ComplexShape.up ℕ).next n)).hom

instance cocycleModule (n : ℕ) : Module ℤ (Cocycle K n) := (Cocycle K n).module

theorem next_nat (n : ℕ) : (ComplexShape.up ℕ).next n = n + 1 :=
  CochainComplex.next ℕ n

theorem prev_nat (n : ℕ) : (ComplexShape.up ℕ).prev n = n - 1 := by
  cases n <;> simp

theorem cocycle_condition (n : ℕ) (c : Cocycle K n) :
    (K.d n (n + 1)).hom c.1 = 0 := by
  rw [← next_nat n]
  exact c.2

/-- A cocycle specified by the ordinary `n → n+1` differential. -/
def mkCocycle (n : ℕ) (c : K.X n) (hc : (K.d n (n + 1)).hom c = 0) : Cocycle K n :=
  ⟨c, by
    change (K.d n ((ComplexShape.up ℕ).next n)).hom c = 0
    rw [next_nat n]
    exact hc⟩

@[simp] theorem mkCocycle_val (n : ℕ) (c : K.X n)
    (hc : (K.d n (n + 1)).hom c = 0) : (mkCocycle K n c hc).1 = c := rfl

/-- The canonical class in the actual categorical cochain homology. -/
def cocycleClass (n : ℕ) : Cocycle K n →ₗ[ℤ] K.homology n :=
  FirstHurewicz.ChainHomology.shortCycleClass (K.sc n)

theorem cocycleClass_surjective (n : ℕ) : Function.Surjective (cocycleClass K n) :=
  FirstHurewicz.ChainHomology.shortCycleClass_surjective (K.sc n)

/-- A class vanishes precisely when its actual representative is an incoming coboundary. -/
theorem cocycleClass_eq_zero_iff (n : ℕ) (c : Cocycle K n) :
    cocycleClass K n c = 0 ↔ ∃ b : K.X (n - 1), (K.d (n - 1) n).hom b = c.1 := by
  refine (FirstHurewicz.ChainHomology.shortCycleClass_eq_zero_iff (K.sc n) c).trans ?_
  change (∃ b : K.X ((ComplexShape.up ℕ).prev n),
    (K.d ((ComplexShape.up ℕ).prev n) n).hom b = c.1) ↔ _
  rw [prev_nat]

/-- The actual equality criterion for two cocycle representatives. -/
theorem cocycleClass_eq_iff (n : ℕ) (c d : Cocycle K n) :
    cocycleClass K n c = cocycleClass K n d ↔
      ∃ b : K.X (n - 1), (K.d (n - 1) n).hom b = c.1 - d.1 := by
  simpa only [map_sub, sub_eq_zero, Submodule.coe_sub] using
    cocycleClass_eq_zero_iff K n (c - d)

/-- Every actual incoming coboundary is a cocycle, including degree zero. -/
def coboundaryCocycle (n : ℕ) (b : K.X (n - 1)) : Cocycle K n :=
  mkCocycle K n ((K.d (n - 1) n).hom b)
    (congrArg (fun f : K.X (n - 1) ⟶ K.X (n + 1) => f.hom b)
      (K.d_comp_d (n - 1) n (n + 1)))

@[simp] theorem coboundaryCocycle_val (n : ℕ) (b : K.X (n - 1)) :
    (coboundaryCocycle K n b).1 = (K.d (n - 1) n).hom b := rfl

@[simp] theorem cocycleClass_coboundary (n : ℕ) (b : K.X (n - 1)) :
    cocycleClass K n (coboundaryCocycle K n b) = 0 :=
  (cocycleClass_eq_zero_iff K n _).mpr ⟨b, rfl⟩

/-- There is no nonzero incoming coboundary in degree zero. -/
theorem cocycleClass_zero_eq_zero_iff (c : Cocycle K 0) :
    cocycleClass K 0 c = 0 ↔ c.1 = 0 := by
  rw [cocycleClass_eq_zero_iff]
  have hd : K.d 0 0 = 0 := K.shape 0 0 (by simp)
  simp only [hd, ModuleCat.hom_zero, LinearMap.zero_apply]
  constructor
  · rintro ⟨b, hb⟩
    exact hb.symm
  · intro hc
    exact ⟨0, hc.symm⟩

theorem cocycleClass_zero_injective : Function.Injective (cocycleClass K 0) := by
  intro c d hcd
  have hzero : cocycleClass K 0 (c - d) = 0 := by rw [map_sub, hcd, sub_self]
  have hc := (cocycleClass_zero_eq_zero_iff K (c - d)).mp hzero
  apply Subtype.ext
  exact sub_eq_zero.mp hc

variable {K L : CochainComplex (ModuleCat.{0} ℤ) ℕ} (f : L ⟶ K)

abbrev shortMap (n : ℕ) : L.sc n ⟶ K.sc n :=
  (HomologicalComplex.shortComplexFunctor (ModuleCat.{0} ℤ) (ComplexShape.up ℕ) n).map f

/-- The concrete cocycle map induced by the actual cochain map. -/
def mapCocycles (n : ℕ) : Cocycle L n →ₗ[ℤ] Cocycle K n :=
  ((L.sc n).moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap (shortMap f n) ≫
    (K.sc n).moduleCatCyclesIso.hom).hom

@[simp] theorem mapCocycles_val (n : ℕ) (c : Cocycle L n) :
    (mapCocycles f n c).1 = (f.f n).hom c.1 := by
  have hcat : (L.sc n).moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap (shortMap f n) ≫
      (K.sc n).moduleCatCyclesIso.hom ≫ (K.sc n).moduleCatLeftHomologyData.i =
      (L.sc n).moduleCatLeftHomologyData.i ≫ (shortMap f n).τ₂ := by
    rw [(K.sc n).moduleCatCyclesIso_hom_i, ShortComplex.cyclesMap_i,
      (L.sc n).moduleCatCyclesIso_inv_iCycles_assoc]
  exact congrArg (fun g => g.hom c) hcat

/-- Mathlib's actual homology map sends a cocycle class to the class of
its literal image under the given degree component. -/
theorem homologyMap_cocycleClass (n : ℕ) (c : Cocycle L n) :
    (HomologicalComplex.homologyMap f n).hom (cocycleClass L n c) =
      cocycleClass K n (mapCocycles f n c) := by
  have hcat : (L.sc n).moduleCatLeftHomologyData.π ≫
      (L.sc n).moduleCatHomologyIso.inv ≫ ShortComplex.homologyMap (shortMap f n) =
      ((L.sc n).moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap (shortMap f n) ≫
        (K.sc n).moduleCatCyclesIso.hom) ≫ (K.sc n).moduleCatLeftHomologyData.π ≫
          (K.sc n).moduleCatHomologyIso.inv := by
    simp only [Category.assoc, ← (L.sc n).moduleCatCyclesIso_inv_π_assoc,
      ← (K.sc n).moduleCatCyclesIso_inv_π, Iso.hom_inv_id_assoc]
    rw [ShortComplex.homologyπ_naturality]
  exact congrArg (fun g => g.hom c) hcat

end Wikipedia.HopfProblem.SingularCohomologyFree
