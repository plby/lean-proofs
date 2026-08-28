import Wikipedia.HopfProblem.SheafLerayCurveExt
import Wikipedia.HopfProblem.SheafLerayCurveCyclesResolution
import Wikipedia.HopfProblem.SheafLerayLowDegreesAbstractResolution
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-!
# Genuine cycles and boundary Ext vanishing in the needed finite range

The hypotheses concern only the actual homology objects of the original
complex. The cycle groups are not declared acyclic: their required Ext
vanishing is proved by induction using the original boundary short exact
sequences and their native connecting maps.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.SheafLerayCurve.Abstract

open CuspNormalization.SheafCohomologyResolution

universe u

variable {C : Type u} [Category.{0} C] [Abelian C] [HasExt.{0} C]
  (A : C) (K : CochainComplex C ℕ)

/-- The explicit triangular finite range of actual homology-object Ext
vanishings needed by the curve-type Leray edges. -/
def HigherVanishing (N : ℕ) : Prop :=
  ∀ q p : ℕ, 2 ≤ p → q + p ≤ N → Subsingleton (Ext A (K.homology q) p)

theorem HigherVanishing.mono {N M : ℕ} (h : HigherVanishing A K N) (hMN : M ≤ N) :
    HigherVanishing A K M :=
  fun q p hp hqp => h q p hp (hqp.trans hMN)

/-- The needed positive Ext vanishing of each term follows from its
actual injectivity, not from a separate acyclicity hypothesis. -/
theorem term_ext_subsingleton (hI : ∀ q : ℕ, Injective (K.X q))
    (q p : ℕ) (hp : 0 < p) : Subsingleton (Ext A (K.X q) p) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  let : Injective (K.X q) := hI q
  exact Ext.subsingleton_of_injective A (K.X q) r

/-- The original cycles inherit just the required finite range of
positive Ext vanishing, by genuine boundary dimension shifting. -/
theorem cycles_ext_subsingleton (hI : ∀ q : ℕ, Injective (K.X q))
    (N : ℕ) (h : HigherVanishing A K N) (q p : ℕ) (hp : 2 ≤ p)
    (hqp : q + p ≤ N) : Subsingleton (Ext A (K.cycles q) p) := by
  induction q generalizing p with
  | zero =>
    let : Subsingleton (Ext A (K.homology 0) p) := h 0 p hp hqp
    exact ExtComparison.subsingleton_of_iso A
      (SheafLerayLowDegrees.Abstract.initialCyclesIso K).symm p
  | succ q ih =>
    let R := cyclesResolution K q
    let : Subsingleton (Ext A R.complex.X₁ p) :=
      term_ext_subsingleton A K hI q p (by omega)
    let : Subsingleton (Ext A R.F (p + 1)) := ih (p + 1) (by omega) (by omega)
    let : Subsingleton (Ext A R.K p) :=
      ⟨fun x y => (connecting_injective A R.first_shortExact p)
        (Subsingleton.elim (connecting A R.first_shortExact p x)
          (connecting A R.first_shortExact p y))⟩
    let : Subsingleton (Ext A R.complex.X₃ p) := h (q + 1) p hp hqp
    exact ExtComparison.middle_subsingleton A R.second_shortExact p

/-- The original boundary object is the kernel of the original homology
quotient. Its positive Ext vanishing follows from the actual connecting
injection into the next cycle Ext group. -/
theorem boundary_ext_subsingleton (hI : ∀ q : ℕ, Injective (K.X q))
    (N : ℕ) (h : HigherVanishing A K N) (n p : ℕ) (hp : 1 ≤ p)
    (hnp : n + p + 1 ≤ N) :
    Subsingleton (Ext A (cyclesResolution K n).K p) := by
  let R := cyclesResolution K n
  let : Subsingleton (Ext A R.complex.X₁ p) :=
    term_ext_subsingleton A K hI n p hp
  let : Subsingleton (Ext A R.F (p + 1)) :=
    cycles_ext_subsingleton A K hI N h n (p + 1) (by omega) (by omega)
  exact ⟨fun x y => (connecting_injective A R.first_shortExact p)
    (Subsingleton.elim (connecting A R.first_shortExact p x)
      (connecting A R.first_shortExact p y))⟩

/-- The actual cycle-to-homology quotient induces an isomorphism on
degree-one Ext once the two proved adjacent boundary Ext groups vanish. -/
def cyclesHomologyExtOneEquiv (hI : ∀ q : ℕ, Injective (K.X q))
    (N : ℕ) (h : HigherVanishing A K N) (n : ℕ) (hn : n + 3 ≤ N) :
    Ext A (K.cycles (n + 1)) 1 ≃+ Ext A (K.homology (n + 1)) 1 := by
  let : Subsingleton (Ext A (cyclesResolution K n).K 1) :=
    boundary_ext_subsingleton A K hI N h n 1 (by omega) (by omega)
  let : Subsingleton (Ext A (cyclesResolution K n).K 2) :=
    boundary_ext_subsingleton A K hI N h n 2 (by omega) (by omega)
  exact ExtComparison.rightMapEquiv A (cyclesResolution K n).second_shortExact 1

/-- Its forward map is precisely the original homology quotient on Ext. -/
@[simp] theorem cyclesHomologyExtOneEquiv_apply (hI : ∀ q : ℕ, Injective (K.X q))
    (N : ℕ) (h : HigherVanishing A K N) (n : ℕ) (hn : n + 3 ≤ N)
    (x : Ext A (K.cycles (n + 1)) 1) :
    cyclesHomologyExtOneEquiv A K hI N h n hn x =
      x.comp (Ext.mk₀ (K.homologyπ (n + 1))) (add_zero 1) := rfl

/-- The same original map as an isomorphism in the category of abelian groups. -/
def cyclesHomologyExtOneIso (hI : ∀ q : ℕ, Injective (K.X q))
    (N : ℕ) (h : HigherVanishing A K N) (n : ℕ) (hn : n + 3 ≤ N) :
    AddCommGrpCat.of (Ext A (K.cycles (n + 1)) 1) ≅
      AddCommGrpCat.of (Ext A (K.homology (n + 1)) 1) :=
  (cyclesHomologyExtOneEquiv A K hI N h n hn).toAddCommGrpIso

@[simp] theorem cyclesHomologyExtOneIso_hom (hI : ∀ q : ℕ, Injective (K.X q))
    (N : ℕ) (h : HigherVanishing A K N) (n : ℕ) (hn : n + 3 ≤ N) :
    (cyclesHomologyExtOneIso A K hI N h n hn).hom =
      (extFunctorObj A 1).map (K.homologyπ (n + 1)) := rfl

end Wikipedia.HopfProblem.SheafLerayCurve.Abstract
