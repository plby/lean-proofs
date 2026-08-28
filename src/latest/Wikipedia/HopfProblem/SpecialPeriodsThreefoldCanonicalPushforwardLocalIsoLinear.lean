import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardLocalIsoBasic
import Mathlib.Algebra.Module.Equiv.Defs

/-!
# Linearity of the genuinely glued section isomorphism

Fix an open set `U`.  Scalars on `U` may restrict to different rings on
the chart intersections `U ∩ C i`.  If the actual sheaf restrictions are
semilinear over these ring homomorphisms and each given local section
isomorphism is linear over its local ring, then the already constructed
global additive isomorphism is linear.  This is proved by restriction
to the cover; global scalar linearity is not an input.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

universe u v

namespace Wikipedia.HopfProblem.CanonicalPushforwardLocalIso.Data

variable {X : TopCat.{u}} {κ : Type v}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} {C : κ → Opens X}
    (L : CanonicalPushforwardLocalIso.Data F G C) (U : Opens X)
    (R : Type*) [Semiring R] (Ri : κ → Type*) [∀ i, Semiring (Ri i)]
    [Module R (Section F U)] [Module R (Section G U)]
    [∀ i, Module (Ri i) (Section F (chartCover C U i))]
    [∀ i, Module (Ri i) (Section G (chartCover C U i))]
    (ρ : ∀ i, R →+* Ri i)
    (hF : ∀ (i : κ) (r : R) (s : Section F U),
      restrict F (chartCover_le C U i) (r • s) =
        ρ i r • restrict F (chartCover_le C U i) s)
    (hG : ∀ (i : κ) (r : R) (s : Section G U),
      restrict G (chartCover_le C U i) (r • s) =
        ρ i r • restrict G (chartCover_le C U i) s)
    (hlocal : ∀ (i : κ) (r : Ri i) (s : Section F (chartCover C U i)),
      L.localEquiv i (chartCover C U i) (chartCover_le_chart C U i) (r • s) =
        r • L.localEquiv i (chartCover C U i) (chartCover_le_chart C U i) s)

include hF hG hlocal in
/-- Scalar linearity of the global map follows from actual local restrictions. -/
theorem sectionAddEquiv_smul (r : R) (s : Section F U) :
    L.sectionAddEquiv U (r • s) = r • L.sectionAddEquiv U s := by
  apply eq_of_chartCover G C L.cover U
  intro i
  rw [L.sectionAddEquiv_restrict_chartCover, hF, hlocal, hG,
    L.sectionAddEquiv_restrict_chartCover]

/-- The true global linear section isomorphism, with the same underlying
map and inverse as the additive isomorphism obtained by sheaf gluing. -/
def sectionLinearEquiv : Section F U ≃ₗ[R] Section G U where
  __ := L.sectionAddEquiv U
  map_smul' := L.sectionAddEquiv_smul U R Ri ρ hF hG hlocal

@[simp] theorem sectionLinearEquiv_toAddEquiv :
    (L.sectionLinearEquiv U R Ri ρ hF hG hlocal).toAddEquiv =
      L.sectionAddEquiv U := rfl

@[simp] theorem sectionLinearEquiv_apply (s : Section F U) :
    L.sectionLinearEquiv U R Ri ρ hF hG hlocal s = L.sectionAddEquiv U s := rfl

@[simp] theorem sectionLinearEquiv_symm_apply (s : Section G U) :
    (L.sectionLinearEquiv U R Ri ρ hF hG hlocal).symm s =
      (L.sectionAddEquiv U).symm s := rfl

include hF hG hlocal in
/-- The inverse of the glued map is linear for the same actual scalar actions. -/
theorem sectionAddEquiv_symm_smul (r : R) (s : Section G U) :
    (L.sectionAddEquiv U).symm (r • s) = r • (L.sectionAddEquiv U).symm s :=
  (L.sectionLinearEquiv U R Ri ρ hF hG hlocal).symm.map_smul r s

/-- The linear upgrade retains the exact original local formula. -/
theorem sectionLinearEquiv_restrict_chartCover (s : Section F U) (i : κ) :
    restrict G (chartCover_le C U i) (L.sectionLinearEquiv U R Ri ρ hF hG hlocal s) =
      L.localEquiv i (chartCover C U i) (chartCover_le_chart C U i)
        (restrict F (chartCover_le C U i) s) :=
  L.sectionAddEquiv_restrict_chartCover U s i

/-- The inverse linear upgrade also retains its actual inverse local formula. -/
theorem sectionLinearEquiv_symm_restrict_chartCover (s : Section G U) (i : κ) :
    restrict F (chartCover_le C U i)
        ((L.sectionLinearEquiv U R Ri ρ hF hG hlocal).symm s) =
      (L.localEquiv i (chartCover C U i) (chartCover_le_chart C U i)).symm
        (restrict G (chartCover_le C U i) s) :=
  L.sectionAddEquiv_symm_restrict_chart i (chartCover_le C U i)
    (chartCover_le_chart C U i) s

end Wikipedia.HopfProblem.CanonicalPushforwardLocalIso.Data
