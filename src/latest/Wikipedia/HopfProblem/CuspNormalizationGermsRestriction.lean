import Wikipedia.HopfProblem.CuspNormalizationGermsBasic
import Wikipedia.HopfProblem.CuspNormalizationGermsPlanes
import Wikipedia.HopfProblem.CuspNormalizationGermsFinite

/-!
# Restriction of actual analytic germs to the coordinate branches

The source ring consists of actual ambient analytic germs restricted to
the coordinate-plane union, as elements of its neighbourhood-within germ
ring.  Restriction to each branch is actual analytic composition with the
coordinate-plane inclusion.  A branch germ extends to the ambient space
by the actual coordinate projection.

The kernel of restriction to the union is proved to equal the intersection
of the branch kernels.  This identifies the singular function-germ ring
with the actual image in the product of its analytic branch-germ rings.
-/

noncomputable section

open Set Filter Topology

namespace Wikipedia.HopfProblem.CuspNormalization.Germs

open ToricCharts ToricComponent

local notation "E₂" => CoordinateSpace 2
local notation "E₃" => CoordinateSpace 3

abbrev AmbientGerm := AnalyticGerm (0 : E₃)
abbrev BranchGerm := AnalyticGerm (0 : E₂)

/-- Pullback along the actual coordinate-plane inclusion. -/
def toBranch (j : Fin 3) : AmbientGerm →+* BranchGerm :=
  pullbackAt (insertZero j) (insertZero_holomorphic j).contDiffAt.analyticAt
    (insertZero_zero j)

/-- Actual extension of a branch germ, constant in the omitted coordinate. -/
def extendBranch (j : Fin 3) : BranchGerm →+* AmbientGerm :=
  pullbackAt (removeCoordinate j) (removeCoordinate_holomorphic j).contDiffAt.analyticAt
    (removeCoordinate_zero j)

theorem toBranch_ofAnalytic (j : Fin 3) (f : E₃ → ℂ) (hf : AnalyticAt ℂ f 0) :
    toBranch j (ofAnalytic f hf) =
      ofAnalytic (f ∘ insertZero j)
        (hf.comp_of_eq (insertZero_holomorphic j).contDiffAt.analyticAt (insertZero_zero j)) :=
  pullbackAt_ofAnalytic ..

theorem extendBranch_ofAnalytic (j : Fin 3) (f : E₂ → ℂ) (hf : AnalyticAt ℂ f 0) :
    extendBranch j (ofAnalytic f hf) =
      ofAnalytic (f ∘ removeCoordinate j)
        (hf.comp_of_eq (removeCoordinate_holomorphic j).contDiffAt.analyticAt
          (removeCoordinate_zero j)) :=
  pullbackAt_ofAnalytic ..

/-- Restriction of the actual extension recovers the original branch germ. -/
theorem toBranch_extendBranch (j : Fin 3) (φ : BranchGerm) :
    toBranch j (extendBranch j φ) = φ := by
  obtain ⟨f, hf, rfl⟩ := exists_representative φ
  rw [extendBranch_ofAnalytic, toBranch_ofAnalytic]
  apply (ofAnalytic_eq_iff _ _ _ _).mpr
  exact Eventually.of_forall fun z => by
    simp only [Function.comp_apply, removeCoordinate_insertZero]

theorem toBranch_surjective (j : Fin 3) : Function.Surjective (toBranch j) :=
  fun φ => ⟨extendBranch j φ, toBranch_extendBranch j φ⟩

/-- Simultaneous restriction to the actual selected branches. -/
def toBranches (s : Finset (Fin 3)) : AmbientGerm →+* (s → BranchGerm) :=
  RingHom.pi fun j => toBranch j

@[simp] theorem toBranches_apply (s : Finset (Fin 3)) (φ : AmbientGerm) (j : s) :
    toBranches s φ j = toBranch j φ := rfl

theorem toBranches_coordinate_surjective (s : Finset (Fin 3)) (j : s) :
    Function.Surjective (GermsFinite.coordinateMap (toBranches s) j) :=
  toBranch_surjective j

/-- Restriction to the singular set is a map into its literal
neighbourhood-within germ ring. -/
def toPlaneUnion (s : Finset (Fin 3)) :
    AmbientGerm →+* Filter.Germ (𝓝[planeUnion s] (0 : E₃)) ℂ :=
  (compTendstoRingHom (id : E₃ → E₃)
    ((tendsto_id : Tendsto id (𝓝 (0 : E₃)) (𝓝 (0 : E₃))).mono_left
      nhdsWithin_le_nhds)).comp (analyticSubring (0 : E₃)).subtype

@[simp] theorem toPlaneUnion_ofAnalytic (s : Finset (Fin 3)) (f : E₃ → ℂ)
    (hf : AnalyticAt ℂ f 0) :
    toPlaneUnion s (ofAnalytic f hf) =
      (f : Filter.Germ (𝓝[planeUnion s] (0 : E₃)) ℂ) := rfl

/-- The actual ring of ambient-analytic function germs on the union. -/
abbrev RestrictedAnalyticGerm (s : Finset (Fin 3)) := (toPlaneUnion s).range

/-- The actual subring of compatible branch germs obtained by restriction. -/
abbrev BranchImage (s : Finset (Fin 3)) := (toBranches s).range

theorem toBranch_ofAnalytic_eq_zero_iff (j : Fin 3) (f : E₃ → ℂ)
    (hf : AnalyticAt ℂ f 0) :
    toBranch j (ofAnalytic f hf) = 0 ↔ (f ∘ insertZero j) =ᶠ[𝓝 (0 : E₂)] 0 := by
  rw [toBranch_ofAnalytic]
  exact (ofAnalytic_eq_iff _ (fun _ => 0) _ analyticAt_const)

theorem toPlaneUnion_ofAnalytic_eq_zero_iff (s : Finset (Fin 3)) (f : E₃ → ℂ)
    (hf : AnalyticAt ℂ f 0) :
    toPlaneUnion s (ofAnalytic f hf) = 0 ↔ f =ᶠ[𝓝[planeUnion s] (0 : E₃)] 0 :=
  Filter.Germ.coe_eq

/-- Restriction to the singular set vanishes exactly when every branch
restriction does; the assertion concerns actual analytic function germs. -/
theorem toPlaneUnion_eq_zero_iff (s : Finset (Fin 3)) (φ : AmbientGerm) :
    toPlaneUnion s φ = 0 ↔ toBranches s φ = 0 := by
  obtain ⟨f, hf, rfl⟩ := exists_representative φ
  rw [toPlaneUnion_ofAnalytic_eq_zero_iff, eventually_zero_on_union_iff]
  constructor
  · intro h
    funext j
    exact (toBranch_ofAnalytic_eq_zero_iff j f hf).mpr (h j j.property)
  · intro h j hj
    apply (toBranch_ofAnalytic_eq_zero_iff j f hf).mp
    exact congrFun h ⟨j, hj⟩

theorem kernel_toPlaneUnion (s : Finset (Fin 3)) :
    RingHom.ker (toPlaneUnion s) = RingHom.ker (toBranches s) := by
  ext φ
  exact toPlaneUnion_eq_zero_iff s φ

/-- The actual vanishing ideal on the union is the intersection of the
actual analytic branch vanishing ideals. -/
theorem kernel_toPlaneUnion_eq_iInf (s : Finset (Fin 3)) :
    RingHom.ker (toPlaneUnion s) = ⨅ j : s, RingHom.ker (toBranch j) := by
  rw [kernel_toPlaneUnion]
  exact GermsFinite.ker_eq_iInf_coordinate_ker (toBranches s)

/-- First-isomorphism comparison with the actual branch restriction image. -/
def restrictedEquivBranchImage (s : Finset (Fin 3)) :
    RestrictedAnalyticGerm s ≃+* BranchImage s :=
  (toPlaneUnion s).quotientKerEquivRange.symm.trans
    ((Ideal.quotEquivOfEq (kernel_toPlaneUnion s)).trans
      (toBranches s).quotientKerEquivRange)

end Wikipedia.HopfProblem.CuspNormalization.Germs
