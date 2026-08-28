import Wikipedia.HopfProblem.CuspNormalizationGermsIntegral
import Mathlib.Algebra.Exact.Basic

/-!
# Ordered restriction maps from actual singular analytic germs

The source is the existing ring of ambient analytic germs restricted to
the actual coordinate-plane union.  Indexing its actual branch pullbacks
by one, two, or three ordered labels changes no functions or germ rings.
The image computation is proved on genuine ambient representatives.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.CuspNormalization.SheafGermComplex

open Germs

/-- Actual branch restriction with an explicitly chosen labeling. -/
def labeledRestriction {ι : Type*} (s : Finset (Fin 3)) (label : ι → s) :
    RestrictedAnalyticGerm s →+* (ι → BranchGerm) :=
  RingHom.pi fun i => (Pi.evalRingHom (fun _ : s => BranchGerm) (label i)).comp
    (restrictionToBranches s)

/-- The corresponding actual ambient-to-branch pullbacks. -/
def labeledAmbientRestriction {ι : Type*} (s : Finset (Fin 3)) (label : ι → s) :
    AmbientGerm →+* (ι → BranchGerm) :=
  RingHom.pi fun i => toBranch (label i)

@[simp] theorem labeledRestriction_apply {ι : Type*} (s : Finset (Fin 3)) (label : ι → s)
    (φ : RestrictedAnalyticGerm s) (i : ι) :
    labeledRestriction s label φ i = restrictionToBranches s φ (label i) := rfl

@[simp] theorem labeledAmbientRestriction_apply {ι : Type*} (s : Finset (Fin 3))
    (label : ι → s) (φ : AmbientGerm) (i : ι) :
    labeledAmbientRestriction s label φ i = toBranch (label i) φ := rfl

@[simp] theorem labeledRestriction_rangeRestrict {ι : Type*} (s : Finset (Fin 3))
    (label : ι → s) (φ : AmbientGerm) :
    labeledRestriction s label ((toPlaneUnion s).rangeRestrict φ) =
      labeledAmbientRestriction s label φ := by
  funext i
  change restrictionToBranches s ((toPlaneUnion s).rangeRestrict φ) (label i) = _
  rw [restrictionToBranches_rangeRestrict]
  rfl

/-- No actual singular germ is lost by any labeling covering all branches. -/
theorem labeledRestriction_injective {ι : Type*} (s : Finset (Fin 3)) (label : ι → s)
    (hlabel : Function.Surjective label) : Function.Injective (labeledRestriction s label) := by
  intro φ ψ h
  apply restrictionToBranches_injective s
  funext j
  obtain ⟨i, rfl⟩ := hlabel j
  exact congrFun h i

/-- The source image is exactly the image of actual ambient restrictions,
not an independently imposed algebraic compatibility condition. -/
theorem range_labeledRestriction {ι : Type*} (s : Finset (Fin 3)) (label : ι → s) :
    Set.range (labeledRestriction s label) = Set.range (labeledAmbientRestriction s label) := by
  ext f
  constructor
  · rintro ⟨φ, rfl⟩
    obtain ⟨ψ, hψ⟩ := φ.property
    have he : (toPlaneUnion s).rangeRestrict ψ = φ := Subtype.ext hψ
    refine ⟨ψ, ?_⟩
    rw [← he, labeledRestriction_rangeRestrict]
  · rintro ⟨φ, rfl⟩
    exact ⟨(toPlaneUnion s).rangeRestrict φ, labeledRestriction_rangeRestrict s label φ⟩

def tripleLabel (j : Fin 3) : (Finset.univ : Finset (Fin 3)) :=
  ⟨j, Finset.mem_univ j⟩

theorem tripleLabel_surjective : Function.Surjective tripleLabel :=
  fun j => ⟨j.val, rfl⟩

/-- Pullback from the actual three-plane singular analytic-germ ring. -/
def tripleRestriction : RestrictedAnalyticGerm (Finset.univ : Finset (Fin 3)) →+*
    (Fin 3 → BranchGerm) :=
  labeledRestriction Finset.univ tripleLabel

def tripleAmbientRestriction : AmbientGerm →+* (Fin 3 → BranchGerm) :=
  labeledAmbientRestriction Finset.univ tripleLabel

@[simp] theorem tripleAmbientRestriction_apply (φ : AmbientGerm) (j : Fin 3) :
    tripleAmbientRestriction φ j = toBranch j φ := rfl

@[simp] theorem tripleRestriction_rangeRestrict (φ : AmbientGerm) :
    tripleRestriction ((toPlaneUnion Finset.univ).rangeRestrict φ) =
      tripleAmbientRestriction φ :=
  labeledRestriction_rangeRestrict Finset.univ tripleLabel φ

theorem tripleRestriction_injective : Function.Injective tripleRestriction :=
  labeledRestriction_injective Finset.univ tripleLabel tripleLabel_surjective

theorem range_tripleRestriction :
    Set.range tripleRestriction = Set.range tripleAmbientRestriction :=
  range_labeledRestriction Finset.univ tripleLabel

/-- The standard ordered two-plane model; its intersection is axis two. -/
def doubleBranches : Finset (Fin 3) := {0, 1}

def doubleLabel (i : Fin 2) : doubleBranches :=
  ⟨i.castSucc, by fin_cases i <;> decide⟩

theorem doubleLabel_surjective : Function.Surjective doubleLabel := by
  rintro ⟨j, hj⟩
  have hj' : j = 0 ∨ j = 1 := by simpa only [doubleBranches, Finset.mem_insert,
    Finset.mem_singleton] using hj
  obtain rfl | rfl := hj'
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

/-- Pullback from the actual two-plane singular analytic-germ ring. -/
def doubleRestriction : RestrictedAnalyticGerm doubleBranches →+* (Fin 2 → BranchGerm) :=
  labeledRestriction doubleBranches doubleLabel

def doubleAmbientRestriction : AmbientGerm →+* (Fin 2 → BranchGerm) :=
  labeledAmbientRestriction doubleBranches doubleLabel

@[simp] theorem doubleAmbientRestriction_apply (φ : AmbientGerm) (i : Fin 2) :
    doubleAmbientRestriction φ i = toBranch i.castSucc φ := rfl

@[simp] theorem doubleRestriction_rangeRestrict (φ : AmbientGerm) :
    doubleRestriction ((toPlaneUnion doubleBranches).rangeRestrict φ) =
      doubleAmbientRestriction φ :=
  labeledRestriction_rangeRestrict doubleBranches doubleLabel φ

theorem doubleRestriction_injective : Function.Injective doubleRestriction :=
  labeledRestriction_injective doubleBranches doubleLabel doubleLabel_surjective

theorem range_doubleRestriction :
    Set.range doubleRestriction = Set.range doubleAmbientRestriction :=
  range_labeledRestriction doubleBranches doubleLabel

/-- In the one-plane case the actual restriction is already an isomorphism. -/
def singleRestriction (j : Fin 3) : RestrictedAnalyticGerm {j} →+* BranchGerm :=
  (Pi.evalRingHom (fun _ : ({j} : Finset (Fin 3)) => BranchGerm)
    ⟨j, Finset.mem_singleton_self j⟩).comp (restrictionToBranches {j})

theorem singleRestriction_injective (j : Fin 3) : Function.Injective (singleRestriction j) := by
  intro φ ψ h
  apply restrictionToBranches_injective {j}
  funext k
  have hk : (k : Fin 3) = j := Finset.mem_singleton.mp k.property
  have he : k = ⟨j, Finset.mem_singleton_self j⟩ := Subtype.ext hk
  rw [he]
  exact h

theorem singleRestriction_surjective (j : Fin 3) : Function.Surjective (singleRestriction j) :=
  restrictionToBranches_coordinate_surjective {j} ⟨j, Finset.mem_singleton_self j⟩

def singleRestrictionEquiv (j : Fin 3) : RestrictedAnalyticGerm {j} ≃+* BranchGerm :=
  RingEquiv.ofBijective (singleRestriction j)
    ⟨singleRestriction_injective j, singleRestriction_surjective j⟩

@[simp] theorem singleRestriction_rangeRestrict (j : Fin 3) (φ : AmbientGerm) :
    singleRestriction j ((toPlaneUnion {j}).rangeRestrict φ) = toBranch j φ := by
  change restrictionToBranches {j} ((toPlaneUnion {j}).rangeRestrict φ) _ = _
  rw [restrictionToBranches_rangeRestrict]
  rfl

end Wikipedia.HopfProblem.CuspNormalization.SheafGermComplex
