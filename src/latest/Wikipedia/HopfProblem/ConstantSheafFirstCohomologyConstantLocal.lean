import Wikipedia.HopfProblem.ConstantSheafFirstCohomologyConstantStalk
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Sections of native constant sheaves on connected open sets

Local surjectivity of the actual sheafification unit makes the value of a
section's germ locally constant.  On a preconnected open set these germ
values agree; native sheaf separatedness then identifies the section with
an original constant.  In particular the original germ homomorphism from
a connected nonempty open set is bijective.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory TopCat

namespace Wikipedia.HopfProblem.ConstantSheafFirstCohomology.Constant

variable {X : TopCat.{0}} {A : AddCommGrpCat.{0}}

/-- Every section of the actual constant sheaf is locally an original
constant representative. -/
theorem exists_constant_restriction (U : Opens X)
    (s : (sheaf X A).obj.obj (op U)) (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U) (a : A), x ∈ V ∧
      (unit X A).app (op V) a = (sheaf X A).obj.map (homOfLE hVU).op s := by
  have hloc : TopCat.Presheaf.IsLocallySurjective (unit X A) := by
    change CategoryTheory.Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (presheaf X A))
    infer_instance
  obtain ⟨V, hVU, ⟨a, ha⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff (unit X A)).mp hloc U s x hx
  exact ⟨V, hVU, a, hxV, ha⟩

/-- The actual coefficient value of a section at a point, read through its
original colimit germ. -/
def sectionValue (U : Opens X) (s : (sheaf X A).obj.obj (op U)) (x : U) : A :=
  stalkEquiv X A x.1 (Presheaf.germ (sheaf X A).obj U x.1 x.2 s)

@[simp]
theorem sectionValue_unit (U : Opens X) (a : A) (x : U) :
    sectionValue U ((unit X A).app (op U) a) x = a :=
  stalkEquiv_germ_unit X A x.1 U x.2 a

@[simp]
theorem sectionValue_restrict {U V : Opens X} (i : V ⟶ U)
    (s : (sheaf X A).obj.obj (op U)) (x : V) :
    sectionValue V ((sheaf X A).obj.map i.op s) x =
      sectionValue U s ⟨x.1, i.le x.2⟩ := by
  unfold sectionValue
  rw [TopCat.Presheaf.germ_res_apply]

/-- Native constant-sheaf sections are separated by their actual germ values. -/
theorem section_ext (U : Opens X) (s t : (sheaf X A).obj.obj (op U))
    (h : ∀ x : U, sectionValue U s x = sectionValue U t x) : s = t := by
  apply TopCat.Presheaf.section_ext (sheaf X A) U s t
  intro x hx
  apply (stalkEquiv X A x).injective
  exact h ⟨x, hx⟩

/-- The genuine germ-value function is locally constant, without any local
connectedness hypothesis on the space. -/
theorem sectionValue_isLocallyConstant (U : Opens X)
    (s : (sheaf X A).obj.obj (op U)) : IsLocallyConstant (sectionValue U s) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  obtain ⟨V, hVU, a, hxV, ha⟩ := exists_constant_restriction U s x.1 x.2
  have hval (y : U) (hy : y.1 ∈ V) : sectionValue U s y = a := by
    calc
      sectionValue U s y =
          sectionValue V ((sheaf X A).obj.map (homOfLE hVU).op s) ⟨y.1, hy⟩ :=
        (sectionValue_restrict (homOfLE hVU) s ⟨y.1, hy⟩).symm
      _ = sectionValue V ((unit X A).app (op V) a) ⟨y.1, hy⟩ :=
        congrArg (fun t => sectionValue V t ⟨y.1, hy⟩) ha.symm
      _ = a := sectionValue_unit V a ⟨y.1, hy⟩
  refine ⟨Subtype.val ⁻¹' (V : Set X), V.isOpen.preimage continuous_subtype_val,
    hxV, ?_⟩
  intro y hy
  exact (hval y hy).trans (hval x hxV).symm

/-- On a preconnected open set every native section is an actual constant.
The statement also includes the empty open set. -/
theorem unit_app_surjective (X : TopCat.{0}) (A : AddCommGrpCat.{0})
    (U : Opens X) (hU : IsPreconnected (U : Set X)) :
    Function.Surjective ((unit X A).app (op U)) := by
  let : PreconnectedSpace U := Subtype.preconnectedSpace hU
  intro s
  obtain ⟨a, ha⟩ := (sectionValue_isLocallyConstant U s).exists_eq_const
  refine ⟨a, ?_⟩
  apply section_ext
  intro x
  exact (sectionValue_unit U a x).trans (congrFun ha x).symm

/-- A nonempty open set distinguishes literal constants. -/
theorem unit_app_injective (X : TopCat.{0}) (A : AddCommGrpCat.{0})
    (U : Opens X) (hU : (U : Set X).Nonempty) :
    Function.Injective ((unit X A).app (op U)) := by
  obtain ⟨x, hx⟩ := hU
  intro a b hab
  have h := congrArg (fun s => sectionValue U s ⟨x, hx⟩) hab
  exact (sectionValue_unit U a ⟨x, hx⟩).symm.trans
    (h.trans (sectionValue_unit U b ⟨x, hx⟩))

/-- On a connected nonempty open set the actual unit identifies sections
with the coefficient group. -/
theorem unit_app_bijective (X : TopCat.{0}) (A : AddCommGrpCat.{0})
    (U : Opens X) (hU : IsConnected (U : Set X)) :
    Function.Bijective ((unit X A).app (op U)) :=
  ⟨unit_app_injective X A U hU.nonempty, unit_app_surjective X A U hU.isPreconnected⟩

/-- On a preconnected open set, one germ determines the entire section. -/
theorem germ_injective (X : TopCat.{0}) (A : AddCommGrpCat.{0})
    (U : Opens X) (hU : IsPreconnected (U : Set X)) (x : X) (hx : x ∈ U) :
    Function.Injective (Presheaf.germ (sheaf X A).obj U x hx) := by
  intro s t hst
  obtain ⟨a, rfl⟩ := unit_app_surjective X A U hU s
  obtain ⟨b, rfl⟩ := unit_app_surjective X A U hU t
  have hab := congrArg (stalkEquiv X A x) hst
  have heq : a = b := (stalkEquiv_germ_unit X A x U hx a).symm.trans
    (hab.trans (stalkEquiv_germ_unit X A x U hx b))
  exact congrArg ((unit X A).app (op U)) heq

/-- The original germ map from a connected open neighborhood is bijective. -/
theorem germ_bijective (X : TopCat.{0}) (A : AddCommGrpCat.{0})
    (U : Opens X) (hU : IsConnected (U : Set X)) (x : X) (hx : x ∈ U) :
    Function.Bijective (Presheaf.germ (sheaf X A).obj U x hx) :=
  ⟨germ_injective X A U hU.isPreconnected x hx, germ_surjective X A U x hx⟩

end Wikipedia.HopfProblem.ConstantSheafFirstCohomology.Constant
