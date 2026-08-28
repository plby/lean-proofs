import Wikipedia.HopfProblem.DegreeCollapseDiskCylinder
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Compatible bottom and boundary data glue on the native disk cylinder

The gluing space is the literal bottom-or-side subset of the cylinder.
Its topology is verified by a compact quotient, not imposed on the maps.
-/

noncomputable section

open Set Metric Topology
open scoped unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def boundaryToDisk : C(Sphere (E := E), Disk (E := E)) :=
  ⟨fun u => ⟨u.val, sphere_subset_closedBall u.property⟩, continuous_subtype_val.subtype_mk _⟩

def bottomMap : C(Disk (E := E), bottomOrSide (E := E)) :=
  ⟨fun u => ⟨(0, u), Or.inl rfl⟩, (continuous_const.prodMk continuous_id).subtype_mk _⟩

def sideMap : C(I × Sphere (E := E), bottomOrSide (E := E)) :=
  ⟨fun p => ⟨(p.1, boundaryToDisk p.2), Or.inr (mem_sphere_zero_iff_norm.mp p.2.property)⟩,
    (continuous_fst.prodMk (boundaryToDisk.continuous.comp continuous_snd)).subtype_mk _⟩

def bottomSideQuotient : C(Disk (E := E) ⊕ (I × Sphere (E := E)), bottomOrSide (E := E)) :=
  ⟨Sum.elim bottomMap sideMap, bottomMap.continuous.sumElim sideMap.continuous⟩

omit [NormedSpace ℝ E] in
theorem bottomSideQuotient_surjective : Function.Surjective (bottomSideQuotient (E := E)) := by
  rintro ⟨⟨t, u⟩, ht | hu⟩
  · change t = 0 at ht
    subst t
    exact ⟨.inl u, rfl⟩
  · exact ⟨.inr (t, ⟨u.val, mem_sphere_zero_iff_norm.mpr hu⟩), rfl⟩

variable [FiniteDimensional ℝ E]

theorem bottomSideQuotient_isQuotientMap : IsQuotientMap (bottomSideQuotient (E := E)) :=
  .of_surjective_continuous bottomSideQuotient_surjective bottomSideQuotient.continuous

variable {X : Type*} [TopologicalSpace X]
  (f : C(Disk (E := E), X)) (G : C(I × Sphere (E := E), X))
  (h0 : ∀ u, G (0, u) = f (boundaryToDisk u))

def bottomSideData : C(Disk (E := E) ⊕ (I × Sphere (E := E)), X) :=
  ⟨Sum.elim f G, f.continuous.sumElim G.continuous⟩

include h0 in
omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem bottomSideData_constant_on_fibres
    (a b : Disk (E := E) ⊕ (I × Sphere (E := E)))
    (h : bottomSideQuotient a = bottomSideQuotient b) :
    bottomSideData f G a = bottomSideData f G b := by
  have he := congrArg Subtype.val h
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg f (congrArg Prod.snd he)
    | inr b =>
      have ht : (0 : I) = b.1 := congrArg Prod.fst he
      have hu : a = boundaryToDisk b.2 := congrArg Prod.snd he
      exact (congrArg f hu).trans ((h0 b.2).symm.trans
        (congrArg G (Prod.ext ht rfl)))
  | inr a =>
    cases b with
    | inl b =>
      change G a = f b
      have ht : a.1 = (0 : I) := congrArg Prod.fst he
      have hu : boundaryToDisk a.2 = b := congrArg Prod.snd he
      have ha : a = (0, a.2) := Prod.ext ht rfl
      exact (congrArg G ha).trans ((h0 a.2).trans (congrArg f hu))
    | inr b =>
      change G a = G b
      have ht : a.1 = b.1 := congrArg (fun p : I × Disk (E := E) => p.1) he
      have hu : a.2.val = b.2.val :=
        congrArg (fun p : I × Disk (E := E) => p.2.val) he
      exact congrArg G (Prod.ext ht (Subtype.ext hu))

def gluedBottomSide : C(bottomOrSide (E := E), X) :=
  bottomSideQuotient_isQuotientMap.lift (bottomSideData f G)
    (bottomSideData_constant_on_fibres f G h0)

@[simp] theorem gluedBottomSide_apply
    (z : Disk (E := E) ⊕ (I × Sphere (E := E))) :
    gluedBottomSide f G h0 (bottomSideQuotient z) = bottomSideData f G z :=
  ContinuousMap.congr_fun
    (bottomSideQuotient_isQuotientMap.lift_comp (bottomSideData f G)
      (bottomSideData_constant_on_fibres f G h0)) z

@[simp] theorem gluedBottomSide_bottom (u : Disk (E := E)) :
    gluedBottomSide f G h0 (bottomMap u) = f u := gluedBottomSide_apply f G h0 (.inl u)

@[simp] theorem gluedBottomSide_side (p : I × Sphere (E := E)) :
    gluedBottomSide f G h0 (sideMap p) = G p := gluedBottomSide_apply f G h0 (.inr p)

end Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder
