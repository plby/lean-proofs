import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Algebra.Category.Grp.Limits

/-!
# Gluing local isomorphisms of actual additive sheaves

Natural local section isomorphisms which agree on common subopens
glue on every open set by the genuine sheaf gluing theorem. Their
inverses are glued in the source sheaf, and local uniqueness proves
the two global maps are inverse. No global comparison is an input.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

universe u v

namespace Wikipedia.HopfProblem.CanonicalPushforwardLocalIso

variable {X : TopCat.{u}} {κ : Type v}

/-- Sections of the actual given additive sheaf. -/
abbrev Section (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : Opens X) : Type u :=
  F.obj.obj (op U)

/-- The actual restriction homomorphism of the given sheaf. -/
def restrict (F : TopCat.Sheaf AddCommGrpCat.{u} X) {U V : Opens X} (h : U ≤ V) :
    Section F V →+ Section F U :=
  (F.obj.map (homOfLE h).op).hom

@[simp] theorem restrict_refl (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (U : Opens X) (s : Section F U) : restrict F (le_refl U) s = s := by
  change F.obj.map (𝟙 (op U)) s = s
  exact congrArg (fun f : F.obj.obj (op U) ⟶ F.obj.obj (op U) => f s)
    (F.obj.map_id (op U))

@[simp] theorem restrict_restrict (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    {U V W : Opens X} (hUV : U ≤ V) (hVW : V ≤ W) (s : Section F W) :
    restrict F hUV (restrict F hVW s) = restrict F (hUV.trans hVW) s := by
  change F.obj.map (homOfLE hUV).op (F.obj.map (homOfLE hVW).op s) =
    F.obj.map (homOfLE (hUV.trans hVW)).op s
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Intersect the actual covering opens with an arbitrary open domain. -/
def chartCover (C : κ → Opens X) (U : Opens X) (i : κ) : Opens X := U ⊓ C i

theorem chartCover_le (C : κ → Opens X) (U : Opens X) (i : κ) :
    chartCover C U i ≤ U := inf_le_left

theorem chartCover_le_chart (C : κ → Opens X) (U : Opens X) (i : κ) :
    chartCover C U i ≤ C i := inf_le_right

theorem chartCover_covers (C : κ → Opens X) (hC : ∀ x : X, ∃ i, x ∈ C i)
    (U : Opens X) : U ≤ iSup (chartCover C U) := by
  intro x hx
  obtain ⟨i, hi⟩ := hC x
  exact Opens.mem_iSup.mpr ⟨i, hx, hi⟩

/-- Equality is detected on the restrictions of the actual open cover. -/
theorem eq_of_chartCover (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (C : κ → Opens X) (hC : ∀ x : X, ∃ i, x ∈ C i) (U : Opens X)
    (s t : Section F U)
    (h : ∀ i, restrict F (chartCover_le C U i) s =
      restrict F (chartCover_le C U i) t) : s = t :=
  F.eq_of_locally_eq' (chartCover C U) U (fun i => homOfLE (chartCover_le C U i))
    (chartCover_covers C hC U) s t h

/-- Actual local section isomorphisms, natural on all subopens and
agreeing on every common subopen of two covering charts. -/
structure Data (F G : TopCat.Sheaf AddCommGrpCat.{u} X) (C : κ → Opens X) where
  cover : ∀ x : X, ∃ i, x ∈ C i
  localEquiv : ∀ (i : κ) (U : Opens X), U ≤ C i → Section F U ≃+ Section G U
  naturality : ∀ (i : κ) {U V : Opens X} (h : U ≤ V) (hV : V ≤ C i) (s : Section F V),
    restrict G h (localEquiv i V hV s) =
      localEquiv i U (h.trans hV) (restrict F h s)
  agreement : ∀ (i j : κ) (U : Opens X) (hi : U ≤ C i) (hj : U ≤ C j) (s : Section F U),
    localEquiv i U hi s = localEquiv j U hj s

namespace Data

variable {F G : TopCat.Sheaf AddCommGrpCat.{u} X} {C : κ → Opens X}
  (L : Data F G C)

/-- The inverse local isomorphisms satisfy the same actual descent laws. -/
def symm : Data G F C where
  cover := L.cover
  localEquiv i U hU := (L.localEquiv i U hU).symm
  naturality := by
    intro i U V h hV s
    apply (L.localEquiv i U (h.trans hV)).injective
    rw [← L.naturality i h hV]
    simp only [AddEquiv.apply_symm_apply]
  agreement := by
    intro i j U hi hj s
    apply (L.localEquiv i U hi).injective
    rw [(L.localEquiv i U hi).apply_symm_apply, L.agreement i j U hi hj,
      (L.localEquiv j U hj).apply_symm_apply]

@[simp] theorem symm_localEquiv (i : κ) (U : Opens X) (hU : U ≤ C i) :
    L.symm.localEquiv i U hU = (L.localEquiv i U hU).symm := rfl

/-- Apply each local isomorphism to the genuine restricted section. -/
def localImage (U : Opens X) (s : Section F U) (i : κ) :
    Section G (chartCover C U i) :=
  L.localEquiv i (chartCover C U i) (chartCover_le_chart C U i)
    (restrict F (chartCover_le C U i) s)

theorem localImage_compatible (U : Opens X) (s : Section F U) :
    TopCat.Presheaf.IsCompatible G.obj (chartCover C U) (L.localImage U s) := by
  intro i j
  change restrict G inf_le_left (L.localImage U s i) =
    restrict G inf_le_right (L.localImage U s j)
  rw [localImage, localImage, L.naturality, L.naturality,
    restrict_restrict, restrict_restrict]
  exact L.agreement i j _ _ _ _

/-- Genuine unique gluing in the target sheaf produces the global image. -/
theorem existsUnique_mapSection (U : Opens X) (s : Section F U) :
    ∃! t : Section G U, ∀ i,
      restrict G (chartCover_le C U i) t = L.localImage U s i :=
  G.existsUnique_gluing' (chartCover C U) U
    (fun i => homOfLE (chartCover_le C U i)) (chartCover_covers C L.cover U)
    (L.localImage U s) (L.localImage_compatible U s)

/-- The actual global section obtained from the local section images. -/
def mapSection (U : Opens X) (s : Section F U) : Section G U :=
  (L.existsUnique_mapSection U s).choose

theorem mapSection_restrict_chartCover (U : Opens X) (s : Section F U) (i : κ) :
    restrict G (chartCover_le C U i) (L.mapSection U s) = L.localImage U s i :=
  (L.existsUnique_mapSection U s).choose_spec.1 i

/-- The glued map is the given local map on every chart subopen. -/
theorem mapSection_restrict_chart (i : κ) {U V : Opens X} (h : U ≤ V)
    (hU : U ≤ C i) (s : Section F V) :
    restrict G h (L.mapSection V s) = L.localEquiv i U hU (restrict F h s) := by
  let h' : U ≤ chartCover C V i := le_inf h hU
  calc
    _ = restrict G h' (restrict G (chartCover_le C V i) (L.mapSection V s)) :=
      (restrict_restrict G h' (chartCover_le C V i) (L.mapSection V s)).symm
    _ = restrict G h' (L.localImage V s i) :=
      congrArg (restrict G h') (L.mapSection_restrict_chartCover V s i)
    _ = L.localEquiv i U hU (restrict F h s) := by
      rw [localImage, L.naturality, restrict_restrict]

/-- The map on all opens commutes with the original restrictions. -/
theorem mapSection_restrict {U V : Opens X} (h : U ≤ V) (s : Section F V) :
    restrict G h (L.mapSection V s) = L.mapSection U (restrict F h s) := by
  apply eq_of_chartCover G C L.cover U
  intro i
  calc
    _ = restrict G ((chartCover_le C U i).trans h) (L.mapSection V s) :=
      restrict_restrict G (chartCover_le C U i) h (L.mapSection V s)
    _ = L.localEquiv i (chartCover C U i) (chartCover_le_chart C U i)
        (restrict F ((chartCover_le C U i).trans h) s) :=
      L.mapSection_restrict_chart i ((chartCover_le C U i).trans h)
        (chartCover_le_chart C U i) s
    _ = L.localEquiv i (chartCover C U i) (chartCover_le_chart C U i)
        (restrict F (chartCover_le C U i) (restrict F h s)) :=
      congrArg (L.localEquiv i (chartCover C U i) (chartCover_le_chart C U i))
        (restrict_restrict F (chartCover_le C U i) h s).symm
    _ = restrict G (chartCover_le C U i) (L.mapSection U (restrict F h s)) :=
      (L.mapSection_restrict_chartCover U (restrict F h s) i).symm

theorem mapSection_add (U : Opens X) (s t : Section F U) :
    L.mapSection U (s + t) = L.mapSection U s + L.mapSection U t := by
  apply eq_of_chartCover G C L.cover U
  intro i
  simp only [map_add, mapSection_restrict_chartCover, localImage]

/-- Gluing the inverse local maps in the source sheaf undoes the forward map. -/
theorem symm_mapSection_mapSection (U : Opens X) (s : Section F U) :
    L.symm.mapSection U (L.mapSection U s) = s := by
  apply eq_of_chartCover F C L.cover U
  intro i
  rw [mapSection_restrict_chartCover, localImage, mapSection_restrict_chartCover, localImage]
  exact (L.localEquiv i (chartCover C U i) (chartCover_le_chart C U i)).symm_apply_apply _

theorem mapSection_symm_mapSection (U : Opens X) (s : Section G U) :
    L.mapSection U (L.symm.mapSection U s) = s := by
  apply eq_of_chartCover G C L.cover U
  intro i
  rw [mapSection_restrict_chartCover, localImage, mapSection_restrict_chartCover, localImage]
  exact (L.localEquiv i (chartCover C U i) (chartCover_le_chart C U i)).apply_symm_apply _

/-- Actual global section isomorphisms, constructed from the local ones. -/
def sectionAddEquiv (U : Opens X) : Section F U ≃+ Section G U where
  toFun := L.mapSection U
  invFun := L.symm.mapSection U
  left_inv := L.symm_mapSection_mapSection U
  right_inv := L.mapSection_symm_mapSection U
  map_add' := L.mapSection_add U

@[simp] theorem sectionAddEquiv_apply (U : Opens X) (s : Section F U) :
    L.sectionAddEquiv U s = L.mapSection U s := rfl

@[simp] theorem sectionAddEquiv_symm_apply (U : Opens X) (s : Section G U) :
    (L.sectionAddEquiv U).symm s = L.symm.mapSection U s := rfl

theorem sectionAddEquiv_restrict_chartCover (U : Opens X) (s : Section F U) (i : κ) :
    restrict G (chartCover_le C U i) (L.sectionAddEquiv U s) =
      L.localEquiv i (chartCover C U i) (chartCover_le_chart C U i)
        (restrict F (chartCover_le C U i) s) :=
  L.mapSection_restrict_chartCover U s i

theorem sectionAddEquiv_restrict_chart (i : κ) {U V : Opens X} (h : U ≤ V)
    (hU : U ≤ C i) (s : Section F V) :
    restrict G h (L.sectionAddEquiv V s) = L.localEquiv i U hU (restrict F h s) :=
  L.mapSection_restrict_chart i h hU s

theorem sectionAddEquiv_symm_restrict_chart (i : κ) {U V : Opens X} (h : U ≤ V)
    (hU : U ≤ C i) (s : Section G V) :
    restrict F h ((L.sectionAddEquiv V).symm s) =
      (L.localEquiv i U hU).symm (restrict G h s) :=
  L.symm.mapSection_restrict_chart i h hU s

theorem sectionAddEquiv_restrict {U V : Opens X} (h : U ≤ V) (s : Section F V) :
    restrict G h (L.sectionAddEquiv V s) = L.sectionAddEquiv U (restrict F h s) :=
  L.mapSection_restrict h s

theorem sectionAddEquiv_symm_restrict {U V : Opens X} (h : U ≤ V) (s : Section G V) :
    restrict F h ((L.sectionAddEquiv V).symm s) =
      (L.sectionAddEquiv U).symm (restrict G h s) :=
  L.symm.mapSection_restrict h s

/-- On every chart subopen the global isomorphism equals the given local one. -/
theorem sectionAddEquiv_eq_local (i : κ) (U : Opens X) (hU : U ≤ C i) :
    L.sectionAddEquiv U = L.localEquiv i U hU := by
  apply AddEquiv.ext
  intro s
  simpa only [restrict_refl] using L.sectionAddEquiv_restrict_chart i (le_refl U) hU s

theorem sectionAddEquiv_symm_eq_local (i : κ) (U : Opens X) (hU : U ≤ C i) :
    (L.sectionAddEquiv U).symm = (L.localEquiv i U hU).symm :=
  congrArg AddEquiv.symm (L.sectionAddEquiv_eq_local i U hU)

end Data

end Wikipedia.HopfProblem.CanonicalPushforwardLocalIso
