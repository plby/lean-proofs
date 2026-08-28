import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologySection

/-!
# Transitions between actual section product charts

Changing a base section from `s` to `g • s` changes the fibre coordinate of
the same quotient point from `f` to `g • f`. The representative identities
also hold for sections on different open sets at a common base lift orbit.
-/

noncomputable section

open Set Topology TopologicalSpace

namespace Wikipedia.HopfProblem.DiagonalQuotient

variable {G B F : Type*} [Group G] [MulAction G B] [MulAction G F]
    [TopologicalSpace B] [TopologicalSpace F]

omit [TopologicalSpace F] in
/-- Changing both coordinates by the same group element leaves the quotient point unchanged. -/
theorem sectionMap_overlap_smul (U V : Opens (BaseSpace G B))
    (s : C(U, B)) (t : C(V, B)) (x : U) (y : V) (g : G)
    (hg : t y = g • s x) (f : F) :
    sectionMap V t (y, g • f) = sectionMap U s (x, f) := by
  change quotient G B F (t y, g • f) = quotient G B F (s x, f)
  rw [hg]
  exact quotient_smul G B F g (s x, f)

omit [TopologicalSpace F] in
/-- Moving the group action from a base lift to its fibre uses the inverse element. -/
theorem sectionMap_overlap (U V : Opens (BaseSpace G B))
    (s : C(U, B)) (t : C(V, B)) (x : U) (y : V) (g : G)
    (hg : t y = g • s x) (f : F) :
    sectionMap V t (y, f) = sectionMap U s (x, g⁻¹ • f) := by
  simpa only [smul_inv_smul] using
    sectionMap_overlap_smul U V s t x y g hg (g⁻¹ • f)

omit [TopologicalSpace F] in
/-- The representative transition on a common section domain. -/
theorem sectionMap_transition_smul (U : Opens (BaseSpace G B))
    (s t : C(U, B)) (x : U) (g : G) (hg : t x = g • s x) (f : F) :
    sectionMap U t (x, g • f) = sectionMap U s (x, f) :=
  sectionMap_overlap_smul U U s t x x g hg f

omit [TopologicalSpace F] in
/-- The inverse-action version of the representative transition. -/
theorem sectionMap_transition (U : Opens (BaseSpace G B))
    (s t : C(U, B)) (x : U) (g : G) (hg : t x = g • s x) (f : F) :
    sectionMap U t (x, f) = sectionMap U s (x, g⁻¹ • f) :=
  sectionMap_overlap U U s t x x g hg f

variable [ContinuousConstSMul G F]

/-- The actual coordinate change at a point where the two section lifts differ by `g`. -/
theorem sectionHomeomorph_transition_apply
    (hq : IsQuotientCoveringMap (baseQuotient G B) G)
    (U : Opens (BaseSpace G B)) (s t : C(U, B))
    (hs : ∀ x : U, baseQuotient G B (s x) = x)
    (ht : ∀ x : U, baseQuotient G B (t x) = x)
    (x : U) (g : G) (hg : t x = g • s x) (f : F) :
    sectionHomeomorph hq U t ht ((sectionHomeomorph hq U s hs).symm (x, f)) =
      (x, g • f) := by
  apply (sectionHomeomorph (F := F) hq U t ht).symm.injective
  rw [Homeomorph.symm_apply_apply]
  apply Subtype.ext
  simpa only [sectionHomeomorph_symm_coe] using
    (sectionMap_transition_smul U s t x g hg f).symm

/-- A constant section transition is the identity on the base times the group
action on the fibre. -/
def sectionTransitionHomeomorph (U : Opens (BaseSpace G B)) (g : G) :
    (U × F) ≃ₜ (U × F) :=
  (Homeomorph.refl U).prodCongr (Homeomorph.smul (α := F) g)

@[simp] theorem sectionTransitionHomeomorph_apply
    (U : Opens (BaseSpace G B)) (g : G) (x : U × F) :
    sectionTransitionHomeomorph U g x = (x.1, g • x.2) := rfl

@[simp] theorem sectionTransitionHomeomorph_symm_apply
    (U : Opens (BaseSpace G B)) (g : G) (x : U × F) :
    (sectionTransitionHomeomorph U g).symm x = (x.1, g⁻¹ • x.2) := rfl

/-- The complete chart transition for sections differing by a constant group element. -/
theorem sectionHomeomorph_transition
    (hq : IsQuotientCoveringMap (baseQuotient G B) G)
    (U : Opens (BaseSpace G B)) (s t : C(U, B))
    (hs : ∀ x : U, baseQuotient G B (s x) = x)
    (ht : ∀ x : U, baseQuotient G B (t x) = x)
    (g : G) (hg : ∀ x : U, t x = g • s x) :
    (sectionHomeomorph (F := F) hq U s hs).symm.trans (sectionHomeomorph hq U t ht) =
      sectionTransitionHomeomorph U g := by
  apply Homeomorph.ext
  intro x
  exact sectionHomeomorph_transition_apply hq U s t hs ht x.1 g (hg x.1) x.2

end Wikipedia.HopfProblem.DiagonalQuotient
