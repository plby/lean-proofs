import Wikipedia.HomotopyGroupsOfSpheres.Basic
import Wikipedia.SmoothSixDPoincare.SpherePointConnecting

/-!
# A sphere quotient with only one possibly nontrivial fiber

Off the exceptional value, the original quotient is a homeomorphism. Removing
one further source point gives compatible covers by contractible open sets.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.SpherePinch

local instance (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨by simp⟩

variable {n m : ℕ} (f : C(Sphere n, Sphere m)) (b : Sphere m)
variable (hq : IsQuotientMap f)
variable (hi : ∀ u v, f u ≠ b → f u = f v → u = v)

def patch : Set (Sphere n) := f ⁻¹' {b}ᶜ

theorem patch_open : IsOpen (patch f b) :=
  isClosed_singleton.isOpen_compl.preimage f.continuous

def patchHomeomorph : ↥(patch f b) ≃ₜ ↥({b}ᶜ : Set (Sphere m)) := by
  let g := ({b}ᶜ : Set (Sphere m)).restrictPreimage f
  have hg : IsQuotientMap g := hq.restrictPreimage_isOpen isClosed_singleton.isOpen_compl
  have hinj : Function.Injective g := by
    intro u v h
    exact Subtype.ext (hi u.val v.val u.property (congrArg Subtype.val h))
  exact (Equiv.ofBijective g ⟨hinj, hg.surjective⟩).toHomeomorph
    (fun _ ↦ hg.isCoinducing.isOpen_preimage)

theorem patchHomeomorph_apply (u : patch f b) :
    (patchHomeomorph f b hq hi u).val = f u.val := rfl

include hq hi in
theorem patch_contractible : ContractibleSpace (patch f b) := by
  let : ContractibleSpace ({b}ᶜ : Set (Sphere m)) :=
    Wikipedia.SmoothSixDPoincare.SpherePoint.puncture_contractible (n := m) b
  exact (patchHomeomorph f b hq hi).contractibleSpace

variable (p : Sphere n) (hp : f p ≠ b)

include hi hp in
theorem fiber_eq_point (u : Sphere n) : f u = f p ↔ u = p := by
  constructor
  · intro h
    exact hi u p (h ▸ hp) h
  · rintro rfl
    rfl

include hi hp in
theorem maps_puncture : MapsTo f {p}ᶜ {f p}ᶜ := by
  intro u hu h
  exact hu ((fiber_eq_point f b hi p hp u).mp h)

include hp in
theorem source_cover : {p}ᶜ ∪ patch f b = univ := by
  apply eq_univ_of_forall
  intro u
  by_cases hu : u = p
  · subst u
    exact Or.inr hp
  · exact Or.inl hu

include hp in
theorem target_cover : {f p}ᶜ ∪ {b}ᶜ = univ := by
  apply eq_univ_of_forall
  intro v
  by_cases hv : v = f p
  · subst v
    exact Or.inr hp
  · exact Or.inl hv

def overlapHomeomorph : ↥({p}ᶜ ∩ patch f b) ≃ₜ ↥({f p}ᶜ ∩ ({b}ᶜ : Set (Sphere m))) := by
  let e := patchHomeomorph f b hq hi
  have hinv (v : ↥({f p}ᶜ ∩ ({b}ᶜ : Set (Sphere m)))) :
      (e.symm ⟨v.val, v.property.2⟩).val ≠ p := by
    intro h
    have he := congrArg (fun z : ({b}ᶜ : Set (Sphere m)) ↦ z.val)
      (e.apply_symm_apply ⟨v.val, v.property.2⟩)
    change f (e.symm ⟨v.val, v.property.2⟩).val = v.val at he
    rw [h] at he
    exact v.property.1 he.symm
  exact {
    toFun u := ⟨f u.val, maps_puncture f b hi p hp u.property.1, u.property.2⟩
    invFun v := ⟨(e.symm ⟨v.val, v.property.2⟩).val,
      hinv v, (e.symm ⟨v.val, v.property.2⟩).property⟩
    left_inv u := by
      apply Subtype.ext
      exact congrArg (fun z : patch f b ↦ z.val) (e.symm_apply_apply ⟨u.val, u.property.2⟩)
    right_inv v := by
      apply Subtype.ext
      exact congrArg (fun z : ({b}ᶜ : Set (Sphere m)) ↦ z.val)
        (e.apply_symm_apply ⟨v.val, v.property.2⟩)
    continuous_toFun := (f.continuous.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := (continuous_subtype_val.comp
      (e.symm.continuous.comp (continuous_subtype_val.subtype_mk _))).subtype_mk _ }

theorem overlapHomeomorph_apply (u : ↥({p}ᶜ ∩ patch f b)) :
    (overlapHomeomorph f b hq hi p hp u).val = f u.val := rfl

end Wikipedia.HomotopyGroupsOfSpheres.SpherePinch
