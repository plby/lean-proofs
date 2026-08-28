import Wikipedia.NoExoticSixSphere.InjectiveOperatorSphereParity

/-!
# Exact disk extensions under normalization and changes of target

These statements retain the actual boundary maps. The target spaces may
have different presentations; a disk-dependent homeomorphism and its
continuous inverse transport the original extensions in both directions.
-/

noncomputable section

namespace NoExoticSixSphere.DiskBoundary

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def Extends (f : C(Sphere 3, X)) : Prop :=
  ∃ F : C(DiskCylinder.Disk (E := Vector 4), X),
    ∀ s, F (DiskCylinder.boundaryToDisk s) = f s

theorem extends_comp (f : C(Sphere 3, X)) (h : Extends f) (k : C(X, Y)) :
    Extends (k.comp f) := by
  obtain ⟨F, hF⟩ := h
  exact ⟨k.comp F, fun s ↦ congrArg k (hF s)⟩

theorem extends_homotopic_iff {f g : C(Sphere 3, X)} (h : f.Homotopic g) :
    Extends f ↔ Extends g := by
  constructor
  · rintro ⟨F, hF⟩
    exact exists_extension_of_homotopic h F hF
  · rintro ⟨G, hG⟩
    exact exists_extension_of_homotopic h.symm G hG

theorem extends_diskHomeomorph_iff
    (H : DiskCylinder.Disk (E := Vector 4) → (X ≃ₜ Y))
    (hH : Continuous (fun p : DiskCylinder.Disk (E := Vector 4) × X ↦ H p.1 p.2))
    (hHi : Continuous (fun p : DiskCylinder.Disk (E := Vector 4) × Y ↦ (H p.1).symm p.2))
    (f : C(Sphere 3, X)) (g : C(Sphere 3, Y))
    (hfg : ∀ s, g s = H (DiskCylinder.boundaryToDisk s) (f s)) :
    Extends g ↔ Extends f := by
  constructor
  · rintro ⟨G, hG⟩
    refine ⟨⟨fun x ↦ (H x).symm (G x),
      hHi.comp (continuous_id.prodMk G.continuous)⟩, ?_⟩
    intro s
    change (H (DiskCylinder.boundaryToDisk s)).symm (G (DiskCylinder.boundaryToDisk s)) = f s
    rw [hG, hfg, Homeomorph.symm_apply_apply]
  · rintro ⟨F, hF⟩
    refine ⟨⟨fun x ↦ H x (F x), hH.comp (continuous_id.prodMk F.continuous)⟩, ?_⟩
    intro s
    change H (DiskCylinder.boundaryToDisk s) (F (DiskCylinder.boundaryToDisk s)) = g s
    rw [hF, hfg]

theorem extends_normalize_iff {N n : ℕ} (f : C(Sphere 3, Stiefel.Monomorphism.Space N n)) :
    Extends ((Stiefel.Monomorphism.normalize N n).comp f) ↔ Extends f := by
  constructor
  · intro h
    have he := extends_comp _ h (Stiefel.Monomorphism.inclusion N n)
    apply (extends_homotopic_iff
      (f := ((Stiefel.Monomorphism.inclusion N n).comp
        (Stiefel.Monomorphism.normalize N n)).comp f) (g := f) ?_).mp he
    exact ⟨((Stiefel.Monomorphism.normalizationHomotopy N n).compContinuousMap f).symm⟩
  · intro h
    exact extends_comp f h (Stiefel.Monomorphism.normalize N n)

theorem extends_inclusion_iff {N n : ℕ} (f : C(Sphere 3, Stiefel.Space N n)) :
    Extends ((Stiefel.Monomorphism.inclusion N n).comp f) ↔ Extends f := by
  constructor
  · intro h
    have he := extends_comp _ h (Stiefel.Monomorphism.normalize N n)
    have hf : (Stiefel.Monomorphism.normalize N n).comp
        ((Stiefel.Monomorphism.inclusion N n).comp f) = f := by
      apply ContinuousMap.ext
      intro s
      exact Stiefel.Monomorphism.normalize_inclusion (f s)
    rwa [hf] at he
  · intro h
    exact extends_comp f h (Stiefel.Monomorphism.inclusion N n)

end NoExoticSixSphere.DiskBoundary
