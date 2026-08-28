import Wikipedia.HopfProblem.TriangleUniformizationGluingRemovable
import Mathlib.Topology.LocallyFinite

/-!
# Finite and relatively locally finite unions of removable sets

Relatively closed continuously removable sets are stable under finite
unions.  For a family that is locally finite only inside an open domain,
an open neighbourhood in the domain subtype meets finitely many members.
Its open image in the complex plane reduces local removability of the
whole union to that finite-union result.
-/

noncomputable section

open Set Filter Topology

namespace Wikipedia.HopfProblem.TriangleUniformizationGluing

/-- To remove a union, first remove the left set away from the relatively
closed right set, then remove the right set on the whole open test domain. -/
theorem ContinuousRemovable.union {Ω S T : Set ℂ}
    (hS : ContinuousRemovable Ω S) (hT : ContinuousRemovable Ω T)
    (hclosedT : IsOpen (Ω \ T)) : ContinuousRemovable Ω (S ∪ T) := by
  intro V hV hVΩ f hf hd
  have hVT : IsOpen (V \ T) := by
    have he : V \ T = V ∩ (Ω \ T) := by
      ext z
      constructor
      · intro hz
        exact ⟨hz.1, hVΩ hz.1, hz.2⟩
      · intro hz
        exact ⟨hz.1, hz.2.2⟩
    rw [he]
    exact hV.inter hclosedT
  have hdiff : DifferentiableOn ℂ f (V \ T) := by
    apply hS (V \ T) hVT (sdiff_subset.trans hVΩ) f (hf.mono sdiff_subset)
    intro z hz
    exact hd z ⟨hz.1.1, fun hu => hu.elim hz.2 hz.1.2⟩
  apply hT V hV hVΩ f hf
  intro z hz
  exact hdiff.differentiableAt (hVT.mem_nhds hz)

/-- A finite family of relatively closed continuously removable sets has
a continuously removable union. -/
theorem continuousRemovable_biUnion_finset {ι : Type*} {Ω : Set ℂ} {S : ι → Set ℂ}
    (t : Finset ι) (hS : ∀ i ∈ t, ContinuousRemovable Ω (S i))
    (hclosed : ∀ i ∈ t, IsOpen (Ω \ S i)) :
    ContinuousRemovable Ω (⋃ i ∈ t, S i) := by
  classical
  revert hS hclosed
  induction t using Finset.induction_on with
  | empty =>
    intro _ _
    simpa using continuousRemovable_empty Ω
  | @insert a t hat ih =>
    intro hS hclosed
    have ht : ContinuousRemovable Ω (⋃ i ∈ t, S i) :=
      ih (fun i hi => hS i (Finset.mem_insert_of_mem hi))
        (fun i hi => hclosed i (Finset.mem_insert_of_mem hi))
    simpa only [Finset.mem_insert, iUnion_iUnion_eq_or_left, union_comm] using
      ht.union (hS a (Finset.mem_insert_self a t))
        (hclosed a (Finset.mem_insert_self a t))

/-- The finite-indexed-family form of finite-union removability. -/
theorem continuousRemovable_iUnion_finite {ι : Type*} [Finite ι] {Ω : Set ℂ}
    (S : ι → Set ℂ) (hS : ∀ i, ContinuousRemovable Ω (S i))
    (hclosed : ∀ i, IsOpen (Ω \ S i)) : ContinuousRemovable Ω (⋃ i, S i) := by
  classical
  let := Fintype.ofFinite ι
  simpa only [Finset.mem_univ, iUnion_true] using
    continuousRemovable_biUnion_finset (Finset.univ : Finset ι)
      (fun i _ => hS i) (fun i _ => hclosed i)

/-- Continuous removability is local on the ambient domain. -/
theorem continuousRemovable_of_locally {Ω S : Set ℂ}
    (hlocal : ∀ z ∈ Ω, ∃ W : Set ℂ,
      IsOpen W ∧ z ∈ W ∧ ContinuousRemovable W S) : ContinuousRemovable Ω S := by
  intro V hV hVΩ f hf hd z hz
  obtain ⟨W, hW, hzW, hrem⟩ := hlocal z (hVΩ hz)
  have hVW : IsOpen (V ∩ W) := hV.inter hW
  have hdiff : DifferentiableOn ℂ f (V ∩ W) := by
    apply hrem (V ∩ W) hVW inter_subset_right f (hf.mono inter_subset_left)
    intro x hx
    exact hd x ⟨hx.1.1, hx.2⟩
  exact (hdiff.differentiableAt (hVW.mem_nhds ⟨hz, hzW⟩)).differentiableWithinAt

/-- Relative local finiteness on an open domain suffices for removability
of an arbitrary union of relatively closed removable sets.  The sets need
not be locally finite at any point outside the domain. -/
theorem continuousRemovable_iUnion_of_locallyFinite {ι : Type*} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (S : ι → Set ℂ)
    (hS : ∀ i, ContinuousRemovable Ω (S i))
    (hclosed : ∀ i, IsOpen (Ω \ S i))
    (hloc : LocallyFinite (fun i => (Subtype.val : Ω → ℂ) ⁻¹' S i)) :
    ContinuousRemovable Ω (⋃ i, S i) := by
  classical
  apply continuousRemovable_of_locally
  intro z hz
  obtain ⟨N, hN, hfin⟩ := hloc ⟨z, hz⟩
  obtain ⟨W, hWN, hW, hzW⟩ := mem_nhds_iff.mp hN
  let t := hfin.toFinset
  have hWΩ : (Subtype.val '' W : Set ℂ) ⊆ Ω := by
    rintro x ⟨w, hw, rfl⟩
    exact w.property
  have hrem : ContinuousRemovable Ω (⋃ i ∈ t, S i) :=
    continuousRemovable_biUnion_finset t (fun i _ => hS i) (fun i _ => hclosed i)
  refine ⟨Subtype.val '' W, hΩ.isOpenMap_subtype_val _ hW,
    mem_image_of_mem _ hzW, ?_⟩
  apply (hrem.mono_domain hWΩ).mono_set_on
  rintro x ⟨w, hw, rfl⟩ hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  apply mem_iUnion₂.mpr
  refine ⟨i, ?_, hi⟩
  exact hfin.mem_toFinset.mpr ⟨w, hi, hWN hw⟩

end Wikipedia.HopfProblem.TriangleUniformizationGluing
