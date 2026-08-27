import ErdosProblems.Erdos587.HooleyZonotopeMap
import ErdosProblems.Erdos587.HooleyRobustSpanning

/-! # Finite coordinate changes agreeing with a surjective real linear map -/

namespace Erdos587.GeneralizedAP

theorem delta_robust_span_coordinate_image {d n : ℕ} (U : Finset (Fin d → ℤ)) (k : ℕ)
    (hspan : ∀ V ⊆ U, k ≤ V.card →
      Submodule.span ℝ (intCastVec '' (V : Set (Fin d → ℤ))) = ⊤)
    (ψ : (Fin d → ℤ) → Fin n → ℤ)
    (q : (Fin d → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (hq : Function.Surjective q)
    (hψ : ∀ u ∈ U, intCastVec (ψ u) = q (intCastVec u)) :
    ∀ V ⊆ U.image ψ, k ≤ V.card →
      Submodule.span ℝ (intCastVec '' (V : Set (Fin n → ℤ))) = ⊤ := by
  classical
  intro V hVU hkV
  let W := U.filter (fun u => ψ u ∈ V)
  have hW : W ⊆ U := Finset.filter_subset _ _
  have himage : W.image ψ = V := by
    ext y
    constructor
    · intro hy
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
      exact (Finset.mem_filter.mp hu).2
    · intro hy
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp (hVU hy)
      exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨hu, hy⟩, rfl⟩
  have hkW : k ≤ W.card := hkV.trans (himage ▸ Finset.card_image_le)
  have hmap := CFP.delta_robust_spanning_image U intCastVec k hspan q hq W hW hkW
  have himageR : (q ∘ intCastVec) '' (W : Set (Fin d → ℤ)) =
      intCastVec '' (V : Set (Fin n → ℤ)) := by
    rw [← himage, Finset.coe_image, Set.image_image]
    apply Set.image_congr
    intro u hu
    exact (hψ u (hW hu)).symm
  rwa [himageR] at hmap

lemma delta_injOn_of_evaluation {α β γ : Type*} (ψ : α → β) (f : α → γ) (g : β → γ)
    {U : Set α} (hU : Set.InjOn f U) (hψ : ∀ u ∈ U, g (ψ u) = f u) : Set.InjOn ψ U := by
  intro u hu v hv h
  apply hU hu hv
  exact (hψ u hu).symm.trans ((congrArg g h).trans (hψ v hv))

lemma delta_zonotope_coordinate_image {d n : ℕ} (U : Finset (Fin d → ℤ))
    (ψ : (Fin d → ℤ) → Fin n → ℤ) (hinj : Set.InjOn ψ U)
    (q : (Fin d → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hψ : ∀ u ∈ U, intCastVec (ψ u) = q (intCastVec u)) :
    CFP.deltaZonotope (fun u : U.image ψ => intCastVec (u : Fin n → ℤ)) =
      q '' CFP.deltaZonotope (fun u : U => intCastVec (u : Fin d → ℤ)) := by
  classical
  let f : U → U.image ψ := fun u => ⟨ψ u, Finset.mem_image_of_mem ψ u.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro u v huv
      exact Subtype.ext (hinj u.property v.property (congrArg Subtype.val huv))
    · rintro ⟨y, hy⟩
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨⟨u, hu⟩, rfl⟩
  let e := Equiv.ofBijective f hf
  rw [← CFP.deltaZonotope_reindex (fun u : U.image ψ => intCastVec (u : Fin n → ℤ)) e]
  have hfun : (fun u : U.image ψ => intCastVec (u : Fin n → ℤ)) ∘ e =
      q ∘ (fun u : U => intCastVec (u : Fin d → ℤ)) := by
    funext u
    exact hψ u u.property
  rw [hfun, CFP.deltaZonotope_linear_image]

end Erdos587.GeneralizedAP
