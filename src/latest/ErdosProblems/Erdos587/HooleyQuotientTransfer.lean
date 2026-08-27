import ErdosProblems.Erdos587.HooleyQuotientIteration
import ErdosProblems.Erdos587.HooleyRobustSpanning

/-! # Robust spanning and zonotope mass survive an inner quotient -/

open scoped BigOperators

namespace Erdos587.GeneralizedAP

lemma delta_finset_zonotope_image {d n : ℕ} (U : Finset (Fin d → ℤ))
    (q : (Fin d → ℤ) →ₗ[ℤ] (Fin n → ℤ)) (hinj : Set.InjOn q U) :
    CFP.deltaZonotope (fun u : U.image q => intCastVec (u : Fin n → ℤ)) =
      intLinearMapRealExtension q ''
        CFP.deltaZonotope (fun u : U => intCastVec (u : Fin d → ℤ)) := by
  classical
  let f : U → U.image q := fun u => ⟨q u, Finset.mem_image_of_mem q u.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro u v huv
      exact Subtype.ext (hinj u.property v.property (congrArg Subtype.val huv))
    · rintro ⟨y, hy⟩
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨⟨u, hu⟩, rfl⟩
  let e := Equiv.ofBijective f hf
  rw [← CFP.deltaZonotope_reindex (fun u : U.image q => intCastVec (u : Fin n → ℤ)) e]
  have hfun : (fun u : U.image q => intCastVec (u : Fin n → ℤ)) ∘ e =
      intLinearMapRealExtension q ∘ (fun u : U => intCastVec (u : Fin d → ℤ)) := by
    funext u
    change intCastVec (q u) = intLinearMapRealExtension q (intCastVec u)
    exact (intLinearMapRealExtension_intCastVec q u).symm
  rw [hfun, CFP.deltaZonotope_linear_image]

theorem delta_finset_robust_spanning_image {d n : ℕ} (U : Finset (Fin d → ℤ)) (k : ℕ)
    (hspan : ∀ V ⊆ U, k ≤ V.card →
      Submodule.span ℝ (intCastVec '' (V : Set (Fin d → ℤ))) = ⊤)
    (q : (Fin d → ℤ) →ₗ[ℤ] (Fin n → ℤ)) (hq : Function.Surjective q) :
    ∀ V ⊆ U.image q, k ≤ V.card →
      Submodule.span ℝ (intCastVec '' (V : Set (Fin n → ℤ))) = ⊤ := by
  classical
  intro V hVU hkV
  let W := U.filter (fun u => q u ∈ V)
  have hW : W ⊆ U := Finset.filter_subset _ _
  have himage : W.image q = V := by
    ext y
    constructor
    · rintro hy
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
      exact (Finset.mem_filter.mp hu).2
    · intro hy
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp (hVU hy)
      exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨hu, hy⟩, rfl⟩
  have hkW : k ≤ W.card := hkV.trans (himage ▸ Finset.card_image_le)
  have hmap := CFP.delta_robust_spanning_image U intCastVec k hspan
    (intLinearMapRealExtension q) (intLinearMapRealExtension_surjective q hq) W hW hkW
  have himageR : (intLinearMapRealExtension q ∘ intCastVec) '' (W : Set (Fin d → ℤ)) =
      intCastVec '' (V : Set (Fin n → ℤ)) := by
    rw [← himage, Finset.coe_image, Set.image_image]
    congr 1
    funext u
    exact intLinearMapRealExtension_intCastVec q u
  rwa [himageR] at hmap

lemma DeltaInnerQuotient.injOn (X : ConvexProgression) (D : DeltaInnerQuotient X)
    {U : Set (Fin X.rank → ℤ)} (hU : Set.InjOn X.eval U) : Set.InjOn D.projection U := by
  intro u hu v hv h
  apply hU hu hv
  have hh := congrArg D.progression.eval h
  simpa only [D.eval_projection] using hh

lemma DeltaInnerQuotient.homogeneous (X : ConvexProgression) (D : DeltaInnerQuotient X)
    (hbase : ∃ c, X.eval c = X.base) : ∃ c, D.progression.eval c = D.progression.base := by
  obtain ⟨c, hc⟩ := hbase
  exact ⟨D.projection c, (D.eval_projection c).trans (hc.trans D.base_eq.symm)⟩

lemma DeltaInnerQuotient.rank_pos (X : ConvexProgression) (D : DeltaInnerQuotient X)
    (h : ∃ u, X.eval u ≠ 0) : 0 < D.progression.rank := by
  obtain ⟨u, hu⟩ := h
  by_contra hdim
  have hz : D.progression.rank = 0 := by omega
  have hp0 : D.projection u = 0 := by
    funext i
    have hi := i.isLt
    omega
  have hh := D.eval_projection u
  rw [hp0, map_zero] at hh
  exact hu hh.symm

lemma DeltaInnerQuotient.zonotope (X : ConvexProgression) (D : DeltaInnerQuotient X)
    (U : Finset (Fin X.rank → ℤ)) (hinj : Set.InjOn X.eval U) (δ : ℝ)
    (hsub : ∀ x ∈ CFP.deltaZonotope (fun u : U => intCastVec (u : Fin X.rank → ℤ)),
      δ • x ∈ X.body) :
    ∀ x ∈ CFP.deltaZonotope (fun u : U.image D.projection =>
      intCastVec (u : Fin D.progression.rank → ℤ)),
      (D.factor * δ) • x ∈ D.progression.body := by
  rw [delta_finset_zonotope_image U D.projection (D.injOn X hinj)]
  rintro x ⟨y, hy, rfl⟩
  rw [D.body_eq]
  refine ⟨intLinearMapRealExtension D.projection (δ • y), ⟨δ • y, hsub y hy, rfl⟩, ?_⟩
  rw [map_smul, mul_smul]

end Erdos587.GeneralizedAP
