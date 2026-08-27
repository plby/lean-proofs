import ErdosProblems.Erdos587.HooleyLatticeCoordinates

/-! # Pulling a convex body back to the whole lattice of a finite-index subgroup -/

namespace Erdos587.GeneralizedAP

theorem delta_pullback_lattice_full (X : ConvexProgression)
    (Γ : AddSubgroup (Fin X.rank → ℤ)) [Γ.FiniteIndex]
    (b : Module.Basis (Fin X.rank) ℤ Γ.toIntSubmodule)
    (hperiod : ∀ i, intCastVec (Γ.index • Pi.single i (1 : ℤ)) ∈ X.body) :
    Submodule.span ℝ (integerPointCasts ((deltaLatticeRealEquiv Γ b).symm '' X.body)) = ⊤ := by
  let T := deltaLatticeRealEquiv Γ b
  let M := Submodule.span ℝ (integerPointCasts (T.symm '' X.body))
  have hindex : (Γ.index : ℝ) ≠ 0 := by
    exact_mod_cast (AddSubgroup.FiniteIndex.index_ne_zero (H := Γ))
  have hmap : M.map T.toLinearMap = ⊤ := by
    apply top_unique
    rw [← (Pi.basisFun ℝ (Fin X.rank)).span_eq]
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    obtain ⟨y, hy⟩ := (deltaLatticeEmbedding_range Γ b _).mpr
      (Γ.nsmul_index_mem (Pi.single i (1 : ℤ)))
    have hyR : T (intCastVec y) = intCastVec (Γ.index • Pi.single i (1 : ℤ)) := by
      change intLinearMapRealExtension (deltaLatticeEmbedding Γ b) (intCastVec y) = _
      rw [intLinearMapRealExtension_intCastVec, hy]
    have hyBody : intCastVec y ∈ T.symm '' X.body := by
      refine ⟨intCastVec (Γ.index • Pi.single i (1 : ℤ)), hperiod i, ?_⟩
      rw [← hyR, T.symm_apply_apply]
    have hyM : intCastVec y ∈ M := Submodule.subset_span ⟨y, hyBody, rfl⟩
    have hscaled : (Γ.index : ℝ) • Pi.single i (1 : ℝ) ∈ M.map T.toLinearMap := by
      refine Submodule.mem_map.mpr ⟨intCastVec y, hyM, ?_⟩
      change T (intCastVec y) = _
      rw [hyR]
      funext j
      simp [intCastVec, Pi.single_apply]
    have hh := (M.map T.toLinearMap).smul_mem (Γ.index : ℝ)⁻¹ hscaled
    have hmem : Pi.single i (1 : ℝ) ∈ M.map T.toLinearMap := by
      simpa only [inv_smul_smul₀ hindex] using hh
    obtain ⟨z, hz, heq⟩ := Submodule.mem_map.mp hmem
    exact ⟨z, hz, by simpa only [Pi.basisFun_apply] using heq⟩
  apply Submodule.map_injective_of_injective T.injective
  change M.map T.toLinearMap = (⊤ : Submodule ℝ (Fin X.rank → ℝ)).map T.toLinearMap
  rw [hmap, Submodule.map_top, LinearMap.range_eq_top.mpr T.surjective]

noncomputable def deltaLatticePullback (X : ConvexProgression)
    (Γ : AddSubgroup (Fin X.rank → ℤ)) [Γ.FiniteIndex]
    (b : Module.Basis (Fin X.rank) ℤ Γ.toIntSubmodule)
    (hperiod : ∀ i, intCastVec (Γ.index • Pi.single i (1 : ℤ)) ∈ X.body) :
    ConvexProgression where
  rank := X.rank
  base := 0
  eval := 0
  body := (deltaLatticeRealEquiv Γ b).symm '' X.body
  body_zero := ⟨0, X.body_zero, map_zero _⟩
  body_convex := X.body_convex.linear_image _
  body_neg := by
    rintro x ⟨y, hy, rfl⟩
    exact ⟨-y, X.body_neg y hy, map_neg _ _⟩
  body_closed := by
    have hcompact := Metric.isCompact_of_isClosed_isBounded X.body_closed X.body_bounded
    exact (hcompact.image
      (deltaLatticeRealEquiv Γ b).symm.continuous_of_finiteDimensional).isClosed
  body_bounded := by
    have hcompact := Metric.isCompact_of_isClosed_isBounded X.body_closed X.body_bounded
    exact (hcompact.image
      (deltaLatticeRealEquiv Γ b).symm.continuous_of_finiteDimensional).isBounded
  body_full := by
    intro x
    let T := deltaLatticeRealEquiv Γ b
    obtain ⟨c, hc, hcx⟩ := X.body_full (T x)
    refine ⟨c, hc, c • T x, hcx, ?_⟩
    rw [map_smul, T.symm_apply_apply]
  body_lattice_full := delta_pullback_lattice_full X Γ b hperiod

lemma deltaLatticePullback_intPoint_iff (X : ConvexProgression)
    (Γ : AddSubgroup (Fin X.rank → ℤ)) [Γ.FiniteIndex]
    (b : Module.Basis (Fin X.rank) ℤ Γ.toIntSubmodule) (hperiod) (y : Fin X.rank → ℤ) :
    (deltaLatticePullback X Γ b hperiod).IntPoint y ↔
      intCastVec (deltaLatticeEmbedding Γ b y) ∈ X.body := by
  change intCastVec y ∈ (deltaLatticeRealEquiv Γ b).symm '' X.body ↔ _
  let T := deltaLatticeRealEquiv Γ b
  have hy : T (intCastVec y) = intCastVec (deltaLatticeEmbedding Γ b y) :=
    intLinearMapRealExtension_intCastVec _ y
  constructor
  · rintro ⟨w, hw, heq⟩
    have hh : w = intCastVec (deltaLatticeEmbedding Γ b y) :=
      (T.apply_symm_apply w).symm.trans ((congrArg T heq).trans hy)
    exact hh ▸ hw
  · intro hw
    refine ⟨intCastVec (deltaLatticeEmbedding Γ b y), hw, ?_⟩
    exact (congrArg T.symm hy.symm).trans (T.symm_apply_apply _)

lemma deltaLatticePullback_dilate_mem (X : ConvexProgression)
    (Γ : AddSubgroup (Fin X.rank → ℤ)) [Γ.FiniteIndex]
    (b : Module.Basis (Fin X.rank) ℤ Γ.toIntSubmodule) (hperiod) (s : ℝ) (y : Fin X.rank → ℤ)
    (hy : intCastVec y ∈ bodyDilate s (deltaLatticePullback X Γ b hperiod).body) :
    intCastVec (deltaLatticeEmbedding Γ b y) ∈ bodyDilate s X.body := by
  let T := deltaLatticeRealEquiv Γ b
  obtain ⟨z, ⟨w, hw, rfl⟩, heq⟩ := hy
  refine ⟨w, hw, ?_⟩
  calc
    s • w = T (s • T.symm w) := by rw [map_smul, T.apply_symm_apply]
    _ = T (intCastVec y) := congrArg T heq
    _ = intCastVec (deltaLatticeEmbedding Γ b y) := intLinearMapRealExtension_intCastVec _ y

end Erdos587.GeneralizedAP
