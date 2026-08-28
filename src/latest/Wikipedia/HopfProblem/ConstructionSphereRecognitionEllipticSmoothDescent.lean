import Wikipedia.HopfProblem.CuspCircleNormalTrivializationRealMaps

/-!
# Smooth descent in the original real atlases

Smoothness is tested through actual surjective local diffeomorphisms.
The product construction retains the original product charts and literal
local inverse.  No atlas is defined by transporting a desired product.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticSmooth

section Descent

variable {E F G H K L M N P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace K] [TopologicalSpace L]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace K N]
  [TopologicalSpace P] [ChartedSpace L P]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  {Q : ModelWithCorners ℝ G L} {n : ℕ∞ω}

/-- Real regularity descends through the original local inverse of a covering.
The covering may be real analytic while the descended map is only smooth. -/
theorem contMDiff_of_comp_real_localDiffeomorph {q : M → N} {f : N → P}
    (hq : IsLocalDiffeomorph I J ω q) (hs : Function.Surjective q)
    (hf : ContMDiff I Q n (f ∘ q)) : ContMDiff J Q n f := by
  intro y
  obtain ⟨x, rfl⟩ := hs y
  have hi : ContMDiffAt J I n (hq x).localInverse (q x) :=
    (hq x).localInverse_contMDiffAt.of_le le_top
  have h := hf.contMDiffAt.comp (q x) hi
  apply h.congr_of_eventuallyEq
  filter_upwards [(hq x).localInverse_eventuallyEq_right] with z hz
  change f z = f (q ((hq x).localInverse z))
  rw [show q ((hq x).localInverse z) = z from hz]

end Descent

section Product

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G H K L M N B : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [TopologicalSpace H] [TopologicalSpace K] [TopologicalSpace L]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace K N]
  [TopologicalSpace B] [ChartedSpace L B]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F K}
  (Q : ModelWithCorners 𝕜 G L) {n : ℕ∞ω}

/-- The identity on the first factor times an actual partial diffeomorphism. -/
def partialDiffeomorph_prodLeft (e : PartialDiffeomorph I J M N n) :
    PartialDiffeomorph (Q.prod I) (Q.prod J) (B × M) (B × N) n where
  toFun p := (p.1, e p.2)
  invFun p := (p.1, e.symm p.2)
  source := univ ×ˢ e.source
  target := univ ×ˢ e.target
  map_source' _ h := ⟨mem_univ _, e.map_source h.2⟩
  map_target' _ h := ⟨mem_univ _, e.map_target h.2⟩
  left_inv' _ h := Prod.ext rfl (e.left_inv h.2)
  right_inv' _ h := Prod.ext rfl (e.right_inv h.2)
  open_source := isOpen_univ.prod e.open_source
  open_target := isOpen_univ.prod e.open_target
  contMDiffOn_toFun := contMDiffOn_fst.prodMk
    (e.contMDiffOn_toFun.comp contMDiffOn_snd (fun _ h => h.2))
  contMDiffOn_invFun := contMDiffOn_fst.prodMk
    (e.contMDiffOn_invFun.comp contMDiffOn_snd (fun _ h => h.2))

@[simp] theorem partialDiffeomorph_prodLeft_apply
    (e : PartialDiffeomorph I J M N n) (p : B × M) :
    partialDiffeomorph_prodLeft Q e p = (p.1, e p.2) := rfl

@[simp] theorem partialDiffeomorph_prodLeft_symm_apply
    (e : PartialDiffeomorph I J M N n) (p : B × N) :
    (partialDiffeomorph_prodLeft Q e).symm p = (p.1, e.symm p.2) := rfl

/-- A covering retains its original local diffeomorphisms after a product with the base. -/
theorem isLocalDiffeomorph_prodLeft {q : M → N} (hq : IsLocalDiffeomorph I J n q) :
    IsLocalDiffeomorph (Q.prod I) (Q.prod J) n
      (fun p : B × M => (p.1, q p.2)) := by
  intro p
  obtain ⟨e, he, hqe⟩ := hq p.2
  refine ⟨partialDiffeomorph_prodLeft Q e, ⟨mem_univ _, he⟩, ?_⟩
  intro x hx
  exact Prod.ext rfl (hqe hx.2)

end Product

end Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticSmooth
