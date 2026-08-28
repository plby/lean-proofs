import Wikipedia.HopfProblem.CuspNormalizationSheafPullbackBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafReducedSheaf
import Wikipedia.HopfProblem.HolomorphicFunctionSheafCohomologyZeroBasic
import Mathlib.Topology.Sheaves.Functors

/-!
# The actual reduced-function pullback as a sheaf morphism

Composition with a holomorphic map into a subset gives a morphism from
the independently defined reduced holomorphic-function sheaf to the
actual pushforward of the holomorphic-function sheaf on the source.
Its components and naturality are the literal function pullbacks.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafPullback

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℂ E H)
  {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace G] {N : Type} [TopologicalSpace N] [ChartedSpace G N]
  (J : ModelWithCorners ℂ F G) (S : Set M)
  (g : ContMDiffMap J I N M ω) (hg : ∀ x : N, g x ∈ S)

/-- The actual continuous map into the subset as a morphism of topological spaces. -/
def topMap : TopCat.of N ⟶ TopCat.of S :=
  TopCat.ofHom ⟨subsetMap I J S g hg, subsetMap_continuous I J S g hg⟩

@[simp] theorem topMap_apply (x : N) :
    topMap I J S g hg x = subsetMap I J S g hg x := rfl

theorem topMap_preimageOpen (U : Opens S) :
    (Opens.map (topMap I J S g hg)).obj U = preimageOpen I J S g hg U := rfl

/-- The genuine sheaf morphism induced by actual holomorphic composition. -/
def pullback : SheafReduced.sheaf I S ⟶
    (TopCat.Sheaf.pushforward CommRingCat (topMap I J S g hg)).obj
      (HolomorphicFunctionSheaf.sheaf J N) :=
  ObjectProperty.homMk
    { app U := CommRingCat.ofHom (pullbackSection I J S g hg U.unop).toRingHom
      naturality _ _ _ := by ext s; rfl }

@[simp] theorem pullback_app (U : Opens S) (s : SheafReduced.Section I S U) :
    (pullback I J S g hg).hom.app (op U) s = pullbackSection I J S g hg U s := rfl

/-- Surjectivity of the actual map makes pullback injective on every
actual relative-open section ring. -/
theorem pullbackSection_injective
    (hsurj : Function.Surjective (subsetMap I J S g hg)) (U : Opens S) :
    Function.Injective (pullbackSection I J S g hg U) := by
  intro s t h
  apply Subtype.ext
  funext y
  obtain ⟨x, hx⟩ := hsurj y.val
  have hxU : x ∈ preimageOpen I J S g hg U := by
    change subsetMap I J S g hg x ∈ U
    rw [hx]
    exact y.property
  have hy : (⟨subsetMap I J S g hg x, hxU⟩ : U) = y := Subtype.ext hx
  have he := congrArg
    (fun f : HolomorphicFunctionSheaf.Section J N (preimageOpen I J S g hg U) => f ⟨x, hxU⟩) h
  change s ⟨subsetMap I J S g hg x, hxU⟩ = t ⟨subsetMap I J S g hg x, hxU⟩ at he
  simpa only [hy] using he

/-- The additive sheaf morphism underlying the actual ring pullback. -/
def additivePullback : SheafReduced.additiveSheaf I S ⟶
    (TopCat.Sheaf.pushforward AddCommGrpCat (topMap I J S g hg)).obj
      (HolomorphicFunctionSheaf.additiveSheaf J N) :=
  (sheafCompose _ (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).map
    (pullback I J S g hg)

@[simp] theorem additivePullback_app (U : Opens S) (s : SheafReduced.Section I S U) :
    (additivePullback I J S g hg).hom.app (op U) s =
      pullbackSection I J S g hg U s := rfl

end Wikipedia.HopfProblem.CuspNormalization.SheafPullback
