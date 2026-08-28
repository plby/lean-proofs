import Wikipedia.HopfProblem.HolomorphicMeromorphicPullbackFunctor

/-!
# Gluing actual local meromorphic descents

For an open surjective holomorphic map, local sections with the same
actual pullback have equal germs on overlaps: a source point above any
overlap point detects equality through the injective fraction-stalk
pullback. These compatible germs define a genuine global section, whose
local fraction representations come from the given local sections.

On preconnected inverse-image domains, one actual germ equality already
gives the required full local pullback equality by the native identity
principle. No gluing or descent property is assumed.
-/

noncomputable section

open TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  (I : ModelWithCorners ℂ E H) [TopologicalSpace M] [ChartedSpace H M]
  {E' H' N : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [TopologicalSpace H']
  (J : ModelWithCorners ℂ E' H') [TopologicalSpace N] [ChartedSpace H' N]
  [I.Boundaryless] [IsManifold I ω M] [J.Boundaryless] [IsManifold J ω N]

/-- Actual local descents of one global meromorphic function have the same
native germ at any common base point. -/
theorem local_descent_germs_eq (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f)
    (hsurj : _root_.Function.Surjective f) (g : Function I M)
    {U V : Opens N} (s : Section J N U) (t : Section J N V)
    (hs : pullbackSection I J f hf U s =
      restrict I M (le_top : pullbackOpen I J f U ≤ ⊤) g)
    (ht : pullbackSection I J f hf V t =
      restrict I M (le_top : pullbackOpen I J f V ≤ ⊤) g)
    (y : N) (hyU : y ∈ U) (hyV : y ∈ V) :
    s ⟨y, hyU⟩ = t ⟨y, hyV⟩ := by
  obtain ⟨x, rfl⟩ := hsurj y
  apply germPullback_injective I J f hf x
  exact (congrArg (fun a : Section I M (pullbackOpen I J f U) => a ⟨x, hyU⟩) hs).trans
    (congrArg (fun a : Section I M (pullbackOpen I J f V) => a ⟨x, hyV⟩) ht).symm

/-- Overlap compatibility is proved using the actual pullback, not supplied
as an additional sheaf-gluing assumption. -/
theorem local_descent_restrictions_eq (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f)
    (hsurj : _root_.Function.Surjective f) (g : Function I M)
    {U V : Opens N} (s : Section J N U) (t : Section J N V)
    (hs : pullbackSection I J f hf U s =
      restrict I M (le_top : pullbackOpen I J f U ≤ ⊤) g)
    (ht : pullbackSection I J f hf V t =
      restrict I M (le_top : pullbackOpen I J f V ≤ ⊤) g) :
    restrict J N (inf_le_left : U ⊓ V ≤ U) s =
      restrict J N (inf_le_right : U ⊓ V ≤ V) t := by
  apply section_ext
  intro y
  exact local_descent_germs_eq I J f hf hsurj g s t hs ht y.val y.property.1 y.property.2

/-- Genuine local meromorphic descents glue uniquely to a global section
on the original target manifold, with the specified actual pullback. -/
theorem existsUnique_global_descent (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f)
    (hsurj : _root_.Function.Surjective f) (g : Function I M)
    (hlocal : ∀ y : N, ∃ (U : Opens N) (_hy : y ∈ U) (s : Section J N U),
      pullbackSection I J f hf U s =
        restrict I M (le_top : pullbackOpen I J f U ≤ ⊤) g) :
    ∃! s : Function J N, pullbackRingHom I J f hf ⊤ s = g := by
  classical
  choose U hU s hs using hlocal
  let a : (y : (⊤ : Opens N)) → Germ J N y.val :=
    fun y => s y.val ⟨y.val, hU y.val⟩
  have ha : ∀ (y : N) (z : U y), a ⟨z.val, by trivial⟩ = s y z := by
    intro y z
    exact local_descent_germs_eq I J f hf hsurj g (s z.val) (s y) (hs z.val) (hs y)
      z.val (hU z.val) z.property
  let b : Function J N := ⟨a, by
    intro y
    obtain ⟨V, hVU, hyV, p, q, hq, hrep⟩ :=
      local_representation J N (s y.val) ⟨y.val, hU y.val⟩
    refine ⟨V, hyV, homOfLE (le_top : V ≤ ⊤), p, q, hq, ?_⟩
    intro z
    exact (ha y.val (Set.inclusion hVU z)).trans (hrep z)⟩
  have hb : pullbackRingHom I J f hf ⊤ b = g := by
    apply section_ext
    intro x
    change germPullback I J f hf x.val
      (s (f x.val) ⟨f x.val, hU (f x.val)⟩) = g ⟨x.val, by trivial⟩
    exact congrArg (fun t : Section I M (pullbackOpen I J f (U (f x.val))) =>
      t ⟨x.val, hU (f x.val)⟩) (hs (f x.val))
  refine ⟨b, hb, ?_⟩
  intro t ht
  exact pullbackRingHom_injective I J f hf hsurj ⊤ (ht.trans hb.symm)

/-- If a full inverse-image domain is preconnected, a single genuine germ
equality proves the full local pullback equality needed for gluing. -/
theorem existsUnique_global_descent_of_local_germ
    (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f)
    (hsurj : _root_.Function.Surjective f) (g : Function I M)
    (hlocal : ∀ y : N, ∃ (U : Opens N) (_hy : y ∈ U) (s : Section J N U),
      PreconnectedSpace (pullbackOpen I J f U) ∧
        ∃ x : pullbackOpen I J f U,
          pullbackSection I J f hf U s x = g ⟨x.val, by trivial⟩) :
    ∃! s : Function J N, pullbackRingHom I J f hf ⊤ s = g := by
  apply existsUnique_global_descent I J f hf hsurj g
  intro y
  obtain ⟨U, hy, s, hconn, x, hx⟩ := hlocal y
  let _ : PreconnectedSpace (pullbackOpen I J f U) := hconn
  exact ⟨U, hy, s, section_eq_of_germ_eq I M (pullbackSection I J f hf U s)
    (restrict I M (le_top : pullbackOpen I J f U ≤ ⊤) g) x hx⟩

end Wikipedia.HopfProblem.HolomorphicMeromorphic
