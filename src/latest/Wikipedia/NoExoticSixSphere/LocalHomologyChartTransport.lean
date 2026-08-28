import Wikipedia.NoExoticSixSphere.EuclideanLocalHomology
import Wikipedia.NoExoticSixSphere.IntLinearAutomorphism
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Local homology in the original charts

The local homology isomorphism for an open partial homeomorphism is obtained
by restricting to its actual source, using its source-target homeomorphism,
and including its actual target. Thus a chart computes the local homology
of the original space, not a separately assigned local model.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris

namespace NoExoticSixSphere.RelativeSingularHomology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- Point transport with a specified equality of the image point. -/
def localHomeomorphEquivAt (h : X ≃ₜ Y) (x : X) (y : Y) (hxy : h x = y) (n : ℕ) :
    LocalHomology x n ≃ₗ[ℤ] LocalHomology y n := by
  subst y
  exact localHomeomorphEquiv h x n

variable [T1Space X] [T1Space Y]

/-- The local isomorphism of an actual open partial homeomorphism. -/
def partialHomeomorphEquiv (e : OpenPartialHomeomorph X Y) (x : X) (hx : x ∈ e.source)
    (n : ℕ) : LocalHomology x n ≃ₗ[ℤ] LocalHomology (e x) n :=
  (((neighborhoodEquiv e.source e.open_source ⟨x, hx⟩ n).symm).trans
    (localHomeomorphEquiv e.toHomeomorphSourceTarget ⟨x, hx⟩ n)).trans
    (neighborhoodEquiv e.target e.open_target (e.toHomeomorphSourceTarget ⟨x, hx⟩) n)

/-- Before inversion of the source inclusion, the map is exactly the original chart's
source-target map followed by the target inclusion. -/
theorem partialHomeomorphEquiv_source (e : OpenPartialHomeomorph X Y) (x : X)
    (hx : x ∈ e.source) (n : ℕ) (a : LocalHomology (⟨x, hx⟩ : e.source) n) :
    partialHomeomorphEquiv e x hx n (neighborhoodMap e.source ⟨x, hx⟩ n a) =
      neighborhoodMap e.target (e.toHomeomorphSourceTarget ⟨x, hx⟩) n
        (localHomeomorphEquiv e.toHomeomorphSourceTarget ⟨x, hx⟩ n a) := by
  change neighborhoodEquiv e.target e.open_target _ n
    (localHomeomorphEquiv e.toHomeomorphSourceTarget ⟨x, hx⟩ n
      ((neighborhoodEquiv e.source e.open_source ⟨x, hx⟩ n).symm
        ((neighborhoodEquiv e.source e.open_source ⟨x, hx⟩ n) a))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

end NoExoticSixSphere.RelativeSingularHomology

namespace NoExoticSixSphere.RelativeSingularHomology

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Translation transports the local group at an arbitrary point to the computed origin. -/
def translateLocalEquiv (x : E) (n : ℕ) :
    LocalHomology x n ≃ₗ[ℤ] LocalHomology (0 : E) n :=
  localHomeomorphEquivAt (Homeomorph.subRight x) x 0 (sub_self x) n

end NoExoticSixSphere.RelativeSingularHomology

namespace NoExoticSixSphere.RelativeSingularHomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 1) + 1)]
  {M : Type} [TopologicalSpace M] [T1Space M]

/-- An actual Euclidean chart gives a marking of top local homology of the original space. -/
def chartLocalTopEquiv (e : OpenPartialHomeomorph M E) (x : M) (hx : x ∈ e.source) :
    LocalHomology x (n + 2) ≃ₗ[ℤ] ℤ :=
  ((partialHomeomorphEquiv e x hx (n + 2)).trans
    (translateLocalEquiv E (e x) (n + 2))).trans (localTopEquiv E n)

/-- The primitive local class represented through the specified actual chart. -/
def chartLocalTopClass (e : OpenPartialHomeomorph M E) (x : M) (hx : x ∈ e.source) :
    LocalHomology x (n + 2) := (chartLocalTopEquiv n e x hx).symm 1

theorem chartLocalTopEquiv_class (e : OpenPartialHomeomorph M E) (x : M)
    (hx : x ∈ e.source) :
    chartLocalTopEquiv n e x hx (chartLocalTopClass n e x hx) = 1 :=
  (chartLocalTopEquiv n e x hx).apply_symm_apply 1

/-- An overlap change can reverse the primitive integral class, but cannot rescale it
by any integer other than a unit. No orientation-preserving claim is made here. -/
theorem chartLocalTopClass_eq_or_neg (e f : OpenPartialHomeomorph M E) (x : M)
    (he : x ∈ e.source) (hf : x ∈ f.source) :
    chartLocalTopClass n e x he = chartLocalTopClass n f x hf ∨
      chartLocalTopClass n e x he = -chartLocalTopClass n f x hf := by
  let A := (chartLocalTopEquiv n e x he).symm.trans (chartLocalTopEquiv n f x hf)
  have h := IntLinearAutomorphism.apply_one_eq_one_or_neg_one A
  change chartLocalTopEquiv n f x hf (chartLocalTopClass n e x he) = 1 ∨
    chartLocalTopEquiv n f x hf (chartLocalTopClass n e x he) = -1 at h
  rcases h with h | h
  · left
    apply (chartLocalTopEquiv n f x hf).injective
    rw [h, chartLocalTopEquiv_class]
  · right
    apply (chartLocalTopEquiv n f x hf).injective
    rw [h, map_neg, chartLocalTopEquiv_class]

/-- The original space's other local groups of degree at least two vanish in the chart. -/
theorem chartLocalHomology_subsingleton (e : OpenPartialHomeomorph M E) (x : M)
    (hx : x ∈ e.source) (k : ℕ) (hk : k ≠ 0) (hkn : k ≠ n + 1) :
    Subsingleton (LocalHomology x (k + 1)) := by
  let := localHomology_subsingleton E n k hk hkn
  exact ((partialHomeomorphEquiv e x hx (k + 1)).trans
    (translateLocalEquiv E (e x) (k + 1))).injective.subsingleton

end NoExoticSixSphere.RelativeSingularHomology
