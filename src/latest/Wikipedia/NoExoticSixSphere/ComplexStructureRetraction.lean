import Wikipedia.NoExoticSixSphere.SkewPolarNormalization
import Wikipedia.NoExoticSixSphere.OrthogonalComplexStructures

/-!
# A neighborhood retraction onto orthogonal complex structures

The actual skew operator is divided by the smooth local square root of its
Gram operator. The domain is open and contains every orthogonal complex
structure. The normalization is the identity on that locus.
-/

open Set
open scoped ContDiff Ring

namespace NoExoticSixSphere.OrthogonalComplexStructures

open GLOrthonormalization CayleyTransform SkewSpectralPlane

variable {n : ℕ}

noncomputable def rootData (n : ℕ) :
    NearIdentitySquare.RootData (Vector n →L[ℝ] Vector n) :=
  Classical.choice NearIdentitySquare.nonempty_rootData

def normalizationDomain (n : ℕ) : Set (SkewOperators n) :=
  gram ⁻¹' (rootData n).domain

theorem gram_eq_neg_comp (K : SkewOperators n) : gram K =
    -((K : Vector n →L[ℝ] Vector n).comp (K : Vector n →L[ℝ] Vector n)) := by
  rw [gram, adjoint_eq_neg, ContinuousLinearMap.neg_comp]

theorem contDiff_gram : ContDiff ℝ ∞ (gram (n := n)) := by
  have hK : ContDiff ℝ ∞ (fun K : SkewOperators n ↦ (K : Vector n →L[ℝ] Vector n)) :=
    (skewAdjoint.submodule ℝ (Vector n →L[ℝ] Vector n)).subtypeL.contDiff
  have he : gram (n := n) = fun K : SkewOperators n ↦
      -((K : Vector n →L[ℝ] Vector n).comp (K : Vector n →L[ℝ] Vector n)) :=
    funext gram_eq_neg_comp
  rw [he]
  exact (hK.clm_comp hK).neg

theorem isOpen_normalizationDomain (n : ℕ) : IsOpen (normalizationDomain n) :=
  (rootData n).open_domain.preimage contDiff_gram.continuous

theorem mem_normalizationDomain (J : Space n) : J.1 ∈ normalizationDomain n := by
  change gram J.1 ∈ (rootData n).domain
  rw [gram_eq_one]
  exact (rootData n).one_mem

noncomputable def normalizationOperator (K : SkewOperators n) : Vector n →L[ℝ] Vector n :=
  NearIdentitySquare.normalize (rootData n) (K : Vector n →L[ℝ] Vector n)

theorem normalizationOperator_skew {K : SkewOperators n} (hK : K ∈ normalizationDomain n) :
    star (normalizationOperator K) = -normalizationOperator K :=
  NearIdentitySquare.normalize_skew (rootData n) K.property hK

theorem normalizationOperator_square {K : SkewOperators n} (hK : K ∈ normalizationDomain n) :
    (normalizationOperator K).comp (normalizationOperator K) = -(1 : Vector n →L[ℝ] Vector n) :=
  NearIdentitySquare.normalize_square (rootData n) K.property hK

theorem contDiffOn_normalizationOperator : ContDiffOn ℝ ∞ (normalizationOperator (n := n))
    (normalizationDomain n) := by
  intro K hK
  have hroot : ContDiffAt ℝ ∞ (fun K : SkewOperators n ↦ (rootData n).root (gram K)) K :=
    ((rootData n).smooth.contDiffAt ((rootData n).open_domain.mem_nhds hK)).comp K
      contDiff_gram.contDiffAt
  have hi : ContDiffAt ℝ ∞ Ring.inverse ((rootData n).root (gram K)) := by
    obtain ⟨u, hu⟩ := (rootData n).isUnit_root hK
    simpa only [hu] using (contDiffAt_ringInverse ℝ (n := ∞) u)
  have hinv := hi.comp K hroot
  have hinc : ContDiffAt ℝ ∞
      (fun L : SkewOperators n ↦ (L : Vector n →L[ℝ] Vector n)) K :=
    (skewAdjoint.submodule ℝ (Vector n →L[ℝ] Vector n)).subtypeL.contDiff.contDiffAt
  exact (hinc.mul hinv).contDiffWithinAt

noncomputable def neighborhoodRetraction (n : ℕ) : C(normalizationDomain n, Space n) where
  toFun K := ⟨⟨normalizationOperator K.1, normalizationOperator_skew K.2⟩,
    normalizationOperator_square K.2⟩
  continuous_toFun :=
    (contDiffOn_normalizationOperator.continuousOn.domRestrict.subtype_mk _).subtype_mk _

theorem normalizationOperator_of_complexStructure (J : Space n) :
    normalizationOperator J.1 = (J.1 : Vector n →L[ℝ] Vector n) :=
  NearIdentitySquare.normalize_of_gram_eq_one (rootData n) (gram_eq_one J)

theorem neighborhoodRetraction_eq_self (J : Space n) :
    neighborhoodRetraction n ⟨J.1, mem_normalizationDomain J⟩ = J := by
  apply Subtype.ext
  apply Subtype.ext
  exact normalizationOperator_of_complexStructure J

end NoExoticSixSphere.OrthogonalComplexStructures
