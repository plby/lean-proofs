import Wikipedia.HomotopyGroupsOfSpheres.SelfAdjointPolarNormalization
import Wikipedia.HomotopyGroupsOfSpheres.BalancedRealClassification

/-!
# A continuous neighborhood retraction onto balanced real involutions

Local polar normalization of a symmetric matrix is a symmetric involution.
Its trace is an integer. Restricting to the open set where the normalized
trace has absolute value less than one therefore selects the balanced
component, without assuming that normalization preserves arbitrary traces.
-/

noncomputable section

open scoped Matrix.Norms.L2Operator ContDiff Ring
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres

namespace RealUnitaryMatrices

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem symmetric_involution_trace_integer (A : Matrix N N ℝ)
    (hsym : A.transpose = A) (hsq : A * A = 1) : ∃ z : ℤ, (z : ℝ) = A.trace := by
  obtain ⟨_, μ, hμ, _, htr⟩ := symmetric_involution_diagonalization A hsym hsq
  have hm (i : N) : ∃ z : ℤ, (z : ℝ) = μ i := by
    rcases hμ i with hi | hi
    · exact ⟨1, by simpa only [Int.cast_one] using hi.symm⟩
    · exact ⟨-1, by simpa only [Int.cast_neg, Int.cast_one] using hi.symm⟩
  choose z hz using hm
  refine ⟨∑ i, z i, ?_⟩
  rw [Int.cast_sum, htr]
  exact Finset.sum_congr rfl (fun i _ ↦ hz i)

theorem symmetric_involution_trace_zero_of_small (A : Matrix N N ℝ)
    (hsym : A.transpose = A) (hsq : A * A = 1) (hsmall : |A.trace| < 1) : A.trace = 0 := by
  obtain ⟨z, hz⟩ := symmetric_involution_trace_integer A hsym hsq
  have hr : |(z : ℝ)| < 1 := by rwa [hz]
  have hi : |z| < 1 := by exact_mod_cast hr
  have hz' : (-1 : ℤ) < z ∧ z < 1 := abs_lt.mp hi
  have hzero : z = 0 := by omega
  rw [← hz, hzero, Int.cast_zero]

end RealUnitaryMatrices

namespace BalancedRealInvolutions

open NoExoticSixSphere.NearIdentitySquare RealUnitaryMatrices

def rootData (n : ℕ) : RootData (Matrix (Index n) (Index n) ℝ) :=
  Classical.choice nonempty_rootData

def gramDomain (n : ℕ) : Set (Matrix (Index n) (Index n) ℝ) :=
  {A | star A * A ∈ (rootData n).domain}

theorem isOpen_gramDomain (n : ℕ) : IsOpen (gramDomain n) :=
  (rootData n).open_domain.preimage (continuous_star.mul continuous_id)

def normalizationMatrix {n : ℕ} (A : Matrix (Index n) (Index n) ℝ) :
    Matrix (Index n) (Index n) ℝ := normalize (rootData n) A

theorem contDiffOn_normalizationMatrix (n : ℕ) :
    ContDiffOn ℝ ∞ (normalizationMatrix (n := n)) (gramDomain n) := by
  intro A hA
  have hstar : ContDiff ℝ ∞ (star : Matrix (Index n) (Index n) ℝ → _) :=
    (starL ℝ).contDiff
  have hg : ContDiff ℝ ∞ (fun A : Matrix (Index n) (Index n) ℝ ↦ star A * A) :=
    hstar.mul contDiff_id
  have hr : ContDiffAt ℝ ∞ (fun B : Matrix (Index n) (Index n) ℝ ↦
      (rootData n).root (star B * B)) A :=
    ((rootData n).smooth.contDiffAt ((rootData n).open_domain.mem_nhds hA)).comp
      (f := fun B : Matrix (Index n) (Index n) ℝ ↦ star B * B) A hg.contDiffAt
  have hi : ContDiffAt ℝ ∞ Ring.inverse ((rootData n).root (star A * A)) := by
    obtain ⟨u, hu⟩ := (rootData n).isUnit_root hA
    simpa only [hu] using (contDiffAt_ringInverse ℝ (n := ∞) u)
  exact (contDiffAt_id.mul (hi.comp A hr)).contDiffWithinAt

theorem normalizationMatrix_transpose {n : ℕ} {A : Matrix (Index n) (Index n) ℝ}
    (hsym : A.transpose = A) (hA : A ∈ gramDomain n) :
    (normalizationMatrix A).transpose = normalizationMatrix A := by
  have hk : star A = A := by rwa [star_eq_transpose]
  simpa only [star_eq_transpose, normalizationMatrix] using!
    SelfAdjointPolarNormalization.normalize_selfAdjoint (rootData n) hk hA

theorem normalizationMatrix_square {n : ℕ} {A : Matrix (Index n) (Index n) ℝ}
    (hsym : A.transpose = A) (hA : A ∈ gramDomain n) :
    normalizationMatrix A * normalizationMatrix A = 1 := by
  have hk : star A = A := by rwa [star_eq_transpose]
  exact SelfAdjointPolarNormalization.normalize_square (rootData n) hk hA

def normalizationDomain (n : ℕ) : Set (Matrix (Index n) (Index n) ℝ) :=
  gramDomain n ∩ (fun A ↦ (normalizationMatrix A).trace) ⁻¹' Ioo (-1) 1

theorem isOpen_normalizationDomain (n : ℕ) : IsOpen (normalizationDomain n) := by
  have ht : Continuous (Matrix.trace : Matrix (Index n) (Index n) ℝ → ℝ) := by
    unfold Matrix.trace
    fun_prop
  exact (ht.comp_continuousOn
    (contDiffOn_normalizationMatrix n).continuousOn).isOpen_inter_preimage
    (isOpen_gramDomain n) isOpen_Ioo

theorem normalizationMatrix_mem_locus {n : ℕ} {A : Matrix (Index n) (Index n) ℝ}
    (hsym : A.transpose = A) (hA : A ∈ normalizationDomain n) :
    normalizationMatrix A ∈ locus n := by
  have ht := normalizationMatrix_transpose hsym hA.1
  have hs := normalizationMatrix_square hsym hA.1
  exact mem_locus_of_relations n _ ht hs
    (symmetric_involution_trace_zero_of_small _ ht hs (abs_lt.mpr hA.2))

theorem normalizationMatrix_of_involution {n : ℕ} (J : Space n) :
    normalizationMatrix J.val = J.val := by
  apply normalize_of_gram_eq_one
  rw [star_eq_transpose, transpose_eq, square_eq]

theorem mem_normalizationDomain {n : ℕ} (J : Space n) : J.val ∈ normalizationDomain n := by
  constructor
  · change star J.val * J.val ∈ (rootData n).domain
    rw [star_eq_transpose, transpose_eq, square_eq]
    exact (rootData n).one_mem
  · change (normalizationMatrix J.val).trace ∈ Ioo (-1 : ℝ) 1
    rw [normalizationMatrix_of_involution, trace_eq_zero]
    constructor <;> norm_num

def neighborhoodRetraction (n : ℕ) :
    C({A : Matrix (Index n) (Index n) ℝ | A.transpose = A ∧ A ∈ normalizationDomain n},
      Space n) where
  toFun A := ⟨normalizationMatrix A.val, normalizationMatrix_mem_locus A.property.1 A.property.2⟩
  continuous_toFun := ((contDiffOn_normalizationMatrix n).continuousOn.mono
    (fun _ h ↦ h.2.1)).domRestrict.subtype_mk _

theorem neighborhoodRetraction_eq_self {n : ℕ} (J : Space n) :
    neighborhoodRetraction n ⟨J.val, transpose_eq J, mem_normalizationDomain J⟩ = J :=
  Subtype.ext (normalizationMatrix_of_involution J)

end BalancedRealInvolutions
end Wikipedia.HomotopyGroupsOfSpheres
