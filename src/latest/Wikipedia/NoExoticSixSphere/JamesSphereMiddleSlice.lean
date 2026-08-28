import Wikipedia.NoExoticSixSphere.JamesSphereSuspensionQuotient
import Wikipedia.NoExoticSixSphere.EndingPathEmbedding
import Wikipedia.NoExoticSixSphere.HomotopyFiberNullhomotopyCoordinates
import Wikipedia.NoExoticSixSphere.SpherePathCover

/-!
# The actual middle slice of the sphere-loop evaluation

The middle slice is a closed embedded copy of the original sphere. The
remaining half of each generator gives its specified nullhomotopy. The
actual inverse image under path evaluation is therefore homotopy equivalent
to the sphere times the native loop space. Two distinct interior points on
one generator also give a concrete punctured-sphere path cover.
-/

noncomputable section

open scoped unitInterval ContinuousMap
open Wikipedia.HopfProblem.SingularMayerVietoris

namespace NoExoticSixSphere.JamesSphere

def middleTime : I := ⟨1 / 2, by constructor <;> norm_num⟩

def lowerTime : I := ⟨1 / 4, by constructor <;> norm_num⟩

def upperTime : I := ⟨3 / 4, by constructor <;> norm_num⟩

def middle (n : ℕ) : C(Sphere n, Sphere (n + 1)) := timeSlice n middleTime

theorem middle_isClosedEmbedding (n : ℕ) : Topology.IsClosedEmbedding (middle n) :=
  timeSlice_isClosedEmbedding n middleTime (by norm_num [middleTime])
    (by norm_num [middleTime])

def middleNullhomotopy (n : ℕ) : (middle n).HomotopyRel
    (ContinuousMap.const _ (spherePole (n + 1))) {spherePole n} where
  toFun p := loopEvaluation n (p.2, Set.Icc.convexComb middleTime 1 p.1)
  continuous_toFun := (loopEvaluation n).continuous.comp
    (continuous_snd.prodMk ((Set.Icc.continuous_convexComb middleTime 1).comp continuous_fst))
  map_zero_left x := by rw [Set.Icc.convexComb_zero]; rfl
  map_one_left x := by rw [Set.Icc.convexComb_one]; exact loopEvaluation_one n x
  prop' s x hx := by
    have he : x = spherePole n := hx
    subst x
    change loopEvaluation n (spherePole n, _) = middle n (spherePole n)
    exact (loopEvaluation_pole n _).trans (loopEvaluation_pole n middleTime).symm

def middlePathEquiv (n : ℕ) :
    EndingPath.restriction (spherePole (n + 1)) (Set.range (middle n)) ≃ₕ
      Sphere n × Path (spherePole (n + 1)) (spherePole (n + 1)) :=
  (EndingPath.embeddingFiberHomeomorph (middle n) (middle_isClosedEmbedding n).isEmbedding
    (spherePole (n + 1))).symm.toHomotopyEquiv.trans
      (HomotopyFiberHomotopyInvariance.nullhomotopyEquiv (middle n) (spherePole (n + 1))
        (middleNullhomotopy n).toHomotopy)

theorem middlePathEquiv_symm_curve (n : ℕ) (x : Sphere n)
    (p : Path (spherePole (n + 1)) (spherePole (n + 1))) :
    ((middlePathEquiv n).symm (x, p)).val.val =
      (((middleNullhomotopy n).toHomotopy.evalAt x).trans p).toContinuousMap := by
  apply ContinuousMap.ext
  intro t
  exact HomotopyFiberHomotopyInvariance.nullhomotopyEquiv_symm_path (middle n)
    (spherePole (n + 1)) (middleNullhomotopy n).toHomotopy x p t

theorem middlePathEquiv_symm_source (n : ℕ) (x : Sphere n)
    (p : Path (spherePole (n + 1)) (spherePole (n + 1))) :
    EndingPath.source (spherePole (n + 1)) ((middlePathEquiv n).symm (x, p)).val = middle n x := by
  change ((middlePathEquiv n).symm (x, p)).val.val 0 = _
  rw [middlePathEquiv_symm_curve]
  exact Path.source _

def lowerPuncture (n : ℕ) : Sphere (n + 1) :=
  loopEvaluation n (-spherePole n, lowerTime)

def upperPuncture (n : ℕ) : Sphere (n + 1) :=
  loopEvaluation n (-spherePole n, upperTime)

theorem lowerPuncture_ne_pole (n : ℕ) : lowerPuncture n ≠ spherePole (n + 1) :=
  loopEvaluation_ne_pole n (SpherePoleCompactification.ne_neg (spherePole n)).symm lowerTime
    (by norm_num [lowerTime]) (by norm_num [lowerTime])

theorem upperPuncture_ne_pole (n : ℕ) : upperPuncture n ≠ spherePole (n + 1) :=
  loopEvaluation_ne_pole n (SpherePoleCompactification.ne_neg (spherePole n)).symm upperTime
    (by norm_num [upperTime]) (by norm_num [upperTime])

theorem punctures_ne (n : ℕ) : lowerPuncture n ≠ upperPuncture n := by
  intro he
  have ht := loopEvaluation_time_injective n
    (SpherePoleCompactification.ne_neg (spherePole n)).symm
    (by norm_num [lowerTime]) (by norm_num [lowerTime]) he
  have hv := congrArg Subtype.val ht
  norm_num [lowerTime, upperTime] at hv

def punctureCoverHomologyEquiv (n k : ℕ) (hk : k ≠ 0) :
    SingularHomology
      (EndingPath.restriction (spherePole (n + 1)) {lowerPuncture n}ᶜ ∩
        EndingPath.restriction (spherePole (n + 1)) {upperPuncture n}ᶜ :
          Set (EndingPath.Space (spherePole (n + 1)))) k ≃ₗ[ℤ]
      (SingularHomology
        (Path (spherePole (n + 1)) (spherePole (n + 1))) k ×
      SingularHomology
        (Path (spherePole (n + 1)) (spherePole (n + 1))) k) :=
  SpherePathCover.homologyEquiv (lowerPuncture n) (upperPuncture n) (spherePole (n + 1))
    (punctures_ne n) (lowerPuncture_ne_pole n).symm (upperPuncture_ne_pole n).symm k hk

end NoExoticSixSphere.JamesSphere
