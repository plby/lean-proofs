import Wikipedia.NoExoticSixSphere.JamesSphereFirstStageHomologyRange

/-!
# The original James quotient preserves homology above its first sphere

In degrees above n+1, both neighboring homology groups of the actual
first-stage sphere vanish. The pair sequence identifies absolute with
relative homology. Naturality and the proved relative quotient theorem
then give bijectivity of the ORIGINAL quotient homology map.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.JamesSphere.FirstStageQuotient

theorem firstStage_toRelative_bijective (n k : ℕ) (hn : 0 < n) (hk : n < k) :
    Function.Bijective
      (RelativeSingularHomology.toRelative (James.stage (spherePole n) 1) (k + 1)) := by
  let : Subsingleton (SingularHomology (James.stage (spherePole n) 1) (k + 1)) :=
    subsingleton_singularHomology_of_homeomorph_sphere hn (by omega) (by omega)
      (FirstStage.homeomorph n).symm
  let : Subsingleton (SingularHomology (James.stage (spherePole n) 1) k) :=
    subsingleton_singularHomology_of_homeomorph_sphere hn (by omega) (by omega)
      (FirstStage.homeomorph n).symm
  constructor
  · apply LinearMap.ker_eq_bot.mp
    rw [← RelativeSingularHomology.exact_at_ambient]
    apply LinearMap.range_eq_bot.mpr
    ext c
    exact (congrArg (singularHomologyMap
      (subtypeInclusion (James.stage (spherePole n) 1)) (k + 1))
        (Subsingleton.elim c 0)).trans (map_zero _)
  · intro c
    have hc : c ∈ LinearMap.ker
        (RelativeSingularHomology.connecting (James.stage (spherePole n) 1) k) :=
      Subsingleton.elim _ _
    rw [← RelativeSingularHomology.exact_at_relative] at hc
    exact hc

theorem quotient_homology_bijective_above (n k : ℕ) (hn : 0 < n) (hk : n < k) :
    Function.Bijective (singularHomologyMap (quotientMap n) (k + 1)) := by
  have hs := RelativeSingularHomology.toRelative_naturality
    (quotientMap n) (quotientMap_mapsTo_point n) (k + 1)
  have hb := (quotient_relative_homology_bijective n (k + 1)).comp
    (firstStage_toRelative_bijective n k hn hk)
  change Function.Bijective ((RelativeSingularHomology.map
    (quotientMap n) (quotientMap_mapsTo_point n) (k + 1)).comp
      (RelativeSingularHomology.toRelative (James.stage (spherePole n) 1) (k + 1))) at hb
  rw [hs] at hb
  have he : k - 1 + 2 = k + 1 := by omega
  have ht := RelativeSingularHomology.contractibleSubspace_toRelative_bijective
    ({basepoint n} : Set (Space n)) (k - 1)
  rw [he] at ht
  exact (Function.Bijective.of_comp_iff' ht _).mp hb

def aboveHomologyEquiv (n k : ℕ) (hn : 0 < n) (hk : n < k) :
    SingularHomology (James.Space (Sphere n) (spherePole n)) (k + 1) ≃ₗ[ℤ]
      SingularHomology (Space n) (k + 1) :=
  LinearEquiv.ofBijective (singularHomologyMap (quotientMap n) (k + 1))
    (quotient_homology_bijective_above n k hn hk)

theorem aboveHomologyEquiv_apply (n k : ℕ) (hn : 0 < n) (hk : n < k)
    (c : SingularHomology (James.Space (Sphere n) (spherePole n)) (k + 1)) :
    aboveHomologyEquiv n k hn hk c = singularHomologyMap (quotientMap n) (k + 1) c := rfl

end NoExoticSixSphere.JamesSphere.FirstStageQuotient
