import Wikipedia.HopfProblem.OrbitPairSphereLocalEnergy

/-!
# Squared spherical angle on every nonantipodal pair

Off the diagonal the ordinary arccos derivative applies. On the diagonal,
the previously constructed native smooth logarithm supplies smoothness.
Together these give a canonical smooth energy domain: all nonantipodal
pairs of points in the original round sphere.
-/

noncomputable section

open scoped ContDiff Manifold
open Set

namespace Wikipedia.HopfProblem.OrbitPair.SpherePairedGeodesic

open NoExoticSixSphere GLOrthonormalization

def nonantipodal (n : ℕ) : Set (Sphere n × Sphere n) :=
  {p | -1 < inner ℝ p.1.val p.2.val}

theorem isOpen_nonantipodal (n : ℕ) : IsOpen (nonantipodal n) := by
  apply isOpen_lt continuous_const
  exact (continuous_subtype_val.comp continuous_fst).inner
    (continuous_subtype_val.comp continuous_snd)

theorem diagonal_mem_nonantipodal {n : ℕ} (x : Sphere n) :
    (x, x) ∈ nonantipodal n := by
  change -1 < inner ℝ x.val x.val
  rw [real_inner_self_eq_norm_sq, ClosedHemisphere.unit_norm x]
  norm_num

theorem sphereCost_diagonal {n : ℕ} (x : Sphere n) : sphereCost n (x, x) = 0 := by
  simp only [sphereCost, real_inner_self_eq_norm_sq, ClosedHemisphere.unit_norm x,
    one_pow, Real.arccos_one, zero_pow (show (2 : ℕ) ≠ 0 by decide)]

theorem sphereCost_nonneg {n : ℕ} (p : Sphere n × Sphere n) :
    0 ≤ sphereCost n p := sq_nonneg _

theorem contMDiff_inner_sphere (n : ℕ) :
    ContMDiff ((𝓡 n).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : Sphere n × Sphere n => inner ℝ p.1.val p.2.val) := by
  letI : Fact (Module.finrank ℝ (Vector (n + 1)) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hcoe : ContMDiff (𝓡 n) 𝓘(ℝ, Vector (n + 1)) ∞
      (fun p : Sphere n => p.val) := contMDiff_coe_sphere
  have hv : ContMDiff ((𝓡 n).prod (𝓡 n))
      𝓘(ℝ, Vector (n + 1) × Vector (n + 1)) ∞
      (fun p : Sphere n × Sphere n => (p.1.val, p.2.val)) :=
    (hcoe.comp contMDiff_fst).prodMk_space (hcoe.comp contMDiff_snd)
  have hi : ContDiff ℝ ∞
      (fun p : Vector (n + 1) × Vector (n + 1) => inner ℝ p.1 p.2) :=
    contDiff_fst.inner ℝ contDiff_snd
  exact hi.contMDiff.comp hv

theorem contMDiffAt_sphereCost_of_nonantipodal {n : ℕ}
    (p : Sphere n × Sphere n) (hp : p ∈ nonantipodal n) :
    ContMDiffAt ((𝓡 n).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ (sphereCost n) p := by
  by_cases he : p.1 = p.2
  · obtain ⟨U, hU, hmem, hs⟩ := exists_smooth_cost_near_diagonal n p.1
    have hpair : p = (p.1, p.1) := Prod.ext rfl he.symm
    have hpU : p ∈ U := by rw [hpair]; exact hmem
    exact hs.contMDiffAt (hU.mem_nhds hpU)
  · have hne : p.1.val ≠ p.2.val := fun h => he (Subtype.ext h)
    have hlt : inner ℝ p.1.val p.2.val < 1 :=
      (inner_lt_one_iff_real_of_norm_eq_one (ClosedHemisphere.unit_norm p.1)
        (ClosedHemisphere.unit_norm p.2)).mpr hne
    have ha : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Real.arccos
        (inner ℝ p.1.val p.2.val) :=
      (Real.contDiffAt_arccos (ne_of_gt hp) (ne_of_lt hlt)).contMDiffAt
    exact (ContMDiffAt.comp
      (g := Real.arccos) (f := fun q : Sphere n × Sphere n => inner ℝ q.1.val q.2.val)
      p ha (contMDiff_inner_sphere n).contMDiffAt).pow 2

theorem contMDiffOn_sphereCost_nonantipodal (n : ℕ) :
    ContMDiffOn ((𝓡 n).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (sphereCost n) (nonantipodal n) :=
  fun p hp => (contMDiffAt_sphereCost_of_nonantipodal p hp).contMDiffWithinAt

theorem mem_nonantipodal_of_cost_lt_pi_sq {n : ℕ} (p : Sphere n × Sphere n)
    (hp : sphereCost n p < Real.pi ^ 2) : p ∈ nonantipodal n := by
  have ha := Real.arccos_nonneg (inner ℝ p.1.val p.2.val)
  have hlt : Real.arccos (inner ℝ p.1.val p.2.val) < Real.pi := by
    change Real.arccos (inner ℝ p.1.val p.2.val) ^ 2 < Real.pi ^ 2 at hp
    nlinarith [Real.pi_pos]
  exact Real.arccos_lt_pi.mp hlt

end Wikipedia.HopfProblem.OrbitPair.SpherePairedGeodesic
