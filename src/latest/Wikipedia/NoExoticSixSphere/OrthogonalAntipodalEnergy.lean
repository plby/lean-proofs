import Wikipedia.NoExoticSixSphere.SphereCurveEnergy
import Wikipedia.NoExoticSixSphere.OrthogonalPathEnergy

/-!
# Minimum-energy lower bound for all smooth antipodal orthogonal paths

Each column of an orthogonal path is an actual unit-sphere curve. Summing
the sphere-curve bounds gives the lower bound `n π²` for the original
Hilbert--Schmidt path energy, without assuming the path is exponential.
-/

open scoped ContDiff

namespace NoExoticSixSphere.OrthogonalPathEnergy

open GLOrthonormalization HilbertSchmidt

variable {n : ℕ}

theorem deriv_apply_const {A : ℝ → Vector n →L[ℝ] Vector n}
    (hA : ContDiff ℝ ∞ A) (x : Vector n) (t : ℝ) :
    deriv (fun s ↦ A s x) t = deriv A t x := by
  have hd := (((hA.differentiable (by simp)) t).hasDerivAt).clm_apply (hasDerivAt_const t x)
  simpa only [map_zero, add_zero] using! hd.deriv

theorem energy_eq_column_sum {A : ℝ → Vector n →L[ℝ] Vector n}
    (hA : ContDiff ℝ ∞ A) (l u : ℝ) :
    energy A l u = ∑ i : Fin n,
      ∫ t : ℝ in l..u, ‖deriv A t (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ^ 2 := by
  unfold energy
  simp_rw [squareNorm_eq_sum]
  apply intervalIntegral.integral_finsetSum
  intro i _
  have hc : Continuous (fun t ↦
      ‖deriv A t (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ^ 2) :=
    ((ContDiff.deriv' (n := ∞) hA).continuous.clm_apply continuous_const).norm.pow 2
  exact hc.intervalIntegrable l u

theorem antipodal_energy_ge {γ : ℝ → OrthogonalOperators n}
    (hγ : ContDiff ℝ ∞ (fun t ↦ (γ t).1.1))
    (hend : (γ 1).1.1 = -(γ 0).1.1) :
    (n : ℝ) * Real.pi ^ 2 ≤ energy (fun t ↦ (γ t).1.1) 0 1 := by
  rw [energy_eq_column_sum hγ]
  have hi (i : Fin n) : Real.pi ^ 2 ≤
      ∫ t : ℝ in 0..1, ‖deriv (fun s ↦ (γ s).1.1) t
        (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ^ 2 := by
    let e := EuclideanSpace.basisFun (Fin n) ℝ i
    have hcol : ContDiff ℝ ∞ (fun t ↦ (γ t).1.1 e) := hγ.clm_apply contDiff_const
    have hn (t : ℝ) : ‖(γ t).1.1 e‖ = 1 :=
      ((γ t).2 e).trans ((EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one i)
    have he : (γ 1).1.1 e = -(γ 0).1.1 e := DFunLike.congr_fun hend e
    have hb := SphereCurveAngle.antipodal_energy_ge hcol hn he
    simpa only [deriv_apply_const hγ] using hb
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hi i)
  simpa using hs

theorem energy_congr_Icc {A B : ℝ → Vector n →L[ℝ] Vector n}
    {l u : ℝ} (hlu : l ≤ u) (h : Set.EqOn A B (Set.Icc l u)) :
    energy A l u = energy B l u := by
  apply intervalIntegral.integral_congr_Ioo_of_le hlu
  intro t ht
  have he : A =ᶠ[nhds t] B := Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht)
    (fun s hs ↦ h ⟨hs.1.le, hs.2.le⟩)
  exact congrArg squareNorm he.deriv_eq

end NoExoticSixSphere.OrthogonalPathEnergy
