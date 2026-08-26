import ErdosProblems.Erdos941.SphereBaseChange
import ErdosProblems.Erdos941.RationalSphereIntegrality

/- Adapted from the checked orbit comparison in Erdos1148/GlobalToLocal.lean. -/

/-!
# Comparing global and local pair orbits

Uniqueness of a rational transporter identifies it with every local integral
transporter. Entrywise p-adic integrality then gives an integral transporter.
-/

namespace Erdos941

open PairLocal

lemma rational_local_transporter_eq (r : ℕ) [Fact r.Prime] {d ℓ : ℤ}
    (src dst : SpherePair ℤ d ℓ) (hnd : ℓ ^ 2 ≠ d ^ 2)
    (g : sphereSpecialGroup ℚ) (k : sphereSpecialGroup (PadicInt r))
    (hg : g • mapSpherePair (Int.castRingHom ℚ) src = mapSpherePair (Int.castRingHom ℚ) dst)
    (hk : k • mapSpherePair (Int.castRingHom (PadicInt r)) src =
      mapSpherePair (Int.castRingHom (PadicInt r)) dst) :
    sphereSpecialBaseChange (algebraMap ℚ (Padic r)) g =
      sphereSpecialBaseChange (algebraMap (PadicInt r) (Padic r)) k := by
  let pair := mapSpherePair (Int.castRingHom (Padic r)) src
  have hndK : ((ℓ : Padic r)) ^ 2 ≠ (d : Padic r) ^ 2 :=
    map_sphere_nondegenerate (Int.castRingHom (Padic r)) Int.cast_injective hnd
  apply sphereSpecialGroup_ext_of_pair pair hndK
  · have hq := sphereSpecialBaseChange_intCast_action (algebraMap ℚ (Padic r)) g src.1.1 dst.1.1
      (congrArg (fun x : SpherePair ℚ d ℓ => x.1.1) hg)
    have hp := sphereSpecialBaseChange_intCast_action (algebraMap (PadicInt r) (Padic r))
      k src.1.1 dst.1.1 (congrArg (fun x : SpherePair (PadicInt r) d ℓ => x.1.1) hk)
    exact hq.trans hp.symm
  · have hq := sphereSpecialBaseChange_intCast_action (algebraMap ℚ (Padic r)) g src.1.2 dst.1.2
      (congrArg (fun x : SpherePair ℚ d ℓ => x.1.2) hg)
    have hp := sphereSpecialBaseChange_intCast_action (algebraMap (PadicInt r) (Padic r))
      k src.1.2 dst.1.2 (congrArg (fun x : SpherePair (PadicInt r) d ℓ => x.1.2) hk)
    exact hq.trans hp.symm

lemma sphere_matrix_column_norm (g : sphereSpecialGroup ℚ) (j : Fin 3) :
    normThree (matrixOfCoeffMap g.1.toLinearMap 0 j,
      matrixOfCoeffMap g.1.toLinearMap 1 j, matrixOfCoeffMap g.1.toLinearMap 2 j) = 1 := by
  have h0 := g.2.1 (1, 0, 0)
  have h1 := g.2.1 (0, 1, 0)
  have h2 := g.2.1 (0, 0, 1)
  have hmap (v : ℚ × ℚ × ℚ) : g.1 v = coeffMatrixMap (matrixOfCoeffMap g.1.toLinearMap) v := by
    rw [coeffMatrixMap_matrixOfCoeffMap]; rfl
  rw [hmap] at h0 h1 h2
  simp [coeffMatrixMap, coeffVecEquiv_apply, coeffVecEquiv_symm_apply,
    Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, normThree] at h0 h1 h2
  fin_cases j
  · exact h0
  · exact h1
  · exact h2

lemma exists_integer_matrix_of_local_transporters {d ℓ : ℤ}
    (src dst : SpherePair ℤ d ℓ) (hnd : ℓ ^ 2 ≠ d ^ 2) (g : sphereSpecialGroup ℚ)
    (hg : g • mapSpherePair (Int.castRingHom ℚ) src = mapSpherePair (Int.castRingHom ℚ) dst)
    (hloc : ∀ (r : ℕ) [Fact r.Prime], r ≠ 2 → ∃ k : sphereSpecialGroup (PadicInt r),
      k • mapSpherePair (Int.castRingHom (PadicInt r)) src =
        mapSpherePair (Int.castRingHom (PadicInt r)) dst) :
    ∃ M : Matrix (Fin 3) (Fin 3) ℤ,
      M.map (Int.castRingHom ℚ) = matrixOfCoeffMap g.1.toLinearMap := by
  have hlocal (i j : Fin 3) (r : ℕ) [Fact r.Prime] (hr2 : r ≠ 2) :
      ∃ z : PadicInt r, (z : Padic r) = ((matrixOfCoeffMap g.1.toLinearMap i j : ℚ) : Padic r) := by
    obtain ⟨k, hk⟩ := hloc r hr2
    have heq := rational_local_transporter_eq r src dst hnd g k hg hk
    have hm := congrArg
      (fun u : sphereSpecialGroup (Padic r) => matrixOfCoeffMap u.1.toLinearMap) heq
    rw [matrix_sphereSpecialBaseChange, matrix_sphereSpecialBaseChange] at hm
    refine ⟨matrixOfCoeffMap k.1.toLinearMap i j, ?_⟩
    exact (congrArg (fun M => M i j) hm).symm
  have hentry (i j : Fin 3) : ∃ a : ℤ, (a : ℚ) = matrixOfCoeffMap g.1.toLinearMap i j := by
    obtain ⟨a, b, c, ha, hb, hc⟩ := rational_norm_one_integral_of_odd_local
      (matrixOfCoeffMap g.1.toLinearMap 0 j, matrixOfCoeffMap g.1.toLinearMap 1 j,
        matrixOfCoeffMap g.1.toLinearMap 2 j) (sphere_matrix_column_norm g j)
      (hlocal 0 j) (hlocal 1 j) (hlocal 2 j)
    fin_cases i
    · exact ⟨a, ha⟩
    · exact ⟨b, hb⟩
    · exact ⟨c, hc⟩
  choose M hM using hentry
  exact ⟨M, funext fun i => funext fun j => hM i j⟩

lemma exists_integer_sphereSpecialGroup (g : sphereSpecialGroup ℚ)
    (M : Matrix (Fin 3) (Fin 3) ℤ)
    (hM : M.map (Int.castRingHom ℚ) = matrixOfCoeffMap g.1.toLinearMap) :
    ∃ k : sphereSpecialGroup ℤ, sphereSpecialBaseChange (Int.castRingHom ℚ) k = g := by
  have hdet : M.det = 1 := by
    have h : (M.det : ℚ) = 1 := calc
      _ = (M.map (Int.castRingHom ℚ)).det := (Int.castRingHom ℚ).map_det M
      _ = (matrixOfCoeffMap g.1.toLinearMap).det := congrArg Matrix.det hM
      _ = 1 := by rw [det_matrixOfCoeffMap, g.2.2]
    exact_mod_cast h
  have hunit : IsUnit M.det := by rw [hdet]; exact isUnit_one
  have hpres : ∀ t, normThree (coeffMatrixMap M t) = normThree t := by
    apply normThree_preserved_of_matrix_map (Int.castRingHom ℚ) Int.cast_injective M
    rw [hM]
    intro t
    rw [coeffMatrixMap_matrixOfCoeffMap]
    exact g.2.1 t
  let k : sphereSpecialGroup ℤ := ⟨coeffMatrixEquiv M hunit, ⟨by
    intro t
    rw [coeffMatrixEquiv_apply]
    exact hpres t, by rw [coeffMatrixEquiv_toLinearMap, det_coeffMatrixMap, hdet]⟩⟩
  refine ⟨k, ?_⟩
  apply sphereSpecialGroup_matrix_injective
  dsimp only
  rw [matrix_sphereSpecialBaseChange]
  change (matrixOfCoeffMap (coeffMatrixEquiv M hunit).toLinearMap).map (Int.castRingHom ℚ) = _
  rw [coeffMatrixEquiv_toLinearMap, matrixOfCoeffMap_coeffMatrixMap, hM]

theorem integer_pairOrbit_eq_of_local_eq {d ℓ : ℤ} (src dst : SpherePair ℤ d ℓ)
    (hnd : ℓ ^ 2 ≠ d ^ 2)
    (hloc : ∀ (r : ℕ) [Fact r.Prime], r ≠ 2 →
      (Quotient.mk _ (mapSpherePair (Int.castRingHom (PadicInt r)) src) :
          SpherePairOrbits (PadicInt r) d ℓ) =
        Quotient.mk _ (mapSpherePair (Int.castRingHom (PadicInt r)) dst)) :
    (Quotient.mk _ src : SpherePairOrbits ℤ d ℓ) = Quotient.mk _ dst := by
  have hndQ := map_sphere_nondegenerate (Int.castRingHom ℚ) Int.cast_injective hnd
  obtain ⟨g, hfirst, hsecond⟩ := exists_sphere_transporter
    (mapSpherePair (Int.castRingHom ℚ) dst) (mapSpherePair (Int.castRingHom ℚ) src) hndQ
  have hg : g • mapSpherePair (Int.castRingHom ℚ) dst = mapSpherePair (Int.castRingHom ℚ) src := by
    apply Subtype.ext
    exact Prod.ext hfirst hsecond
  have htransport : ∀ (r : ℕ) [Fact r.Prime], r ≠ 2 → ∃ k : sphereSpecialGroup (PadicInt r),
      k • mapSpherePair (Int.castRingHom (PadicInt r)) dst =
        mapSpherePair (Int.castRingHom (PadicInt r)) src := by
    intro r hr hr2
    exact MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp (Quotient.exact (hloc r hr2)))
  obtain ⟨M, hM⟩ := exists_integer_matrix_of_local_transporters dst src hnd g hg htransport
  obtain ⟨k, hk⟩ := exists_integer_sphereSpecialGroup g M hM
  have hks : k • dst = src := by
    apply mapSpherePair_injective (Int.castRingHom ℚ) Int.cast_injective
    rw [mapSpherePair_smul, hk, hg]
  exact Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨k, hks⟩))

end Erdos941
