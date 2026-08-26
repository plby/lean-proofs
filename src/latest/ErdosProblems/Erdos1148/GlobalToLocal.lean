import ErdosProblems.Erdos1148.BaseChange
import ErdosProblems.Erdos1148.RationalIntegrality

/-!
# Comparing global and local pair orbits

Uniqueness of a rational transporter identifies it with every local integral
transporter. Entrywise p-adic integrality then gives an integral transporter.
-/

namespace Erdos1148.DukeArithmetic

lemma rational_local_transporter_eq (r : ℕ) [Fact r.Prime] {d ℓ : ℤ}
    (src dst : FormPair ℤ d ℓ) (hnd : ℓ ^ 2 ≠ 4 * d ^ 2)
    (g : specialDiscrGroup ℚ) (k : specialDiscrGroup (PadicInt r))
    (hg : g • mapFormPair (Int.castRingHom ℚ) src = mapFormPair (Int.castRingHom ℚ) dst)
    (hk : k • mapFormPair (Int.castRingHom (PadicInt r)) src =
      mapFormPair (Int.castRingHom (PadicInt r)) dst) :
    specialDiscrBaseChange (algebraMap ℚ (Padic r)) g =
      specialDiscrBaseChange (algebraMap (PadicInt r) (Padic r)) k := by
  let pair := mapFormPair (Int.castRingHom (Padic r)) src
  have hndK : ((ℓ : Padic r)) ^ 2 ≠ 4 * (d : Padic r) ^ 2 :=
    map_nondegenerate (Int.castRingHom (Padic r)) Int.cast_injective hnd
  apply specialDiscrGroup_ext_of_pair pair hndK
  · have hq := specialDiscrBaseChange_intCast_action (algebraMap ℚ (Padic r)) g src.1.1 dst.1.1
      (congrArg (fun x : FormPair ℚ d ℓ => x.1.1) hg)
    have hp := specialDiscrBaseChange_intCast_action (algebraMap (PadicInt r) (Padic r))
      k src.1.1 dst.1.1 (congrArg (fun x : FormPair (PadicInt r) d ℓ => x.1.1) hk)
    exact hq.trans hp.symm
  · have hq := specialDiscrBaseChange_intCast_action (algebraMap ℚ (Padic r)) g src.1.2 dst.1.2
      (congrArg (fun x : FormPair ℚ d ℓ => x.1.2) hg)
    have hp := specialDiscrBaseChange_intCast_action (algebraMap (PadicInt r) (Padic r))
      k src.1.2 dst.1.2 (congrArg (fun x : FormPair (PadicInt r) d ℓ => x.1.2) hk)
    exact hq.trans hp.symm

lemma exists_integer_matrix_of_local_transporters {d ℓ : ℤ}
    (src dst : FormPair ℤ d ℓ) (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) (g : specialDiscrGroup ℚ)
    (hg : g • mapFormPair (Int.castRingHom ℚ) src = mapFormPair (Int.castRingHom ℚ) dst)
    (hloc : ∀ (r : ℕ) [Fact r.Prime], ∃ k : specialDiscrGroup (PadicInt r),
      k • mapFormPair (Int.castRingHom (PadicInt r)) src =
        mapFormPair (Int.castRingHom (PadicInt r)) dst) :
    ∃ M : Matrix (Fin 3) (Fin 3) ℤ,
      M.map (Int.castRingHom ℚ) = matrixOfCoeffMap g.1.toLinearMap := by
  have hentry (i j : Fin 3) : ∃ a : ℤ, (a : ℚ) = matrixOfCoeffMap g.1.toLinearMap i j := by
    apply exists_int_of_forall_padic_integral
    intro r hr
    obtain ⟨k, hk⟩ := hloc r
    have heq := rational_local_transporter_eq r src dst hnd g k hg hk
    have hm := congrArg
      (fun u : specialDiscrGroup (Padic r) => matrixOfCoeffMap u.1.toLinearMap) heq
    rw [matrix_specialDiscrBaseChange, matrix_specialDiscrBaseChange] at hm
    refine ⟨matrixOfCoeffMap k.1.toLinearMap i j, ?_⟩
    have hij := congrArg (fun M => M i j) hm
    change (algebraMap (PadicInt r) (Padic r)) (matrixOfCoeffMap k.1.toLinearMap i j) =
      (algebraMap ℚ (Padic r)) (matrixOfCoeffMap g.1.toLinearMap i j)
    exact hij.symm
  choose M hM using hentry
  exact ⟨M, funext fun i => funext fun j => hM i j⟩

lemma exists_integer_specialDiscrGroup (g : specialDiscrGroup ℚ)
    (M : Matrix (Fin 3) (Fin 3) ℤ)
    (hM : M.map (Int.castRingHom ℚ) = matrixOfCoeffMap g.1.toLinearMap) :
    ∃ k : specialDiscrGroup ℤ, specialDiscrBaseChange (Int.castRingHom ℚ) k = g := by
  have hdet : M.det = 1 := by
    have h : (M.det : ℚ) = 1 := calc
      _ = (M.map (Int.castRingHom ℚ)).det := (Int.castRingHom ℚ).map_det M
      _ = (matrixOfCoeffMap g.1.toLinearMap).det := congrArg Matrix.det hM
      _ = 1 := by rw [det_matrixOfCoeffMap, g.2.2]
    exact_mod_cast h
  have hunit : IsUnit M.det := by rw [hdet]; exact isUnit_one
  have hpres : ∀ t, discr (coeffMatrixMap M t) = discr t := by
    apply discr_preserved_of_matrix_map (Int.castRingHom ℚ) Int.cast_injective M
    rw [hM]
    intro t
    rw [coeffMatrixMap_matrixOfCoeffMap]
    exact g.2.1 t
  let k : specialDiscrGroup ℤ := ⟨coeffMatrixEquiv M hunit, ⟨by
    intro t
    rw [coeffMatrixEquiv_apply]
    exact hpres t, by rw [coeffMatrixEquiv_toLinearMap, det_coeffMatrixMap, hdet]⟩⟩
  refine ⟨k, ?_⟩
  apply specialDiscrGroup_matrix_injective
  dsimp only
  rw [matrix_specialDiscrBaseChange]
  change (matrixOfCoeffMap (coeffMatrixEquiv M hunit).toLinearMap).map (Int.castRingHom ℚ) = _
  rw [coeffMatrixEquiv_toLinearMap, matrixOfCoeffMap_coeffMatrixMap, hM]

theorem integer_pairOrbit_eq_of_local_eq {d ℓ : ℤ} (src dst : FormPair ℤ d ℓ)
    (hnd : ℓ ^ 2 ≠ 4 * d ^ 2)
    (hloc : ∀ (r : ℕ) [Fact r.Prime],
      (Quotient.mk _ (mapFormPair (Int.castRingHom (PadicInt r)) src) :
          SpecialPairOrbits (PadicInt r) d ℓ) =
        Quotient.mk _ (mapFormPair (Int.castRingHom (PadicInt r)) dst)) :
    (Quotient.mk _ src : SpecialPairOrbits ℤ d ℓ) = Quotient.mk _ dst := by
  have hndQ := map_nondegenerate (Int.castRingHom ℚ) Int.cast_injective hnd
  obtain ⟨f, hdet, hfirst, hsecond⟩ := exists_specialIsometry_of_nondegenerate_pair
    (mapFormPair (Int.castRingHom ℚ) dst) (mapFormPair (Int.castRingHom ℚ) src) hndQ
  let g : specialDiscrGroup ℚ := ⟨f.toLinearEquiv, ⟨fun t => f.map_app t, hdet⟩⟩
  have hg : g • mapFormPair (Int.castRingHom ℚ) dst = mapFormPair (Int.castRingHom ℚ) src := by
    apply Subtype.ext
    exact Prod.ext hfirst hsecond
  have htransport : ∀ (r : ℕ) [Fact r.Prime], ∃ k : specialDiscrGroup (PadicInt r),
      k • mapFormPair (Int.castRingHom (PadicInt r)) dst =
        mapFormPair (Int.castRingHom (PadicInt r)) src := by
    intro r hr
    exact MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp (Quotient.exact (hloc r)))
  obtain ⟨M, hM⟩ := exists_integer_matrix_of_local_transporters dst src hnd g hg htransport
  obtain ⟨k, hk⟩ := exists_integer_specialDiscrGroup g M hM
  have hks : k • dst = src := by
    apply mapFormPair_injective (Int.castRingHom ℚ) Int.cast_injective
    rw [mapFormPair_smul, hk, hg]
  exact Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨k, hks⟩))

end Erdos1148.DukeArithmetic
