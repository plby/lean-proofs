import ErdosProblems.Erdos1188.SparsePrimeCount

/- Ported from Lean 4.31.0 to 4.33.0; module names and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Polynomial-times-polylogarithmic modulus cutoff for sparse prime frames
-/

namespace Erdos1188

open scoped BigOperators

/-- The binary prime scale is monotone. -/
theorem binaryPrimeScale_mono : Monotone binaryPrimeScale := by
  intro a b hab
  unfold binaryPrimeScale
  have hr : Nat.log 2 a + 1 ≤ Nat.log 2 b + 1 := by
    exact Nat.add_le_add_right (Nat.log_mono_right hab) 1
  simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 128
    (Nat.mul_le_mul hr (Nat.pow_le_pow_right (n := 2) (by decide) hr))

/-- Every indexed prime below index `n` is bounded by the common scale at
`n`. -/
theorem nthPrime_le_binaryPrimeScale {i n : ℕ} (hin : i < n) :
    nthPrime i ≤ binaryPrimeScale n := by
  have hself := nthPrime_le_binary_log i
  have hmono := binaryPrimeScale_mono (Nat.succ_le_of_lt hin)
  exact hself.trans (by simpa [binaryPrimeScale] using hmono)

/-- Sparse heights are monotone. -/
theorem sparseHeight_mono : Monotone sparseHeight := by
  intro a b hab
  unfold sparseHeight sparseLog
  exact Nat.mul_le_mul_left 2048
    (Nat.add_le_add_right (Nat.log_mono_right (Nat.add_le_add_right hab 1)) 1)

/-- Fixed product absorbing the finitely many unrestricted seed coordinates. -/
noncomputable def sparseSeedProduct : ℕ :=
  ∏ i ∈ Finset.range sparseSeed, nthPrime i

/-- The genuinely growing part of the maximum-modulus cutoff. -/
def sparseLateScale (m : ℕ) : ℕ :=
  (binaryPrimeScale (m + 1)) ^ 2 * binaryPrimeScale (sparseHeight m)

/-- Full explicit cutoff. -/
noncomputable def sparsePrimeCutoff (m : ℕ) : ℕ :=
  sparseSeedProduct * sparseLateScale m

/-- The fixed seed product is positive. -/
theorem sparseSeedProduct_pos : 0 < sparseSeedProduct := by
  apply Finset.prod_pos
  intro i _
  exact (nthPrime_prime i).pos

/-- A support using only seed indices has product at most the seed product. -/
theorem earlyPrimeSupport_le_seed {m : ℕ} (J : Finset (Fin m))
    (hJ : ∀ j ∈ J, j.val < sparseSeed) :
    (∏ j ∈ J, nthPrime j.val) ≤ sparseSeedProduct := by
  let V : Finset ℕ := J.image Fin.val
  have hV : V ⊆ Finset.range sparseSeed := by
    intro v hv
    change v ∈ J.image Fin.val at hv
    rw [Finset.mem_image] at hv
    obtain ⟨j, hj, rfl⟩ := hv
    exact Finset.mem_range.mpr (hJ j hj)
  have hprod : (∏ v ∈ V, nthPrime v) = ∏ j ∈ J, nthPrime j.val := by
    exact Finset.prod_image (fun _ _ _ _ h => Fin.ext h)
  have hdvd := Finset.prod_dvd_prod_of_subset V (Finset.range sparseSeed)
    nthPrime hV
  rw [hprod] at hdvd
  exact Nat.le_of_dvd sparseSeedProduct_pos hdvd

/-- Products over optionalized base supports are unchanged. -/
theorem sparseBaseSupportProduct_eq {m : ℕ} (J : Finset (Fin m)) :
    (∏ j ∈ J.map Function.Embedding.some,
      sparseFactors (fun i : Fin m => nthPrime i.val) (nthPrime m) j) =
      ∏ j ∈ J, nthPrime j.val := by
  rw [Finset.prod_map]
  rfl

/-- A closing support contributes the closing prime times its base product. -/
theorem sparseClosingSupportProduct_eq {m : ℕ} (J : Finset (Fin m)) :
    (∏ j ∈ insert none (J.map Function.Embedding.some),
      sparseFactors (fun i : Fin m => nthPrime i.val) (nthPrime m) j) =
      nthPrime m * ∏ j ∈ J, nthPrime j.val := by
  have hn : none ∉ J.map Function.Embedding.some := by simp
  rw [Finset.prod_insert hn, Finset.prod_map]
  rfl

/-- The common indexed-prime scale is positive. -/
theorem binaryPrimeScale_pos (n : ℕ) : 0 < binaryPrimeScale n := by
  unfold binaryPrimeScale
  have hr : 0 < Nat.log 2 n + 1 := by omega
  exact Nat.mul_pos (Nat.mul_pos (by decide) hr) (pow_pos (by decide) _)

/-- The late scale is positive. -/
theorem sparseLateScale_pos (m : ℕ) : 0 < sparseLateScale m := by
  unfold sparseLateScale
  exact Nat.mul_pos (pow_pos (binaryPrimeScale_pos _) _)
    (binaryPrimeScale_pos _)

/-- The product attached to a late base cross-pair support is bounded by the
late scale. -/
theorem crossPairFrameProduct_le_scale {m : ℕ} (i : Fin m)
    (hi : sparseSeed ≤ i.val) (c : CrossPair i.val (sparseHeight i.val)) :
    (∏ j ∈ insert i
        ((crossPairSupport (sparseHeight_lt hi).le c).map (earlierEmbedding i)),
      nthPrime j.val) ≤ sparseLateScale m := by
  let lo : Fin i.val :=
    ⟨c.1.val, lt_of_lt_of_le c.1.isLt (sparseHeight_lt hi).le⟩
  let hiidx : Fin i.val :=
    ⟨sparseHeight i.val + c.2.val, by
      calc
        sparseHeight i.val + c.2.val <
            sparseHeight i.val + (i.val - sparseHeight i.val) :=
          Nat.add_lt_add_left c.2.isLt _
        _ = i.val := Nat.add_sub_of_le (sparseHeight_lt hi).le⟩
  have hlohi : lo ≠ hiidx := by
    exact crossPair_low_ne_high (sparseHeight_lt hi).le c
  have hnoti : i ∉
      (crossPairSupport (sparseHeight_lt hi).le c).map (earlierEmbedding i) := by
    intro hmem
    rw [Finset.mem_map] at hmem
    obtain ⟨j, _, hji⟩ := hmem
    have hv := congrArg Fin.val hji
    exact (ne_of_lt j.isLt) hv
  have hpi : nthPrime i.val ≤ binaryPrimeScale (m + 1) :=
    nthPrime_le_binaryPrimeScale (by omega)
  have hphi : nthPrime hiidx.val ≤ binaryPrimeScale (m + 1) :=
    nthPrime_le_binaryPrimeScale (by omega)
  have hhmono : sparseHeight i.val ≤ sparseHeight m :=
    sparseHeight_mono (by omega)
  have hplo : nthPrime lo.val ≤ binaryPrimeScale (sparseHeight m) := by
    apply nthPrime_le_binaryPrimeScale
    have hlo := c.1.isLt
    dsimp [lo]
    omega
  rw [Finset.prod_insert hnoti]
  have hpair : crossPairSupport (sparseHeight_lt hi).le c = {lo, hiidx} := rfl
  rw [hpair, Finset.prod_map]
  rw [Finset.prod_insert (by simpa using hlohi), Finset.prod_singleton]
  change nthPrime i.val * (nthPrime lo.val * nthPrime hiidx.val) ≤ sparseLateScale m
  unfold sparseLateScale
  calc
    nthPrime i.val * (nthPrime lo.val * nthPrime hiidx.val) ≤
        binaryPrimeScale (m + 1) *
          (binaryPrimeScale (sparseHeight m) * binaryPrimeScale (m + 1)) := by
      gcongr
    _ = (binaryPrimeScale (m + 1)) ^ 2 * binaryPrimeScale (sparseHeight m) := by
      ring

/-- Every allowed closing code also has product bounded by the late scale. -/
theorem closingCodePrimeProduct_le_scale {m : ℕ} (hm : sparseSeed ≤ m)
    (code : ClosingSupportCode m (sparseHeight m)) :
    nthPrime m *
        (∏ j ∈ closingCodeSupport (sparseHeight_lt hm).le code,
          nthPrime j.val) ≤ sparseLateScale m := by
  let S := binaryPrimeScale (m + 1)
  let T := binaryPrimeScale (sparseHeight m)
  have hSpos : 0 < S := binaryPrimeScale_pos _
  have hTpos : 0 < T := binaryPrimeScale_pos _
  have hpm : nthPrime m ≤ S := nthPrime_le_binaryPrimeScale (by omega)
  cases code with
  | none =>
      simp only [closingCodeSupport, Finset.prod_empty, mul_one]
      calc
        nthPrime m ≤ S := hpm
        _ ≤ S * S := Nat.le_mul_of_pos_right S hSpos
        _ ≤ S * S * T := Nat.le_mul_of_pos_right (S * S) hTpos
        _ = sparseLateScale m := by simp [sparseLateScale, S, T, pow_two]
  | some code =>
      cases code with
      | inl j =>
          simp only [closingCodeSupport, Finset.prod_singleton]
          have hpj : nthPrime j.val ≤ S := nthPrime_le_binaryPrimeScale (by omega)
          calc
            nthPrime m * nthPrime j.val ≤ S * S := Nat.mul_le_mul hpm hpj
            _ ≤ S * S * T := Nat.le_mul_of_pos_right (S * S) hTpos
            _ = sparseLateScale m := by simp [sparseLateScale, S, T, pow_two]
      | inr c =>
          let lo : Fin m :=
            ⟨c.1.val, lt_of_lt_of_le c.1.isLt (sparseHeight_lt hm).le⟩
          let hiidx : Fin m :=
            ⟨sparseHeight m + c.2.val, by
              calc
                sparseHeight m + c.2.val <
                    sparseHeight m + (m - sparseHeight m) :=
                  Nat.add_lt_add_left c.2.isLt _
                _ = m := Nat.add_sub_of_le (sparseHeight_lt hm).le⟩
          have hlohi : lo ≠ hiidx :=
            crossPair_low_ne_high (sparseHeight_lt hm).le c
          have hplo : nthPrime lo.val ≤ T := by
            apply nthPrime_le_binaryPrimeScale
            exact c.1.isLt
          have hphi : nthPrime hiidx.val ≤ S :=
            nthPrime_le_binaryPrimeScale (by omega)
          have hpair : closingCodeSupport (sparseHeight_lt hm).le
              (some (Sum.inr c)) = {lo, hiidx} := rfl
          rw [hpair, Finset.prod_insert (by simpa using hlohi),
            Finset.prod_singleton]
          calc
            nthPrime m * (nthPrime lo.val * nthPrime hiidx.val) ≤
                S * (T * S) := by gcongr
            _ = sparseLateScale m := by simp [sparseLateScale, S, T, pow_two]; ring

/-- Every support used by the assignment built from a range profile belongs
to its advertised mixed pool. -/
theorem primeSparseAssigned_mem_pool {m : ℕ}
    (R : SparseRangeProfile (fun i : Fin m => nthPrime i.val)
      (PrimeSparsePool m))
    (i : Fin m) (a : NonzeroResidue (nthPrime i.val)) :
    assignmentForSparseRanges (fun j : Fin m => nthPrime j.val)
        (PrimeSparsePool m) (primeSparsePoolSupport m) R i a ∈
      sparsePooledSupports (fun j : Fin m => nthPrime j.val)
        sparseSeed sparseHeight
        (fun j hj => (sparseHeight_lt hj).le)
        (primeDefaultAssignment m) i := by
  let A := assignmentForSparseRanges (fun j : Fin m => nthPrime j.val)
    (PrimeSparsePool m) (primeSparsePoolSupport m) R
  have hm : A i a ∈ assignmentRange (fun j : Fin m => nthPrime j.val) A i := by
    rw [assignmentRange, Finset.mem_image]
    exact ⟨a, Finset.mem_univ _, rfl⟩
  rw [assignmentForSparseRanges_range] at hm
  obtain ⟨s, hs, hsa⟩ := Finset.mem_image.mp hm
  have hp := s.property
  simpa [primeSparsePoolSupport] using hsa ▸ hp

/-- Every modulus in every prime sparse range-profile system is below the
explicit sparse cutoff. -/
theorem primeSparseSystem_modulus_le_cutoff {m : ℕ} (hm : sparseSeed ≤ m)
    (R : SparseRangeProfile (fun i : Fin m => nthPrime i.val)
      (PrimeSparsePool m))
    (c : CongruenceClass)
    (hc : c ∈ sparseAssignmentSystem
      (fun i : Fin m => nthPrime i.val) (nthPrime m)
      (fun i => (nthPrime_prime i.val).two_le) (nthPrime_prime m).two_le
      (sparseNthPrime_pairwise_coprime m)
      (primeSparseClosingFixed m hm)
      (assignmentForSparseRanges (fun i : Fin m => nthPrime i.val)
        (PrimeSparsePool m) (primeSparsePoolSupport m) R)) :
    c.1 ≤ sparsePrimeCutoff m := by
  classical
  let q := fun i : Fin m => nthPrime i.val
  let P := nthPrime m
  let A := assignmentForSparseRanges q (PrimeSparsePool m)
    (primeSparsePoolSupport m) R
  let close := primeSparseClosingFixed m hm
  rw [sparseAssignmentSystem, Finset.mem_image] at hc
  obtain ⟨d, _, rfl⟩ := hc
  rw [sparseArithmeticClass_modulus q P
    (fun i => (nthPrime_prime i.val).two_le) (nthPrime_prime m).two_le
    (sparseNthPrime_pairwise_coprime m) close A d]
  cases d with
  | inl d =>
      rw [sparseFrameSupport, sparseBaseSupportProduct_eq]
      by_cases hi : sparseSeed ≤ d.index.val
      · have hmem := primeSparseAssigned_mem_pool R d.index
          ⟨d.value, d.value_ne_zero⟩
        simp only [sparsePooledSupports, dif_pos hi] at hmem
        rw [mem_crossPairFamily_iff (sparseHeight_lt hi).le] at hmem
        obtain ⟨code, hcode⟩ := hmem
        have hb := crossPairFrameProduct_le_scale d.index hi code
        have heq : assignedFixed q A d =
            (crossPairSupport (sparseHeight_lt hi).le code).map
              (earlierEmbedding d.index) := by
          unfold assignedFixed A q
          rw [hcode]
        have hb' :
            (∏ j ∈ frameSupport q (assignedFixed q A) d,
              nthPrime j.val) ≤ sparseLateScale m := by
          simpa [frameSupport, heq] using hb
        calc
          (∏ j ∈ frameSupport q (assignedFixed q A) d,
              nthPrime j.val) ≤ sparseLateScale m := hb'
          _ ≤ sparseSeedProduct * sparseLateScale m :=
            Nat.le_mul_of_pos_left _ sparseSeedProduct_pos
          _ = sparsePrimeCutoff m := by rfl
      · have hseed := earlyPrimeSupport_le_seed
          (frameSupport q (assignedFixed q A) d) (by
            intro j hj
            rcases Finset.mem_insert.mp hj with hjd | hjfixed
            · simpa [hjd] using Nat.lt_of_not_ge hi
            · have hlt := assignedFixed_fixesEarlier q A d j hjfixed
              exact lt_trans hlt (Nat.lt_of_not_ge hi))
        calc
          (∏ j ∈ frameSupport q (assignedFixed q A) d,
              nthPrime j.val) ≤ sparseSeedProduct := hseed
          _ ≤ sparseSeedProduct * sparseLateScale m :=
            Nat.le_mul_of_pos_right _ (sparseLateScale_pos m)
          _ = sparsePrimeCutoff m := by rfl
  | inr a =>
      rw [sparseFrameSupport, sparseClosingSupportProduct_eq]
      let code : ClosingSupportCode m (sparseHeight m) :=
        closingCodeEmbedding (sparseClosing_numeric_data hm).1
          (sparseClosing_numeric_data hm).2 ((ZMod.finEquiv (nthPrime m)).symm a)
      have hclose : close a = closingCodeSupport (sparseHeight_lt hm).le code := by
        rfl
      change primeSparseClosingFixed m hm a =
        closingCodeSupport (sparseHeight_lt hm).le code at hclose
      change nthPrime m *
        (∏ j ∈ primeSparseClosingFixed m hm a, nthPrime j.val) ≤
          sparsePrimeCutoff m
      rw [hclose]
      have hb := closingCodePrimeProduct_le_scale hm code
      calc
        nthPrime m *
            (∏ j ∈ closingCodeSupport (sparseHeight_lt hm).le code,
              nthPrime j.val) ≤ sparseLateScale m := hb
        _ ≤ sparseSeedProduct * sparseLateScale m :=
          Nat.le_mul_of_pos_left _ sparseSeedProduct_pos
        _ = sparsePrimeCutoff m := by rfl

end Erdos1188
