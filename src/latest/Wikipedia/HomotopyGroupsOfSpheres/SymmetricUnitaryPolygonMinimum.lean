import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryPolygonSublevels
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryCriticalGenerator
import Wikipedia.HomotopyGroupsOfSpheres.BalancedMinimumExponential

/-! # The minimum energy and its criticality in compact constrained polygon sublevels -/

noncomputable section

open scoped Matrix.Norms.Frobenius
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon

open VertexSpace BalancedRealInvolutions ImaginarySymmetricMatrices

variable {N : Type*} [Fintype N] [DecidableEq N] {m : ℕ}

theorem critical_of_isLocalMin (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (v : VertexSpace.Space N m) (hmin : IsLocalMin (energy a b τ) v) :
    fderiv ℝ (localEnergy a b τ v) 0 = 0 := by
  have ht : (0 : Model N m) ∈ (atVertices v).target := by
    rw [← atVertices_self v]
    exact (atVertices v).map_source (mem_atVertices_source v)
  have hc : ContinuousAt (atVertices v).symm (0 : Model N m) :=
    (atVertices v).symm.continuousAt ht
  have hm : IsLocalMin (energy a b τ) ((atVertices v).symm 0) := by
    simpa only [atVertices_symm_zero] using hmin
  exact IsLocalMin.fderiv_eq_zero (E := Model N m) (hm.comp_continuous hc)

theorem exists_critical_minimizer (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (E : ℝ) (hcompact : IsCompact (energySublevel a b τ E))
    (hne : (energySublevel a b τ E).Nonempty) :
    ∃ v ∈ energySublevel a b τ E, IsMinOn (energy a b τ) (admissible a b m) v ∧
      fderiv ℝ (localEnergy a b τ v) 0 = 0 := by
  have hcont : ContinuousOn (energy a b τ) (energySublevel a b τ E) :=
    (continuousOn_energy a b τ).mono (fun _ hv ↦ hv.1)
  obtain ⟨v, hv, hmin⟩ := hcompact.exists_isMinOn hne hcont
  have hglobal : IsMinOn (energy a b τ) (admissible a b m) v := by
    intro w hw
    by_cases he : energy a b τ w ≤ E
    · exact hmin ⟨hw, he⟩
    · exact hv.2.trans (lt_of_not_ge he).le
  exact ⟨v, hv, hglobal, critical_of_isLocalMin a b τ v
    (hglobal.isLocalMin ((isOpen_admissible a b m).mem_nhds hv.1))⟩

theorem critical_antipodal_energy_ge (n : ℕ) (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : VertexSpace.Space (Index n) m) (hv : v ∈ admissible specialIdentity (antipode n) m)
    (hcrit : fderiv ℝ (localEnergy specialIdentity (antipode n) τ v) 0 = 0) :
    (4 * n : ℝ) * Real.pi ^ 2 ≤ energy specialIdentity (antipode n) τ v := by
  obtain ⟨A, hend, hpath⟩ := critical_identity_is_exponential
    (antipode n) τ hτ hzero hone v hv hcrit
  have hexp : NormedSpace.exp (imaginary A.val) = -1 :=
    (congrArg (fun B : SpecialSpace (Index n) ↦ B.val.val.val) hend).trans (antipode_matrix n)
  have hn := antipodal_squareNorm_ge A.val A.property.1 hexp
  have hcard : (Fintype.card (Index n) : ℝ) = 2 * n := by simp [Index, two_mul]
  rw [hcard] at hn
  rw [energy_eq_squareNorm_of_exponential (antipode n) τ hτ hzero hone v hv A hpath]
  nlinarith only [hn]

theorem antipodal_energy_ge_of_compact_sublevel (n : ℕ) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1) (E : ℝ)
    (hcompact : IsCompact (energySublevel specialIdentity (antipode n) τ E))
    (v : VertexSpace.Space (Index n) m) (hv : v ∈ energySublevel specialIdentity (antipode n) τ E) :
    (4 * n : ℝ) * Real.pi ^ 2 ≤ energy specialIdentity (antipode n) τ v := by
  obtain ⟨w, hw, hmin, hcrit⟩ := exists_critical_minimizer
    specialIdentity (antipode n) τ E hcompact ⟨v, hv⟩
  exact (critical_antipodal_energy_ge n τ hτ hzero hone w hw.1 hcrit).trans (hmin hv.1)

theorem critical_of_minimum_energy (n : ℕ) (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1) (E : ℝ)
    (hcompact : IsCompact (energySublevel specialIdentity (antipode n) τ E))
    (v : VertexSpace.Space (Index n) m) (hv : v ∈ energySublevel specialIdentity (antipode n) τ E)
    (he : energy specialIdentity (antipode n) τ v = (4 * n : ℝ) * Real.pi ^ 2) :
    fderiv ℝ (localEnergy specialIdentity (antipode n) τ v) 0 = 0 := by
  have hmin : IsMinOn (energy specialIdentity (antipode n) τ)
      (admissible specialIdentity (antipode n) m) v := by
    intro w hw
    by_cases hE : energy specialIdentity (antipode n) τ w ≤ E
    · rw [he]
      exact antipodal_energy_ge_of_compact_sublevel n τ hτ hzero hone E hcompact w ⟨hw, hE⟩
    · exact hv.2.trans (lt_of_not_ge hE).le
  exact critical_of_isLocalMin specialIdentity (antipode n) τ v
    (hmin.isLocalMin ((isOpen_admissible specialIdentity (antipode n) m).mem_nhds hv.1))

theorem energy_eq_min_iff_rotation (n : ℕ) (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1) (E : ℝ)
    (hcompact : IsCompact (energySublevel specialIdentity (antipode n) τ E))
    (v : VertexSpace.Space (Index n) m) (hv : v ∈ energySublevel specialIdentity (antipode n) τ E) :
    energy specialIdentity (antipode n) τ v = (4 * n : ℝ) * Real.pi ^ 2 ↔
      ∃ J : BalancedRealInvolutions.Space n, ∀ t ∈ Icc (0 : ℝ) 1,
        path specialIdentity (antipode n) τ hτ v hv.1 t = rotation J (t * Real.pi) := by
  constructor
  · intro he
    have hcrit := critical_of_minimum_energy n τ hτ hzero hone E hcompact v hv he
    obtain ⟨A, hend, hpath⟩ := critical_identity_is_exponential
      (antipode n) τ hτ hzero hone v hv.1 hcrit
    have hexp : NormedSpace.exp (imaginary A.val) = -1 :=
      (congrArg (fun B : SpecialSpace (Index n) ↦ B.val.val.val) hend).trans (antipode_matrix n)
    have hnorm : RealMatrixSquareNorm.squareNorm A.val = (2 * n : ℝ) * Real.pi ^ 2 := by
      have h := energy_eq_squareNorm_of_exponential (antipode n) τ hτ hzero hone v hv.1 A hpath
      rw [he] at h
      nlinarith only [h]
    obtain ⟨J, hJ⟩ := (antipodal_squareNorm_eq_iff_balanced n A.val A.property.1 A.property.2
      hexp).mp hnorm
    have hA : A = minimumGenerator J := Subtype.ext hJ
    refine ⟨J, fun t ht ↦ (hpath t ht).trans ?_⟩
    rw [hA, exponentialCurve_minimumGenerator]
  · rintro ⟨J, hJ⟩
    have hpath (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        path specialIdentity (antipode n) τ hτ v hv.1 t =
          exponentialCurve (minimumGenerator J) t := by
      rw [exponentialCurve_minimumGenerator]
      exact hJ t ht
    rw [energy_eq_squareNorm_of_exponential (antipode n) τ hτ hzero hone v hv.1
      (minimumGenerator J) hpath, minimumGenerator_squareNorm]
    ring

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon
