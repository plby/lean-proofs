import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructurePolygonSublevels
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureStationaryPolygon
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPolygonMinimum

/-!
# Minimum energy in compact complex-structure polygon sublevels

Minimizing in the actual compact sublevel gives a local minimum in the
complex-structure vertex product. Its local coordinate derivative vanishes,
so the proved critical-point classification and antipodal energy bound apply.
-/

open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon

open NoExoticSixSphere.GLOrthonormalization ComplexStructures ComplexStructureVertices

variable {n m : ℕ}

theorem critical_of_isLocalMin (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (v : ComplexStructureVertices.Space n m) (hmin : IsLocalMin (energy a b τ) v) :
    fderiv ℝ (localEnergy a b τ v) 0 = 0 := by
  have htarget : (0 : Model v) ∈ (atVertices v).target := by
    rw [target_eq_univ]
    exact mem_univ _
  have hc : ContinuousAt (atVertices v).symm (0 : Model v) :=
    (atVertices v).symm.continuousAt htarget
  have hm : IsLocalMin (energy a b τ) ((atVertices v).symm 0) := by
    simpa only [atVertices_symm_zero] using hmin
  exact IsLocalMin.fderiv_eq_zero (E := Model v) (hm.comp_continuous hc)

theorem exists_critical_minimizer (a b : ComplexStructures.Space n)
    (τ : Fin (m + 2) → ℝ) (E : ℝ) (hcompact : IsCompact (energySublevel a b τ E))
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

theorem critical_antipodal_energy_ge (a b : ComplexStructures.Space n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : ComplexStructureVertices.Space n m) (hv : v ∈ admissible a b m)
    (hcrit : fderiv ℝ (localEnergy a b τ v) 0 = 0)
    (hanti : (Cayley.relative a b).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4))) :
    ((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2 ≤ energy a b τ v :=
  Polygon.stationary_antipodal_energy_ge (toSymplectic a) (toSymplectic b) τ hτ hzero hone
    (forget v) (admissible_forget a b hv)
    (Polygon.isStationary_of_mfderiv_eq_zero (toSymplectic a) (toSymplectic b) τ
      (forget v) (admissible_forget a b hv) (critical_forget a b τ v hv hcrit)) hanti

theorem antipodal_energy_ge_of_compact_sublevel (a b : ComplexStructures.Space n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1) (E : ℝ)
    (hcompact : IsCompact (energySublevel a b τ E))
    (hanti : (Cayley.relative a b).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (v : ComplexStructureVertices.Space n m) (hv : v ∈ energySublevel a b τ E) :
    ((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2 ≤ energy a b τ v := by
  obtain ⟨w, hw, hmin, hcrit⟩ := exists_critical_minimizer a b τ E hcompact ⟨v, hv⟩
  exact (critical_antipodal_energy_ge a b τ hτ hzero hone w hw.1 hcrit hanti).trans (hmin hv.1)

theorem critical_of_minimum_energy (a b : ComplexStructures.Space n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1) (E : ℝ)
    (hcompact : IsCompact (energySublevel a b τ E))
    (hanti : (Cayley.relative a b).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (v : ComplexStructureVertices.Space n m) (hv : v ∈ energySublevel a b τ E)
    (he : energy a b τ v = ((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2) :
    fderiv ℝ (localEnergy a b τ v) 0 = 0 := by
  have hmin : IsMinOn (energy a b τ) (admissible a b m) v := by
    intro w hw
    by_cases hE : energy a b τ w ≤ E
    · rw [he]
      exact antipodal_energy_ge_of_compact_sublevel a b τ hτ hzero hone E hcompact hanti w ⟨hw, hE⟩
    · exact hv.2.trans (lt_of_not_ge hE).le
  exact critical_of_isLocalMin a b τ v
    (hmin.isLocalMin ((isOpen_admissible a b m).mem_nhds hv.1))

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon
