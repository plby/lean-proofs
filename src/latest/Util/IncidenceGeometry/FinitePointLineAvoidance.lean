import Util.IncidenceGeometry.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Baire.Lemmas

open Classical
noncomputable section

lemma FinitePointLineAvoidance
    (W : Set (EuclideanSpace ℝ (Fin 2)))
    (points : Finset (EuclideanSpace ℝ (Fin 2)))
    (lines : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))))
    (hWopen : IsOpen W) (hWnonempty : W.Nonempty)
    (hline : ∀ ℓ ∈ lines,
      (ℓ : Set (EuclideanSpace ℝ (Fin 2))).Nonempty ∧
        Module.finrank ℝ ℓ.direction = 1) :
    ∃ x ∈ W, x ∉ (points : Set (EuclideanSpace ℝ (Fin 2))) ∧
      ∀ ℓ ∈ lines, x ∉ (ℓ : Set (EuclideanSpace ℝ (Fin 2))) := by
  let E := EuclideanSpace ℝ (Fin 2)
  have affineLine_compl_open_dense :
      ∀ ℓ : AffineSubspace ℝ E,
        (ℓ : Set E).Nonempty ∧ Module.finrank ℝ ℓ.direction = 1 →
          IsOpen ((ℓ : Set E)ᶜ) ∧ Dense ((ℓ : Set E)ᶜ) := by
    intro ℓ hℓ
    have hℓ_ne_top : ℓ ≠ ⊤ := by
      intro htop
      have hfin : Module.finrank ℝ ℓ.direction = 2 := by
        rw [htop, AffineSubspace.direction_top, finrank_top,
          finrank_euclideanSpace_fin]
      have hbad : (1 : ℕ) = 2 := hℓ.2.symm.trans hfin
      norm_num at hbad
    have hconv : Convex ℝ (ℓ : Set E) := by
      rw [convex_iff_segment_subset]
      intro x hx y hy z hz
      rw [segment_eq_image_lineMap] at hz
      rcases hz with ⟨t, _ht, rfl⟩
      exact AffineMap.lineMap_mem t hx hy
    have hinterior_empty : interior (ℓ : Set E) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hne : (interior (ℓ : Set E)).Nonempty := ⟨x, hx⟩
      have hspan : affineSpan ℝ (ℓ : Set E) = ⊤ :=
        (hconv.interior_nonempty_iff_affineSpan_eq_top).mp hne
      rw [AffineSubspace.affineSpan_coe] at hspan
      exact hℓ_ne_top hspan
    exact ⟨ℓ.closed_of_finiteDimensional.isOpen_compl,
      interior_eq_empty_iff_dense_compl.mp hinterior_empty⟩
  let G : Set (Set E) :=
    ((fun p : E => ({p} : Set E)ᶜ) '' (points : Set E)) ∪
      ((fun ℓ : AffineSubspace ℝ E => ((ℓ : Set E)ᶜ : Set E)) ''
        (lines : Set (AffineSubspace ℝ E)))
  have hGfinite : G.Finite := by
    exact (points.finite_toSet.image _).union (lines.finite_toSet.image _)
  have hGopen : ∀ t ∈ G, IsOpen t := by
    intro t ht
    rcases ht with ⟨p, _hp, rfl⟩ | ⟨ℓ, hℓmem, rfl⟩
    · exact isOpen_compl_singleton
    · exact (affineLine_compl_open_dense ℓ (hline ℓ hℓmem)).1
  have hGdense : ∀ t ∈ G, Dense t := by
    intro t ht
    rcases ht with ⟨p, _hp, rfl⟩ | ⟨ℓ, hℓmem, rfl⟩
    · exact dense_compl_singleton p
    · exact (affineLine_compl_open_dense ℓ (hline ℓ hℓmem)).2
  have hdense : Dense (⋂₀ G) := hGfinite.dense_sInter hGopen hGdense
  obtain ⟨x, hxW, hxG⟩ := hdense.inter_open_nonempty W hWopen hWnonempty
  refine ⟨x, hxW, ?_, ?_⟩
  · intro hxpoints
    have hmemG : ({x} : Set E)ᶜ ∈ G := Or.inl ⟨x, hxpoints, rfl⟩
    exact (Set.sInter_subset_of_mem hmemG hxG) rfl
  · intro ℓ hℓmem hxℓ
    have hmemG : ((ℓ : Set E)ᶜ : Set E) ∈ G := Or.inr ⟨ℓ, hℓmem, rfl⟩
    exact (Set.sInter_subset_of_mem hmemG hxG) hxℓ
