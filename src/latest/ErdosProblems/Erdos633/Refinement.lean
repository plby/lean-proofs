import ErdosProblems.Erdos633.Area
import ErdosProblems.Erdos633.Similarity
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Refinement of genuine congruent triangle tilings

The construction replaces each large tile by an isometric copy of a tiling of
the reference tile. It proves coverage and disjointness geometrically, including
tilings with T-junctions, and multiplies the tile counts.
-/

namespace Erdos633

open MeasureTheory

theorem orientedDoubleArea_ne_zero_of_affineIndependent {a b c : ℂ}
    (h : AffineIndependent ℝ ![a, b, c]) : orientedDoubleArea a b c ≠ 0 := by
  intro hd
  have hcoeff (r s : ℝ) (hv : r • (b - a) + s • (c - a) = 0) : r = 0 ∧ s = 0 := by
    have hw : ∑ i : Fin 3, (![ -r - s, r, s] : Fin 3 → ℝ) i = 0 := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
        Matrix.cons_val_zero, Matrix.cons_val_succ]
      ring
    have hsum : ∑ i : Fin 3, (![ -r - s, r, s] : Fin 3 → ℝ) i •
        (![a, b, c] : Fin 3 → ℂ) i = 0 := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
        Matrix.cons_val_zero, Matrix.cons_val_succ]
      calc
        (-r - s) • a + (r • b + s • c) = r • (b - a) + s • (c - a) := by
          simp only [sub_smul, neg_smul, smul_sub]
          abel
        _ = 0 := hv
    have hzero := affineIndependent_iff.mp h Finset.univ ![-r - s, r, s] hw hsum
    exact ⟨hzero 1 (Finset.mem_univ _), hzero 2 (Finset.mem_univ _)⟩
  have hre : (b - a).re = 0 := by
    apply (hcoeff (-(c - a).re) (b - a).re ?_).2
    apply Complex.ext
    · simp only [Complex.add_re, Complex.smul_re, Complex.zero_re, smul_eq_mul]
      ring
    · simp only [Complex.add_im, Complex.smul_im, Complex.zero_im, smul_eq_mul]
      change (b - a).re * (c - a).im - (b - a).im * (c - a).re = 0 at hd
      nlinarith
  have him : (b - a).im = 0 := by
    apply (hcoeff (-(c - a).im) (b - a).im ?_).2
    apply Complex.ext
    · simp only [Complex.add_re, Complex.smul_re, Complex.zero_re, smul_eq_mul]
      change (b - a).re * (c - a).im - (b - a).im * (c - a).re = 0 at hd
      nlinarith
    · simp only [Complex.add_im, Complex.smul_im, Complex.zero_im, smul_eq_mul]
      ring
  have hba : b = a := sub_eq_zero.mp (Complex.ext hre him)
  have hi : (0 : Fin 3) = 1 := h.injective hba.symm
  exact (by decide : (0 : Fin 3) ≠ 1) hi

noncomputable def Triangle.mapAffineEquiv (T : Triangle) (e : ℂ ≃ᵃ[ℝ] ℂ) : Triangle where
  a := e T.a
  b := e T.b
  c := e T.c
  nondegenerate := by
    apply orientedDoubleArea_ne_zero_of_affineIndependent
    have h := T.affineIndependent.map' e.toAffineMap e.injective
    have heq : e.toAffineMap ∘ ![T.a, T.b, T.c] = ![e T.a, e T.b, e T.c] := by
      funext i
      fin_cases i <;> rfl
    rwa [heq] at h

theorem Triangle.mapAffineEquiv_carrier (T : Triangle) (e : ℂ ≃ᵃ[ℝ] ℂ) :
    (T.mapAffineEquiv e).carrier = e '' T.carrier := by
  have h := e.toAffineMap.image_convexHull {T.a, T.b, T.c}
  change (e : ℂ → ℂ) '' convexHull ℝ {T.a, T.b, T.c} =
    convexHull ℝ ((e : ℂ → ℂ) '' {T.a, T.b, T.c}) at h
  change convexHull ℝ {e T.a, e T.b, e T.c} = e '' convexHull ℝ {T.a, T.b, T.c}
  simpa only [Set.image_insert_eq, Set.image_singleton] using h.symm

theorem Triangle.mapAffineEquiv_comp (T : Triangle) (e f : ℂ ≃ᵃ[ℝ] ℂ) :
    (T.mapAffineEquiv e).mapAffineEquiv f = T.mapAffineEquiv (e.trans f) := by
  apply Triangle.ext <;> rfl

/-- The geometric area scales by the absolute determinant of an affine map. -/
theorem Triangle.volume_mapAffineEquiv (T : Triangle) (e : ℂ ≃ᵃ[ℝ] ℂ) :
    volume (T.mapAffineEquiv e).carrier =
      ENNReal.ofReal |LinearMap.det (e.linear : ℂ →ₗ[ℝ] ℂ)| * volume T.carrier := by
  have heq : (e : ℂ → ℂ) = fun z => e.linear z + e 0 := by
    funext z
    simpa only [vadd_eq_add, add_zero] using e.map_vadd 0 z
  rw [T.mapAffineEquiv_carrier]
  calc
    volume (e '' T.carrier) =
        volume ((IsometryEquiv.vaddConst (e 0)) ''
          ((e.linear : ℂ →ₗ[ℝ] ℂ) '' T.carrier)) := by
      congr 1
      rw [Set.image_image]
      exact congrArg (fun f : ℂ → ℂ => f '' T.carrier) heq
    _ = volume ((e.linear : ℂ →ₗ[ℝ] ℂ) '' T.carrier) :=
      isometry_volume_image _ _
    _ = _ := volume.addHaar_image_linearMap _ _

theorem Triangle.area_mapAffineEquiv (T : Triangle) (e : ℂ ≃ᵃ[ℝ] ℂ) :
    (T.mapAffineEquiv e).area = |LinearMap.det (e.linear : ℂ →ₗ[ℝ] ℂ)| * T.area := by
  unfold Triangle.area
  rw [T.volume_mapAffineEquiv, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]

noncomputable def Triangle.mapIsometry (T : Triangle) (e : ℂ ≃ᵢ ℂ) : Triangle :=
  T.mapAffineEquiv e.toRealAffineIsometryEquiv.toAffineEquiv

theorem Triangle.mapIsometry_carrier (T : Triangle) (e : ℂ ≃ᵢ ℂ) :
    (T.mapIsometry e).carrier = e '' T.carrier :=
  T.mapAffineEquiv_carrier e.toRealAffineIsometryEquiv.toAffineEquiv

/-- Isometric transport keeps the reference tile unchanged. -/
noncomputable def CongruentTiling.mapIsometry {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (e : ℂ ≃ᵢ ℂ) :
    CongruentTiling (P.mapIsometry e) R N where
  tile i := (T.tile i).mapIsometry e
  congruent := by
    intro i
    obtain ⟨f, hf⟩ := T.congruent i
    refine ⟨f.trans e, ?_⟩
    change (fun z : ℂ => e (f z)) '' R.carrier = ((T.tile i).mapIsometry e).carrier
    rw [← Set.image_image e f R.carrier, hf, Triangle.mapIsometry_carrier]
  covers := by
    simp only [Triangle.mapIsometry_carrier]
    rw [← Set.image_iUnion, T.covers]
  disjoint := by
    intro i j hij
    simp only [Triangle.mapIsometry_carrier]
    have hi := e.toHomeomorph.image_interior (T.tile i).carrier
    have hj := e.toHomeomorph.image_interior (T.tile j).carrier
    change e '' interior (T.tile i).carrier = interior (e '' (T.tile i).carrier) at hi
    change e '' interior (T.tile j).carrier = interior (e '' (T.tile j).carrier) at hj
    rw [← hi, ← hj]
    exact Set.disjoint_image_of_injective e.injective (T.disjoint hij)

theorem TriangleDissection.tile_subset {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (i : Fin N) : (T.tile i).carrier ⊆ P.carrier := by
  intro z hz
  rw [← T.covers]
  exact Set.mem_iUnion.mpr ⟨i, hz⟩

theorem TriangleDissection.tile_interior_subset {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (i : Fin N) :
    interior (T.tile i).carrier ⊆ interior P.carrier :=
  interior_mono (T.tile_subset i)

theorem CongruentTiling.tile_subset {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (i : Fin N) : (T.tile i).carrier ⊆ P.carrier :=
  T.toTriangleDissection.tile_subset i

theorem CongruentTiling.tile_interior_subset {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (i : Fin N) :
    interior (T.tile i).carrier ⊆ interior P.carrier :=
  T.toTriangleDissection.tile_interior_subset i

/-- Replace the reference tile by an isometric presentation of the same shape. -/
def CongruentTiling.changeTile {P R Q : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (e : ℂ ≃ᵢ ℂ) (he : e '' Q.carrier = R.carrier) :
    CongruentTiling P Q N where
  toTriangleDissection := T.toTriangleDissection
  congruent := by
    intro i
    obtain ⟨f, hf⟩ := T.congruent i
    refine ⟨e.trans f, ?_⟩
    change (fun z : ℂ => f (e z)) '' Q.carrier = (T.tile i).carrier
    rw [← Set.image_image f e Q.carrier, he, hf]

/-- A finite indexing type can be converted to the numerical tiling definition. -/
noncomputable def CongruentTiling.ofIndexed {P R : Triangle} {ι : Type*} [Fintype ι]
    (tile : ι → Triangle)
    (congruent : ∀ i, ∃ f : ℂ ≃ᵢ ℂ, f '' R.carrier = (tile i).carrier)
    (covers : (⋃ i, (tile i).carrier) = P.carrier)
    (disjoint : Pairwise fun i j =>
      Disjoint (interior (tile i).carrier) (interior (tile j).carrier)) :
    CongruentTiling P R (Fintype.card ι) where
  tile k := tile ((Fintype.equivFin ι).symm k)
  congruent k := congruent ((Fintype.equivFin ι).symm k)
  covers := by
    rw [← covers]
    ext z
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨(Fintype.equivFin ι).symm k, hk⟩
    · rintro ⟨i, hi⟩
      refine ⟨Fintype.equivFin ι i, ?_⟩
      rw [Equiv.symm_apply_apply]
      exact hi
  disjoint _ _ h := disjoint ((Fintype.equivFin ι).symm.injective.ne h)

/-- Different pieces may use different tile counts. The resulting count is the
sum of those counts, and no congruence among the parent pieces is required. -/
noncomputable def TriangleDissection.refine {P Q : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (M : Fin N → ℕ)
    (S : ∀ i, CongruentTiling (T.tile i) Q (M i)) :
    CongruentTiling P Q (∑ i, M i) := by
  have hcard : Fintype.card (Σ i : Fin N, Fin (M i)) = ∑ i, M i := by simp
  rw [← hcard]
  apply CongruentTiling.ofIndexed (fun p : Σ i : Fin N, Fin (M i) => (S p.1).tile p.2)
  · intro p
    exact (S p.1).congruent p.2
  · ext z
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨⟨i, j⟩, hz⟩
      exact T.tile_subset i ((S i).tile_subset j hz)
    · intro hz
      rw [← T.covers] at hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      rw [← (S i).covers] at hi
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hi
      exact ⟨⟨i, j⟩, hj⟩
  · rintro ⟨i, j⟩ ⟨k, l⟩ hne
    by_cases hik : i = k
    · subst k
      have hjl : j ≠ l := by
        intro h
        apply hne
        subst l
        rfl
      exact (S i).disjoint hjl
    · exact (T.disjoint hik).mono
        ((S i).tile_interior_subset j) ((S k).tile_interior_subset l)

/-- Flatten equal-size refinements of every piece. -/
noncomputable def CongruentTiling.refinePieces {P R Q : Triangle} {N M : ℕ}
    (T : CongruentTiling P R N) (S : ∀ i, CongruentTiling (T.tile i) Q M) :
    CongruentTiling P Q (N * M) := by
  simpa using T.toTriangleDissection.refine (fun _ => M) S

/-- Congruent tilings compose, multiplying the number of pieces. -/
noncomputable def CongruentTiling.refine {P R Q : Triangle} {N M : ℕ}
    (T : CongruentTiling P R N) (S : CongruentTiling R Q M) :
    CongruentTiling P Q (N * M) := by
  choose e he using T.congruent
  apply T.refinePieces
  intro i
  apply (S.mapIsometry (e i)).of_carrier_eq
  exact (R.mapIsometry_carrier (e i)).trans (he i)

end Erdos633
