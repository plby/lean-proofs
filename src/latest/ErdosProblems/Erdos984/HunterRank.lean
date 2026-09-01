/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterLocalizedKernel
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Rank and coordinate-projection lemmas for resonant frequencies
-/

open Set Function
open scoped BigOperators

namespace Erdos984

noncomputable section

/-- A linearly independent finite family of coordinate vectors has a
nonsingular square coordinate minor. -/
lemma exists_ne_zero_coordinate_minor
    {R D : Type*} [Fintype R] [DecidableEq R] [Finite D]
    (v : R → D → ℝ) (hv : LinearIndependent ℝ v) :
    ∃ σ : R → D, (Matrix.of fun r c ↦ v r (σ c)).det ≠ 0 := by
  classical
  let _ := Fintype.ofFinite D
  let A : Matrix R D ℝ := Matrix.of v
  have hrow : LinearIndependent ℝ A.row := by
    change LinearIndependent ℝ v
    exact hv
  have hrank : A.rank = Fintype.card R := hrow.rank_matrix
  have hspan : Module.finrank ℝ (Submodule.span ℝ (Set.range A.col)) =
      Fintype.card R := by
    rw [← A.rank_eq_finrank_span_cols]
    exact hrank
  obtain ⟨f, hfmem, _hfspan, hfind⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range A.col)
  let e : R ≃ Fin (Module.finrank ℝ
      (Submodule.span ℝ (Set.range A.col))) :=
    (Fintype.equivFin R).trans (finCongr hspan.symm)
  have hex : ∀ r : R, ∃ j : D, A.col j = f (e r) := by
    intro r
    simpa only [Set.mem_range] using hfmem (e r)
  choose σ hσ using hex
  let B : Matrix R R ℝ := Matrix.of fun r c ↦ v r (σ c)
  have hcol : LinearIndependent ℝ B.col := by
    have hfcomp : LinearIndependent ℝ (f ∘ e) :=
      hfind.comp e e.injective
    convert hfcomp using 1
    funext c r
    have hc := congrFun (hσ c) r
    change v r (σ c) = f (e c) r
    exact hc
  have hBinj : Function.Injective B.mulVec := by
    intro x y hxy
    have hzero : B.mulVec (x - y) = 0 := by
      rw [Matrix.mulVec_sub, hxy, sub_self]
    have hsum : ∑ c, (x c - y c) • B.col c = 0 := by
      ext r
      have hr := congrFun hzero r
      simpa [Matrix.mulVec, dotProduct, Matrix.col, mul_comm,
        sub_mul] using hr
    have hcoeff := (Fintype.linearIndependent_iff.mp hcol) (x - y) hsum
    funext c
    have hc := hcoeff c
    exact sub_eq_zero.mp hc
  have hBunit : IsUnit B := Matrix.mulVec_injective_iff_isUnit.mp hBinj
  refine ⟨σ, ?_⟩
  have hdetunit : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hBunit
  have hdet : B.det ≠ 0 := isUnit_iff_ne_zero.mp hdetunit
  simpa [B] using hdet

/-- A nonsingular coordinate minor makes restriction to those coordinates
injective on the span of the given family. -/
lemma coordinate_restriction_injOn_span
    {R D : Type*} [Fintype R] [DecidableEq R]
    (v : R → D → ℝ) (σ : R → D)
    (hdet : (Matrix.of fun r c ↦ v r (σ c)).det ≠ 0) :
    Set.InjOn (fun w : D → ℝ ↦ fun r ↦ w (σ r))
      (Submodule.span ℝ (Set.range v)) := by
  classical
  intro w hw w' hw' heq
  have hdiff : w - w' ∈ Submodule.span ℝ (Set.range v) :=
    Submodule.sub_mem _ hw hw'
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hdiff
  let B : Matrix R R ℝ := Matrix.of fun r j ↦ v r (σ j)
  have hdetT : B.transpose.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact hdet
  have hBTunit : IsUnit B.transpose :=
    (Matrix.isUnit_iff_isUnit_det B.transpose).2
    (isUnit_iff_ne_zero.2 hdetT)
  have hBTinj : Function.Injective B.transpose.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 hBTunit
  have hmul : B.transpose.mulVec c = 0 := by
    ext j
    have hcoord := congrFun heq j
    have hsumcoord := congrArg (fun u : D → ℝ ↦ u (σ j)) hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hsumcoord
    simp only [B, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      Matrix.of_apply]
    calc
      ∑ i, v i (σ j) * c i = ∑ i, c i * v i (σ j) := by
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = (w - w') (σ j) := hsumcoord
      _ = 0 := sub_eq_zero.mpr hcoord
  have hc0 : c = 0 := hBTinj (hmul.trans B.transpose.mulVec_zero.symm)
  rw [hc0] at hc
  simp at hc
  exact sub_eq_zero.mp hc.symm

/-- A finite subset of a coordinate box has at most `|Q|^m` points when
its real span has dimension `m`.  The proof chooses a nonsingular
coordinate minor of a basis and projects to those coordinates. -/
lemma finite_box_card_le_pow_finrank
    {D Q : Type*} [Finite D] [Fintype Q] [Nonempty Q]
    (decode : Q → ℤ) (hdecode : Function.Injective decode)
    (S : Finset (D → Q)) :
    S.card ≤ Fintype.card Q ^
      Module.finrank ℝ (Submodule.span ℝ
        (Set.range fun q : ↑S ↦ fun j ↦ (decode (q.1 j) : ℝ))) := by
  classical
  let _ := Fintype.ofFinite D
  let v : ↑S → D → ℝ := fun q j ↦ (decode (q.1 j) : ℝ)
  let m := Module.finrank ℝ (Submodule.span ℝ (Set.range v))
  obtain ⟨f, hfmem, hfspan, hfind⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range v)
  obtain ⟨σ, hσdet⟩ := exists_ne_zero_coordinate_minor f hfind
  let projection : ↑S → (Fin m → Q) := fun q i ↦ q.1 (σ i)
  have hproj : Function.Injective projection := by
    intro q q' hqq'
    apply Subtype.ext
    have hinj := coordinate_restriction_injOn_span f σ hσdet
    have hvq : v q ∈ Submodule.span ℝ (Set.range f) := by
      rw [hfspan]
      exact Submodule.subset_span (Set.mem_range_self q)
    have hvq' : v q' ∈ Submodule.span ℝ (Set.range f) := by
      rw [hfspan]
      exact Submodule.subset_span (Set.mem_range_self q')
    have hcoords : (fun w : D → ℝ ↦ fun i ↦ w (σ i)) (v q) =
        (fun w : D → ℝ ↦ fun i ↦ w (σ i)) (v q') := by
      funext i
      change (decode (q.1 (σ i)) : ℝ) = (decode (q'.1 (σ i)) : ℝ)
      have hi := congrFun hqq' i
      change q.1 (σ i) = q'.1 (σ i) at hi
      rw [hi]
    have hvEq : v q = v q' := hinj hvq hvq' hcoords
    funext j
    apply hdecode
    have hj := congrFun hvEq j
    change (decode (q.1 j) : ℝ) = (decode (q'.1 j) : ℝ) at hj
    exact_mod_cast hj
  calc
    S.card = Fintype.card ↑S := by simp
    _ ≤ Fintype.card (Fin m → Q) :=
      Fintype.card_le_of_injective projection hproj
    _ = Fintype.card Q ^ m := by simp
    _ = Fintype.card Q ^
        Module.finrank ℝ (Submodule.span ℝ
          (Set.range fun q : ↑S ↦ fun j ↦ (decode (q.1 j) : ℝ))) := rfl

end

end Erdos984
