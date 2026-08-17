/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos223.CarrierOddSeedGeometry

/-!
# Exact cross-unit cores in odd dimensions

This module constructs the adapted orthonormal seed frame and projection
center for an exact cross-unit multipartite core, then upgrades the core to
a weak odd carrier when there are at least four parts.
-/

open scoped RealInnerProductSpace

namespace Erdos223.CarrierOdd

noncomputable section

def frameIndexEquiv' (p : ℕ) : (Fin p × Fin 2) ⊕ Fin 1 ≃ Fin (2 * p + 1) :=
  ((Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin 1))).trans
    finSumFinEquiv).trans (finCongr (by omega))

@[simp] lemma frameIndexEquiv'_left_zero (p : ℕ) (i : Fin p) :
    frameIndexEquiv' p (Sum.inl (i, 0)) = planeFirst p i := by
  apply Fin.ext
  simp [frameIndexEquiv', planeFirst, finProdFinEquiv, finSumFinEquiv]

@[simp] lemma frameIndexEquiv'_left_one (p : ℕ) (i : Fin p) :
    frameIndexEquiv' p (Sum.inl (i, 1)) = planeSecond p i := by
  apply Fin.ext
  simp [frameIndexEquiv', planeSecond, finProdFinEquiv, finSumFinEquiv]
  omega

@[simp] lemma frameIndexEquiv'_right_zero (p : ℕ) :
    frameIndexEquiv' p (Sum.inr 0) = axisIndex p := by
  apply Fin.ext
  simp [frameIndexEquiv', axisIndex, finProdFinEquiv, finSumFinEquiv]

def directionSubspace {p : ℕ}
    (d : Fin p × Fin 2 → Point (2 * p + 1)) (i : Fin p) :
    Submodule ℝ (Point (2 * p + 1)) :=
  Submodule.span ℝ (Set.range fun k : Fin 2 ↦ d (i, k))

def directionSpan {p : ℕ}
    (d : Fin p × Fin 2 → Point (2 * p + 1)) :
    Submodule ℝ (Point (2 * p + 1)) :=
  Submodule.span ℝ (Set.range d)

theorem exists_orthonormal_frame_of_orthogonal_directions
    {p : ℕ} (d : Fin p × Fin 2 → Point (2 * p + 1))
    (hd : LinearIndependent ℝ d)
    (hortho : ∀ {i j : Fin p}, i ≠ j → ∀ k l,
      inner ℝ (d (i, k)) (d (j, l)) = 0) :
    ∃ frame : Fin (2 * p + 1) → Point (2 * p + 1),
      Orthonormal ℝ frame ∧
      (∀ i (k : Fin 2), frame (if k = 0 then planeFirst p i else planeSecond p i) ∈
        directionSubspace d i) ∧
      frame (axisIndex p) ∈ (directionSpan d)ᗮ := by
  let U : Fin p → Submodule ℝ (Point (2 * p + 1)) := directionSubspace d
  let W : Submodule ℝ (Point (2 * p + 1)) := directionSpan d
  have hblock (i : Fin p) : LinearIndependent ℝ (fun k : Fin 2 ↦ d (i, k)) := by
    exact hd.comp (fun k ↦ (i, k)) (by intro k l h; exact congrArg Prod.snd h)
  have hUfin (i : Fin p) : Module.finrank ℝ (U i) = 2 := by
    change Module.finrank ℝ (Submodule.span ℝ
      (Set.range fun k : Fin 2 ↦ d (i, k))) = 2
    rw [finrank_span_eq_card (hblock i)]
    simp
  have hUortho {i j : Fin p} (hij : i ≠ j) : U i ⟂ U j := by
    change Submodule.span ℝ (Set.range fun k : Fin 2 ↦ d (i, k)) ⟂
      Submodule.span ℝ (Set.range fun k : Fin 2 ↦ d (j, k))
    rw [Submodule.isOrtho_span]
    rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
    exact hortho hij k l
  have hUle (i : Fin p) : U i ≤ W := by
    change Submodule.span ℝ (Set.range fun k : Fin 2 ↦ d (i, k)) ≤
      Submodule.span ℝ (Set.range d)
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact Submodule.subset_span ⟨(i, k), rfl⟩
  have hLfin : Module.finrank ℝ Wᗮ = 1 := by
    exact finrank_orthogonal_span_partDirections_eq_one d hd
  let bU (i : Fin p) : OrthonormalBasis (Fin 2) ℝ (U i) :=
    (stdOrthonormalBasis ℝ (U i)).reindex (finCongr (hUfin i))
  let bL : OrthonormalBasis (Fin 1) ℝ Wᗮ :=
    (stdOrthonormalBasis ℝ Wᗮ).reindex (finCongr hLfin)
  let raw : (Fin p × Fin 2) ⊕ Fin 1 → Point (2 * p + 1) :=
    Sum.elim (fun ik ↦ (bU ik.1 ik.2 : Point (2 * p + 1)))
      (fun k ↦ (bL k : Point (2 * p + 1)))
  have hraw : Orthonormal ℝ raw := by
    rw [orthonormal_iff_ite]
    intro a b
    cases a with
    | inl ik =>
        cases b with
        | inl jl =>
            rcases ik with ⟨i, k⟩
            rcases jl with ⟨j, l⟩
            by_cases hij : i = j
            · subst j
              simpa [raw] using
                (orthonormal_iff_ite.mp (bU i).orthonormal k l)
            · have hz := hUortho hij
              have hz' := (Submodule.isOrtho_iff_inner_eq.mp hz)
                (bU i k : Point (2 * p + 1)) (bU i k).property
                (bU j l : Point (2 * p + 1)) (bU j l).property
              simp [raw, hij, hz']
        | inr l =>
            have hm : (bL l : Point (2 * p + 1)) ∈ Wᗮ := (bL l).property
            have hu : (bU ik.1 ik.2 : Point (2 * p + 1)) ∈ W :=
              hUle ik.1 (bU ik.1 ik.2).property
            have hz := ((Submodule.mem_orthogonal' W _).mp hm) _ hu
            rw [real_inner_comm] at hz
            simpa [raw] using hz
    | inr k =>
        cases b with
        | inl jl =>
            have hm : (bL k : Point (2 * p + 1)) ∈ Wᗮ := (bL k).property
            have hu : (bU jl.1 jl.2 : Point (2 * p + 1)) ∈ W :=
              hUle jl.1 (bU jl.1 jl.2).property
            have hz := ((Submodule.mem_orthogonal' W _).mp hm) _ hu
            simpa [raw] using hz
        | inr l =>
            simpa [raw] using (orthonormal_iff_ite.mp bL.orthonormal k l)
  let frame : Fin (2 * p + 1) → Point (2 * p + 1) :=
    raw ∘ (frameIndexEquiv' p).symm
  have hframe : Orthonormal ℝ frame :=
    hraw.comp (frameIndexEquiv' p).symm (frameIndexEquiv' p).symm.injective
  refine ⟨frame, hframe, ?_, ?_⟩
  · intro i k
    fin_cases k
    · change frame (planeFirst p i) ∈ U i
      have he := (frameIndexEquiv' p).symm_apply_apply (Sum.inl (i, 0))
      change raw ((frameIndexEquiv' p).symm (planeFirst p i)) ∈ U i
      rw [← frameIndexEquiv'_left_zero p i, he]
      exact (bU i 0).property
    · change frame (planeSecond p i) ∈ U i
      have he := (frameIndexEquiv' p).symm_apply_apply (Sum.inl (i, 1))
      change raw ((frameIndexEquiv' p).symm (planeSecond p i)) ∈ U i
      rw [← frameIndexEquiv'_left_one p i, he]
      exact (bU i 1).property
  · have he := (frameIndexEquiv' p).symm_apply_apply (Sum.inr (0 : Fin 1))
    change raw ((frameIndexEquiv' p).symm (axisIndex p)) ∈ Wᗮ
    rw [← frameIndexEquiv'_right_zero p, he]
    exact (bL 0).property

private lemma inner_sub_sub_eq_zero_of_four_unit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {a b c e : E}
    (hac : dist a c = 1) (hae : dist a e = 1)
    (hbc : dist b c = 1) (hbe : dist b e = 1) :
    inner ℝ (a - b) (c - e) = 0 := by
  have h_ac : inner ℝ (a - c) (a - c) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hac]
    norm_num
  have h_ae : inner ℝ (a - e) (a - e) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hae]
    norm_num
  have h_bc : inner ℝ (b - c) (b - c) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hbc]
    norm_num
  have h_be : inner ℝ (b - e) (b - e) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hbe]
    norm_num
  rw [real_inner_sub_sub_self] at h_ac h_ae h_bc h_be
  simp only [inner_sub_left, inner_sub_right] at ⊢
  linarith

noncomputable def otherPart {p : ℕ} (hp : 2 ≤ p) (j : Fin p) : Fin p :=
  Classical.choose (Fintype.exists_ne_of_one_lt_card (by
    rw [Fintype.card_fin]
    omega) j)

lemma otherPart_ne {p : ℕ} (hp : 2 ≤ p) (j : Fin p) : otherPart hp j ≠ j :=
  Classical.choose_spec (Fintype.exists_ne_of_one_lt_card (by
    rw [Fintype.card_fin]
    omega) j)

/-- Cross-unit triples determine an orthonormal seed frame and a translation
such that every point equidistant from all triples outside class `i` is
supported on the `i`th coordinate plane plus the leftover axis. -/
theorem exists_axisPlane_coordinates_of_cross_unit_triples
    {p : ℕ} (hp : 2 ≤ p)
    (x : Fin p → Fin 3 → Point (2 * p + 1))
    (hinj : ∀ i, Function.Injective (x i))
    (hcross : ∀ {i j : Fin p}, i ≠ j → ∀ a b,
      dist (x i a) (x j b) = 1) :
    ∃ baseCenter : Point (2 * p + 1),
      ∃ coord : Point (2 * p + 1) ≃ₗᵢ[ℝ] Point (2 * p + 1),
        ∀ (i : Fin p) (q : Point (2 * p + 1)),
          (∀ j, j ≠ i → ∀ a, dist q (x j a) = 1) →
          InAxisPlane i (coord.symm (q - baseCenter)) := by
  let d : Fin p × Fin 2 → Point (2 * p + 1) := partDirectionGeneric x
  let U : Fin p → Submodule ℝ (Point (2 * p + 1)) := directionSubspace d
  let W : Submodule ℝ (Point (2 * p + 1)) := directionSpan d
  have hd : LinearIndependent ℝ d :=
    partDirections_linearIndependent_generic hp hinj hcross
  have hdortho : ∀ {i j : Fin p}, i ≠ j → ∀ k l,
      inner ℝ (d (i, k)) (d (j, l)) = 0 := by
    intro i j hij k l
    exact inner_sub_sub_eq_zero_of_four_unit
      (hcross hij k.succ l.succ) (hcross hij k.succ 0)
      (hcross hij 0 l.succ) (hcross hij 0 0)
  have hUortho {i j : Fin p} (hij : i ≠ j) : U i ⟂ U j := by
    change Submodule.span ℝ (Set.range fun k : Fin 2 ↦ d (i, k)) ⟂
      Submodule.span ℝ (Set.range fun k : Fin 2 ↦ d (j, k))
    rw [Submodule.isOrtho_span]
    rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
    exact hdortho hij k l
  obtain ⟨frame, hframe, hframeU, hframeAxis⟩ :=
    exists_orthonormal_frame_of_orthogonal_directions d hd hdortho
  let coord := coordOfOrthonormalFrame frame hframe
  let reference : Fin p → Point (2 * p + 1) :=
    fun j ↦ x (otherPart hp j) 0
  let baseCenter : Point (2 * p + 1) :=
    ∑ j : Fin p, (U j).starProjection (reference j)
  have hreference (j : Fin p) (a : Fin 3) :
      dist (reference j) (x j a) = 1 := by
    exact hcross (otherPart_ne hp j) 0 a
  have horthogonal_to_U (i : Fin p) (q : Point (2 * p + 1))
      (hq : ∀ j, j ≠ i → ∀ a, dist q (x j a) = 1)
      (j : Fin p) (hji : j ≠ i) : q - reference j ∈ (U j)ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro v hv
    change v ∈ Submodule.span ℝ
      (Set.range fun k : Fin 2 ↦ d (j, k)) at hv
    refine Submodule.span_induction
      (p := fun v _ ↦ inner ℝ (q - reference j) v = 0) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨k, rfl⟩
      dsimp [d, partDirectionGeneric]
      have hz := inner_sub_sub_eq_zero_of_four_unit
        (hq j hji 0) (hq j hji k.succ)
        (hreference j 0) (hreference j k.succ)
      rw [show x j k.succ - x j 0 = -(x j 0 - x j k.succ) by abel,
        inner_neg_right, hz, neg_zero]
    · exact inner_zero_right _
    · intro u v _ _ hu hv
      rw [inner_add_right, hu, hv, add_zero]
    · intro a v _ hv
      rw [real_inner_smul_right, hv, mul_zero]
  have hbase_inner (i : Fin p) (q : Point (2 * p + 1))
      (hq : ∀ j, j ≠ i → ∀ a, dist q (x j a) = 1)
      (j : Fin p) (hji : j ≠ i) (v : Point (2 * p + 1)) (hv : v ∈ U j) :
      inner ℝ (q - baseCenter) v = 0 := by
    have hqref := ((Submodule.mem_orthogonal' (U j) _).mp
      (horthogonal_to_U i q hq j hji)) v hv
    have hsum : inner ℝ baseCenter v = inner ℝ (reference j) v := by
      change inner ℝ (∑ k : Fin p, (U k).starProjection (reference k)) v = _
      rw [sum_inner]
      calc
        (∑ k : Fin p, inner ℝ ((U k).starProjection (reference k)) v) =
            inner ℝ ((U j).starProjection (reference j)) v := by
          apply Finset.sum_eq_single j
          · intro k _ hkj
            have hpj : (U k).starProjection (reference k) ∈ U k :=
              (U k).starProjection_apply_mem _
            exact (Submodule.isOrtho_iff_inner_eq.mp (hUortho hkj))
              _ hpj v hv
          · intro hj
            exact (hj (Finset.mem_univ j)).elim
        _ = inner ℝ (reference j) v := by
          have hz := (U j).starProjection_inner_eq_zero (reference j) v hv
          rw [inner_sub_left] at hz
          exact (sub_eq_zero.mp hz).symm
    rw [inner_sub_left, hsum]
    simpa [inner_sub_left] using hqref
  refine ⟨baseCenter, coord, ?_⟩
  intro i q hq
  intro a haf has haa
  have hneaxis : a ≠ axisIndex p := haa
  have hleft : ∃ ik : Fin p × Fin 2,
      (frameIndexEquiv' p).symm a = Sum.inl ik := by
    cases hidx : (frameIndexEquiv' p).symm a with
    | inl ik => exact ⟨ik, rfl⟩
    | inr k =>
        have hk0 : k = 0 := Subsingleton.elim _ _
        subst k
        have haaxis : a = axisIndex p := by
          calc
            a = frameIndexEquiv' p ((frameIndexEquiv' p).symm a) :=
              ((frameIndexEquiv' p).apply_symm_apply a).symm
            _ = frameIndexEquiv' p (Sum.inr 0) := by rw [hidx]
            _ = axisIndex p := frameIndexEquiv'_right_zero p
        exact (hneaxis haaxis).elim
  obtain ⟨⟨j, k⟩, hjk⟩ := hleft
  have haidx : a = frameIndexEquiv' p (Sum.inl (j, k)) := by
    calc
      a = frameIndexEquiv' p ((frameIndexEquiv' p).symm a) :=
        ((frameIndexEquiv' p).apply_symm_apply a).symm
      _ = frameIndexEquiv' p (Sum.inl (j, k)) := by rw [hjk]
  have haeq : a = if k = 0 then planeFirst p j else planeSecond p j := by
    fin_cases k
    · simpa using haidx.trans (frameIndexEquiv'_left_zero p j)
    · simpa using haidx.trans (frameIndexEquiv'_left_one p j)
  have hji : j ≠ i := by
    intro h
    subst j
    fin_cases k
    · exact haf (by simpa using haeq)
    · exact has (by simpa using haeq)
  have hframeMem : frame a ∈ U j := by
    rw [haeq]
    exact hframeU j k
  have hinner := hbase_inner i q hq j hji (frame a) hframeMem
  have hmap := coord.inner_map_map (coord.symm (q - baseCenter))
    (EuclideanSpace.single a 1)
  rw [coord.apply_symm_apply, coordOfOrthonormalFrame_single] at hmap
  have hcoord : inner ℝ (coord.symm (q - baseCenter))
      (EuclideanSpace.single a 1) = coord.symm (q - baseCenter) a := by
    rw [EuclideanSpace.inner_single_right]
    simp
  rw [hcoord, hinner] at hmap
  exact hmap.symm

/-- A finite exact cross-unit partition in `Point (2p+1)` is contained in a
weak odd carrier as soon as there are at least four parts and every part
contains an injectively indexed triple. -/
theorem isWeakCarrierSet_of_exact_cross_unit_triples_four
    {p : ℕ} {A : Finset (Point (2 * p + 1))} (hp : 4 ≤ p)
    (part : {q : Point (2 * p + 1) // q ∈ A} → Fin p)
    (x : Fin p → Fin 3 → Point (2 * p + 1))
    (hinj : ∀ i, Function.Injective (x i))
    (hcross : ∀ {i j : Fin p}, i ≠ j → ∀ a b,
      dist (x i a) (x j b) = 1)
    (hcomplete : ∀ (q : {q : Point (2 * p + 1) // q ∈ A}) j,
      j ≠ part q → ∀ a, dist q.1 (x j a) = 1) :
    IsWeakCarrierSet (p := p) A := by
  obtain ⟨baseCenter, coord, hcoord⟩ :=
    exists_axisPlane_coordinates_of_cross_unit_triples (by omega : 2 ≤ p)
      x hinj hcross
  let seed : Fin p → Point (2 * p + 1) := fun j ↦ x j 0
  apply isWeakCarrierSet_of_axisPlane_cross_unit_four hp baseCenter coord part seed
  · intro q
    exact hcoord (part q) q.1 (hcomplete q)
  · intro j
    apply hcoord j (seed j)
    intro k hkj a
    exact hcross hkj.symm 0 a
  · intro i j hij
    exact hcross hij 0 0
  · intro q j hj
    exact hcomplete q j hj 0

/-- Assigned form of `isWeakCarrierSet_of_exact_cross_unit_triples_four`. -/
theorem exists_assignment_of_exact_cross_unit_triples_four
    {p : ℕ} {A : Finset (Point (2 * p + 1))} (hp : 4 ≤ p)
    (part : {q : Point (2 * p + 1) // q ∈ A} → Fin p)
    (x : Fin p → Fin 3 → Point (2 * p + 1))
    (hinj : ∀ i, Function.Injective (x i))
    (hcross : ∀ {i j : Fin p}, i ≠ j → ∀ a b,
      dist (x i a) (x j b) = 1)
    (hcomplete : ∀ (q : {q : Point (2 * p + 1) // q ∈ A}) j,
      j ≠ part q → ∀ a, dist q.1 (x j a) = 1) :
    Nonempty (Assignment (p := p) A) :=
  exists_assignment_of_isWeakCarrierSet
    (isWeakCarrierSet_of_exact_cross_unit_triples_four hp part x hinj hcross hcomplete)

end

end Erdos223.CarrierOdd
