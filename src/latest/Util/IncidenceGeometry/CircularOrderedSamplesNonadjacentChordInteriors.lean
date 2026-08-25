import Util.IncidenceGeometry.CircleLineNoThreePoints
import Mathlib.Data.List.FinRange
import Mathlib.Topology.Order.IntermediateValue

open Classical
noncomputable section

lemma CircularOrderedSamplesNonadjacentChordInteriors
    {m : ℕ}
    {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    {γ : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2)}
    (hγ_cont : Continuous γ)
    (hγ_inj : Function.Injective γ)
    (hγ_circle : ∀ t, dist (γ t) c = r)
    (params : Fin (m + 1) → Set.Icc (0 : ℝ) 1)
    (hparams_strict :
      ∀ ⦃i j : Fin (m + 1)⦄, i < j → params i < params j) :
    let vertices : List (EuclideanSpace ℝ (Fin 2)) :=
      List.ofFn (fun k : Fin (m + 1) => γ (params k))
    ∀ ⦃i j : ℕ⦄,
      (hi : i + 1 < vertices.length) →
      (hj : j + 1 < vertices.length) →
      i + 1 < j →
      Disjoint (openSegment ℝ vertices[i] vertices[i + 1])
        (openSegment ℝ vertices[j] vertices[j + 1]) := by
  classical
  let vertices : List (EuclideanSpace ℝ (Fin 2)) :=
    List.ofFn (fun k : Fin (m + 1) => γ (params k))
  have hvertices_length : vertices.length = m + 1 := by
    simp [vertices]
  have sample_ne_of_ne :
      ∀ {a b : ℕ} (ha : a < m + 1) (hb : b < m + 1), a ≠ b →
        γ (params ⟨a, ha⟩) ≠ γ (params ⟨b, hb⟩) := by
    intro a b ha hb hne heq
    have hp_eq : params ⟨a, ha⟩ = params ⟨b, hb⟩ := hγ_inj heq
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hltp : params ⟨a, ha⟩ < params ⟨b, hb⟩ :=
        hparams_strict (i := ⟨a, ha⟩) (j := ⟨b, hb⟩) (by simpa using hlt)
      rw [hp_eq] at hltp
      exact lt_irrefl _ hltp
    · have hltp : params ⟨b, hb⟩ < params ⟨a, ha⟩ :=
        hparams_strict (i := ⟨b, hb⟩) (j := ⟨a, ha⟩) (by simpa using hgt)
      rw [hp_eq] at hltp
      exact lt_irrefl _ hltp
  have sample_ne_of_lt :
      ∀ {a b : ℕ} (ha : a < m + 1) (hb : b < m + 1), a < b →
        γ (params ⟨a, ha⟩) ≠ γ (params ⟨b, hb⟩) := by
    intro a b ha hb hlt
    exact sample_ne_of_ne ha hb (Nat.ne_of_lt hlt)
  have hget :
      ∀ {a : ℕ} (haV : a < vertices.length),
        vertices[a] =
          γ (params ⟨a, by simpa [hvertices_length] using haV⟩) := by
    intro a haV
    dsimp [vertices]
    simp only [List.getElem_ofFn]
  change ∀ ⦃i j : ℕ⦄,
      (hi : i + 1 < vertices.length) →
      (hj : j + 1 < vertices.length) →
      i + 1 < j →
      Disjoint (openSegment ℝ vertices[i] vertices[i + 1])
        (openSegment ℝ vertices[j] vertices[j + 1])
  intro i j hi hj hgap
  rw [Set.disjoint_left]
  intro p hp_left hp_right
  have hi_len : i < vertices.length := by omega
  have hi1_len : i + 1 < vertices.length := hi
  have hj_len : j < vertices.length := by omega
  have hj1_len : j + 1 < vertices.length := hj
  let fi : Fin (m + 1) := ⟨i, by simpa [hvertices_length] using hi_len⟩
  let fi1 : Fin (m + 1) := ⟨i + 1, by simpa [hvertices_length] using hi1_len⟩
  let fj : Fin (m + 1) := ⟨j, by simpa [hvertices_length] using hj_len⟩
  let fj1 : Fin (m + 1) := ⟨j + 1, by simpa [hvertices_length] using hj1_len⟩
  let A : EuclideanSpace ℝ (Fin 2) := vertices[i]
  let B : EuclideanSpace ℝ (Fin 2) := vertices[i + 1]
  let C : EuclideanSpace ℝ (Fin 2) := vertices[j]
  let D : EuclideanSpace ℝ (Fin 2) := vertices[j + 1]
  have hA_eq : A = γ (params fi) := by
    dsimp [A, fi]
    exact hget hi_len
  have hB_eq : B = γ (params fi1) := by
    dsimp [B, fi1]
    exact hget hi1_len
  have hC_eq : C = γ (params fj) := by
    dsimp [C, fj]
    exact hget hj_len
  have hD_eq : D = γ (params fj1) := by
    dsimp [D, fj1]
    exact hget hj1_len
  have hA_ne_B : A ≠ B := by
    rw [hA_eq, hB_eq]
    exact sample_ne_of_lt (by simpa [fi] using fi.2)
      (by simpa [fi1] using fi1.2) (by omega)
  let side : EuclideanSpace ℝ (Fin 2) → ℝ := fun z =>
    (B 0 - A 0) * (z 1 - A 1) - (B 1 - A 1) * (z 0 - A 0)
  have hside_cont : Continuous side := by
    dsimp [side]
    fun_prop
  have side_lineMap_AB : ∀ t : ℝ, side (AffineMap.lineMap A B t) = 0 := by
    intro t
    dsimp [side]
    simp [AffineMap.lineMap_apply_module]
    ring
  have side_lineMap_CD :
      ∀ t : ℝ, side (AffineMap.lineMap C D t) =
        (1 - t) * side C + t * side D := by
    intro t
    dsimp [side]
    simp [AffineMap.lineMap_apply_module]
    ring
  have side_zero_mem_line :
      ∀ z : EuclideanSpace ℝ (Fin 2), side z = 0 → z ∈ line[ℝ, A, B] := by
    intro z hz
    dsimp [side] at hz
    by_cases hdx : B 0 - A 0 = 0
    · have hdy : B 1 - A 1 ≠ 0 := by
        intro hdy
        apply hA_ne_B
        apply PiLp.ext
        intro k
        fin_cases k
        · dsimp at hdx ⊢
          linarith
        · dsimp at hdy ⊢
          linarith
      let t : ℝ := (z 1 - A 1) / (B 1 - A 1)
      have hz_eq : z = AffineMap.lineMap A B t := by
        apply PiLp.ext
        intro k
        fin_cases k
        · dsimp [t]
          simp [AffineMap.lineMap_apply_module]
          have hside' : -(B 1 - A 1) * (z 0 - A 0) = 0 := by
            have h := hz
            rw [hdx] at h
            ring_nf at h ⊢
            exact h
          have hz0 : z 0 - A 0 = 0 := by
            exact (mul_eq_zero.mp hside').resolve_left (neg_ne_zero.mpr hdy)
          field_simp [hdy]
          nlinarith [hdx, hz0]
        · dsimp [t]
          simp [AffineMap.lineMap_apply_module]
          field_simp [hdy]
          ring
      rw [hz_eq]
      exact AffineMap.lineMap_mem_affineSpan_pair t A B
    · let t : ℝ := (z 0 - A 0) / (B 0 - A 0)
      have hz_eq : z = AffineMap.lineMap A B t := by
        apply PiLp.ext
        intro k
        fin_cases k
        · dsimp [t]
          simp [AffineMap.lineMap_apply_module]
          field_simp [hdx]
          ring
        · dsimp [t]
          simp [AffineMap.lineMap_apply_module]
          have hz1 :
              z 1 - A 1 = (B 1 - A 1) * ((z 0 - A 0) / (B 0 - A 0)) := by
            field_simp [hdx]
            nlinarith
          nlinarith
      rw [hz_eq]
      exact AffineMap.lineMap_mem_affineSpan_pair t A B
  have hp_side : side p = 0 := by
    have hp_seg : p ∈ segment ℝ A B := by
      dsimp [A, B]
      exact openSegment_subset_segment ℝ vertices[i] vertices[i + 1] hp_left
    rw [segment_eq_image_lineMap] at hp_seg
    rcases hp_seg with ⟨s, _hs, hs_eq⟩
    rw [← hs_eq]
    exact side_lineMap_AB s
  rw [openSegment_eq_image_lineMap] at hp_right
  rcases hp_right with ⟨t, ht, hp_eq⟩
  rw [← hp_eq] at hp_side
  have hcombo : (1 - t) * side C + t * side D = 0 := by
    rw [← side_lineMap_CD t]
    exact hp_side
  have ht_pos : 0 < t := ht.1
  have hone_sub_pos : 0 < 1 - t := by linarith [ht.2]
  have hparam_j_lt_j1 : params fj < params fj1 := by
    exact hparams_strict (i := fj) (j := fj1) (by simp [fj, fj1])
  have hparam_i_lt_j : params fi < params fj := by
    exact hparams_strict (i := fi) (j := fj) (by simp [fi, fj]; omega)
  have hparam_i1_lt_j : params fi1 < params fj := by
    exact hparams_strict (i := fi1) (j := fj) (by simpa [fi1, fj] using hgap)
  have hcont_on :
      ContinuousOn (fun u : Set.Icc (0 : ℝ) 1 => side (γ u))
        (Set.Icc (params fj) (params fj1)) :=
    (hside_cont.comp hγ_cont).continuousOn
  have root_exists :
      ∃ q ∈ Set.Icc (params fj) (params fj1),
        side (γ q) = 0 := by
    by_cases hle : side C ≤ side D
    · have hC_le_zero : side C ≤ 0 := by
        by_contra hnot
        have hC_pos : 0 < side C := lt_of_not_ge hnot
        have hD_pos : 0 < side D := lt_of_lt_of_le hC_pos hle
        nlinarith
      have hzero_le_D : 0 ≤ side D := by
        by_contra hnot
        have hD_neg : side D < 0 := lt_of_not_ge hnot
        have hC_neg : side C < 0 := lt_of_le_of_lt hle hD_neg
        nlinarith
      have hzero_mem :
          (0 : ℝ) ∈
            Set.Icc ((fun u : Set.Icc (0 : ℝ) 1 => side (γ u)) (params fj))
              ((fun u : Set.Icc (0 : ℝ) 1 => side (γ u)) (params fj1)) := by
        simpa [hC_eq, hD_eq] using And.intro hC_le_zero hzero_le_D
      rcases intermediate_value_Icc (le_of_lt hparam_j_lt_j1) hcont_on hzero_mem with
        ⟨q, hqmem, hqzero⟩
      exact ⟨q, hqmem, hqzero⟩
    · have hD_le_C : side D ≤ side C := le_of_not_ge hle
      have hD_le_zero : side D ≤ 0 := by
        by_contra hnot
        have hD_pos : 0 < side D := lt_of_not_ge hnot
        have hC_pos : 0 < side C := lt_of_lt_of_le hD_pos hD_le_C
        nlinarith
      have hzero_le_C : 0 ≤ side C := by
        by_contra hnot
        have hC_neg : side C < 0 := lt_of_not_ge hnot
        have hD_neg : side D < 0 := lt_of_le_of_lt hD_le_C hC_neg
        nlinarith
      have hzero_mem :
          (0 : ℝ) ∈
            Set.Icc ((fun u : Set.Icc (0 : ℝ) 1 => side (γ u)) (params fj1))
              ((fun u : Set.Icc (0 : ℝ) 1 => side (γ u)) (params fj)) := by
        simpa [hC_eq, hD_eq] using And.intro hD_le_zero hzero_le_C
      rcases intermediate_value_Icc' (le_of_lt hparam_j_lt_j1) hcont_on hzero_mem with
        ⟨q, hqmem, hqzero⟩
      exact ⟨q, hqmem, hqzero⟩
  rcases root_exists with ⟨q, hqmem, hqzero⟩
  have hq_line : γ q ∈ line[ℝ, A, B] := side_zero_mem_line (γ q) hqzero
  have hq_ne_A : γ q ≠ A := by
    intro hqA
    have hq_eq : q = params fi := by
      apply hγ_inj
      simpa [hA_eq] using hqA
    have hle_q : params fj ≤ q := hqmem.1
    rw [hq_eq] at hle_q
    exact (not_le_of_gt hparam_i_lt_j) hle_q
  have hq_ne_B : γ q ≠ B := by
    intro hqB
    have hq_eq : q = params fi1 := by
      apply hγ_inj
      simpa [hB_eq] using hqB
    have hle_q : params fj ≤ q := hqmem.1
    rw [hq_eq] at hle_q
    exact (not_le_of_gt hparam_i1_lt_j) hle_q
  exact CircleLineNoThreePoints
    (c := c) (r := r) (x := A) (y := B)
    (u := A) (v := B) (w := γ q)
    hA_ne_B
    (left_mem_affineSpan_pair ℝ A B)
    (right_mem_affineSpan_pair ℝ A B)
    hq_line
    (by rw [hA_eq]; exact hγ_circle _)
    (by rw [hB_eq]; exact hγ_circle _)
    (hγ_circle q)
    hA_ne_B hq_ne_A.symm hq_ne_B.symm
