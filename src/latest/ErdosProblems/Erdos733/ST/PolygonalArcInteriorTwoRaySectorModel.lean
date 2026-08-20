import Mathlib.Analysis.Convex.PathConnected
import ErdosProblems.Erdos733.ST.Preamble

open Set

noncomputable section

-- [TABLET NODE: PolygonalArcInteriorTwoRaySectorModel]
lemma PolygonalArcInteriorTwoRaySectorModel (r c s : ℝ) (hr : 0 < r)
    (hpos : 0 < s ∨ s = 0 ∧ c < 0) :
    let cross : (Fin 2 → ℝ) → ℝ := fun z => c * z 1 - s * z 0
    let C : Set (Fin 2 → ℝ) := Metric.ball (0 : Fin 2 → ℝ) r
    let G0 : Set (Fin 2 → ℝ) := {z | z ∈ C ∧ z 1 = 0 ∧ 0 < z 0}
    let Gv : Set (Fin 2 → ℝ) :=
      {z | z ∈ C ∧ ∃ t : ℝ, 0 < t ∧ z 0 = t * c ∧ z 1 = t * s}
    let L : Set (Fin 2 → ℝ) := {z | z ∈ C ∧ 0 < z 1 ∧ cross z < 0}
    let R : Set (Fin 2 → ℝ) := {z | z ∈ C ∧ (z 1 < 0 ∨ 0 < cross z)}
    IsOpen C ∧ IsOpen L ∧ IsOpen R ∧
      IsConnected L ∧ IsConnected R ∧
      Disjoint L R ∧
      Disjoint L (G0 ∪ Gv ∪ ({0} : Set (Fin 2 → ℝ))) ∧
      Disjoint R (G0 ∪ Gv ∪ ({0} : Set (Fin 2 → ℝ))) ∧
      C \ (G0 ∪ Gv ∪ ({0} : Set (Fin 2 → ℝ))) = L ∪ R := by
-- BODY
  intro cross C G0 Gv L R
  have hcoord0 : Continuous fun z : Fin 2 → ℝ => z 0 :=
    continuous_apply 0
  have hcoord1 : Continuous fun z : Fin 2 → ℝ => z 1 :=
    continuous_apply 1
  have hcross_cont : Continuous fun z : Fin 2 → ℝ => cross z := by
    dsimp [cross]
    exact (continuous_const.mul hcoord1).sub (continuous_const.mul hcoord0)
  have hC_open : IsOpen C := by
    dsimp [C]
    exact Metric.isOpen_ball
  have hL_open : IsOpen L := by
    dsimp [L]
    exact hC_open.inter ((isOpen_lt continuous_const hcoord1).inter
      (isOpen_lt hcross_cont continuous_const))
  let Rneg : Set (Fin 2 → ℝ) := {z | z ∈ C ∧ z 1 < 0}
  let Rcross : Set (Fin 2 → ℝ) := {z | z ∈ C ∧ 0 < cross z}
  have hR_eq : R = Rneg ∪ Rcross := by
    ext z
    dsimp [R, Rneg, Rcross]
    constructor
    · rintro ⟨hzC, hz | hz⟩
      · exact Or.inl ⟨hzC, hz⟩
      · exact Or.inr ⟨hzC, hz⟩
    · rintro (⟨hzC, hz⟩ | ⟨hzC, hz⟩)
      · exact ⟨hzC, Or.inl hz⟩
      · exact ⟨hzC, Or.inr hz⟩
  have hRneg_open : IsOpen Rneg := by
    dsimp [Rneg]
    exact hC_open.inter (isOpen_lt hcoord1 continuous_const)
  have hRcross_open : IsOpen Rcross := by
    dsimp [Rcross]
    exact hC_open.inter (isOpen_lt continuous_const hcross_cont)
  have hR_open : IsOpen R := by
    rw [hR_eq]
    exact hRneg_open.union hRcross_open
  let X : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 0
  let Y : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 1
  let Cross : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := c • Y - s • X
  have hC_conv : Convex ℝ C := by
    dsimp [C]
    exact convex_ball _ _
  have hYgt : Convex ℝ {z : Fin 2 → ℝ | (0 : ℝ) < Y z} :=
    convex_halfSpace_gt Y.isLinear 0
  have hYlt : Convex ℝ {z : Fin 2 → ℝ | Y z < (0 : ℝ)} :=
    convex_halfSpace_lt Y.isLinear 0
  have hCrossGt : Convex ℝ {z : Fin 2 → ℝ | (0 : ℝ) < Cross z} :=
    convex_halfSpace_gt Cross.isLinear 0
  have hCrossLt : Convex ℝ {z : Fin 2 → ℝ | Cross z < (0 : ℝ)} :=
    convex_halfSpace_lt Cross.isLinear 0
  have hL_conv : Convex ℝ L := by
    simpa [L, cross, X, Y, Cross, Set.inter_def, sub_eq_add_neg, add_comm,
      add_left_comm, add_assoc] using ((hC_conv.inter hYgt).inter (hC_conv.inter hCrossLt))
  have hRneg_conv : Convex ℝ Rneg := by
    simpa [Rneg, C, Y, Set.inter_def] using (hC_conv.inter hYlt)
  have hRcross_conv : Convex ℝ Rcross := by
    simpa [Rcross, cross, X, Y, Cross, Set.inter_def, sub_eq_add_neg, add_comm,
      add_left_comm, add_assoc] using (hC_conv.inter hCrossGt)
  have scaled_mem (w : Fin 2 → ℝ) :
      let δ : ℝ := r / (2 * (‖w‖ + 1))
      0 < δ ∧ δ • w ∈ C := by
    intro δ
    have hden_pos : 0 < 2 * (‖w‖ + 1) := by positivity
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      positivity
    constructor
    · exact hδ_pos
    · dsimp [C]
      rw [Metric.mem_ball, dist_zero_right, norm_smul]
      rw [Real.norm_eq_abs, abs_of_pos hδ_pos]
      dsimp [δ]
      rw [div_mul_eq_mul_div]
      rw [div_lt_iff₀ hden_pos]
      nlinarith [hr, norm_nonneg w]
  have hL_nonempty : L.Nonempty := by
    rcases hpos with hs | ⟨hs0, hc⟩
    · let w : Fin 2 → ℝ := fun i => if i = 0 then c + 1 else s
      let δ : ℝ := r / (2 * (‖w‖ + 1))
      have hδ := scaled_mem w
      dsimp only at hδ
      refine ⟨δ • w, ?_⟩
      dsimp [L]
      constructor
      · exact hδ.2
      constructor
      · simp [w]
        positivity
      · have hcross : cross (δ • w) = -δ * s := by
          dsimp [cross]
          simp [w]
          ring
        rw [hcross]
        nlinarith [hδ.1, hs]
    · let w : Fin 2 → ℝ := Pi.single 1 (1 : ℝ)
      let δ : ℝ := r / (2 * (‖w‖ + 1))
      have hδ := scaled_mem w
      dsimp only at hδ
      refine ⟨δ • w, ?_⟩
      dsimp [L]
      constructor
      · exact hδ.2
      constructor
      · simpa [w] using hδ.1
      · have hcross : cross (δ • w) = c * δ := by
          simpa [cross, w, hs0, mul_comm]
        rw [hcross]
        nlinarith [hδ.1, hc]
  have hRneg_nonempty : Rneg.Nonempty := by
    let w : Fin 2 → ℝ := Pi.single 1 (-1 : ℝ)
    let δ : ℝ := r / (2 * (‖w‖ + 1))
    have hδ := scaled_mem w
    dsimp only at hδ
    refine ⟨δ • w, ?_⟩
    dsimp [Rneg]
    constructor
    · exact hδ.2
    · simp [w]
      linarith [hδ.1]
  have hRcross_nonempty : Rcross.Nonempty := by
    rcases hpos with hs | ⟨hs0, hc⟩
    · let w : Fin 2 → ℝ := Pi.single 0 (-1 : ℝ)
      let δ : ℝ := r / (2 * (‖w‖ + 1))
      have hδ := scaled_mem w
      dsimp only at hδ
      refine ⟨δ • w, ?_⟩
      dsimp [Rcross]
      constructor
      · exact hδ.2
      · have hcross : cross (δ • w) = s * δ := by
          simpa [cross, w, mul_comm]
        rw [hcross]
        positivity
    · let w : Fin 2 → ℝ := Pi.single 1 (-1 : ℝ)
      let δ : ℝ := r / (2 * (‖w‖ + 1))
      have hδ := scaled_mem w
      dsimp only at hδ
      refine ⟨δ • w, ?_⟩
      dsimp [Rcross]
      constructor
      · exact hδ.2
      · have hcross : cross (δ • w) = -c * δ := by
          simpa [cross, w, hs0, mul_comm]
        rw [hcross]
        nlinarith [hδ.1, hc]
  have hR_inter_nonempty : (Rneg ∩ Rcross).Nonempty := by
    rcases hpos with hs | ⟨hs0, hc⟩
    · let w : Fin 2 → ℝ := fun i => if i = 0 then -(c + 1) else -s
      let δ : ℝ := r / (2 * (‖w‖ + 1))
      have hδ := scaled_mem w
      dsimp only at hδ
      refine ⟨δ • w, ?_, ?_⟩
      · dsimp [Rneg]
        constructor
        · exact hδ.2
        · simp [w]
          nlinarith [hδ.1, hs]
      · dsimp [Rcross]
        constructor
        · exact hδ.2
        · have hcross : cross (δ • w) = δ * s := by
            dsimp [cross]
            simp [w]
            ring
          rw [hcross]
          positivity
    · let w : Fin 2 → ℝ := Pi.single 1 (-1 : ℝ)
      let δ : ℝ := r / (2 * (‖w‖ + 1))
      have hδ := scaled_mem w
      dsimp only at hδ
      refine ⟨δ • w, ?_, ?_⟩
      · dsimp [Rneg]
        constructor
        · exact hδ.2
        · simp [w]
          linarith [hδ.1]
      · dsimp [Rcross]
        constructor
        · exact hδ.2
        · have hcross : cross (δ • w) = -c * δ := by
            simpa [cross, w, hs0, mul_comm]
          rw [hcross]
          nlinarith [hδ.1, hc]
  have hL_connected : IsConnected L :=
    hL_conv.isConnected hL_nonempty
  have hRneg_connected : IsConnected Rneg :=
    hRneg_conv.isConnected hRneg_nonempty
  have hRcross_connected : IsConnected Rcross :=
    hRcross_conv.isConnected hRcross_nonempty
  have hR_connected : IsConnected R := by
    rw [hR_eq]
    exact IsConnected.union hR_inter_nonempty hRneg_connected hRcross_connected
  let Bad : Set (Fin 2 → ℝ) := G0 ∪ Gv ∪ ({0} : Set (Fin 2 → ℝ))
  have hcross_Gv {z : Fin 2 → ℝ} (hz : z ∈ Gv) : cross z = 0 := by
    dsimp [Gv] at hz
    rcases hz with ⟨_, t, _ht, hx, hy⟩
    dsimp [cross]
    rw [hx, hy]
    ring
  have hnot_yneg_Gv {z : Fin 2 → ℝ} (hyneg : z 1 < 0) (hz : z ∈ Gv) :
      False := by
    dsimp [Gv] at hz
    rcases hz with ⟨_, t, ht, _hx, hy⟩
    rcases hpos with hs | ⟨hs0, _hc⟩
    · rw [hy] at hyneg
      nlinarith
    · rw [hy, hs0] at hyneg
      nlinarith
  have hcross_G0_nonpos {z : Fin 2 → ℝ} (hz : z ∈ G0) :
      cross z ≤ 0 := by
    dsimp [G0] at hz
    rcases hz with ⟨_, hy0, hxpos⟩
    rcases hpos with hs | ⟨hs0, _hc⟩
    · dsimp [cross]
      rw [hy0]
      nlinarith
    · dsimp [cross]
      rw [hy0, hs0]
      linarith
  have hLR_disjoint : Disjoint L R := by
    rw [Set.disjoint_left]
    intro z hzL hzR
    dsimp [L] at hzL
    dsimp [R] at hzR
    rcases hzL with ⟨_, hypos, hqneg⟩
    rcases hzR with ⟨_, hyneg | hqpos⟩
    · linarith
    · linarith
  have hL_bad_disjoint : Disjoint L Bad := by
    rw [Set.disjoint_left]
    intro z hzL hzBad
    dsimp [L] at hzL
    rcases hzL with ⟨_, hypos, hqneg⟩
    dsimp [Bad] at hzBad
    rcases hzBad with (hzG0 | hzGv) | hzZero
    · dsimp [G0] at hzG0
      rcases hzG0 with ⟨_, hy0, _⟩
      linarith
    · have hq := hcross_Gv hzGv
      linarith
    · rw [Set.mem_singleton_iff] at hzZero
      subst z
      simp at hypos
  have hR_bad_disjoint : Disjoint R Bad := by
    rw [Set.disjoint_left]
    intro z hzR hzBad
    dsimp [R] at hzR
    rcases hzR with ⟨_, hyneg | hqpos⟩
    · dsimp [Bad] at hzBad
      rcases hzBad with (hzG0 | hzGv) | hzZero
      · dsimp [G0] at hzG0
        rcases hzG0 with ⟨_, hy0, _⟩
        linarith
      · exact hnot_yneg_Gv hyneg hzGv
      · rw [Set.mem_singleton_iff] at hzZero
        subst z
        simp at hyneg
    · dsimp [Bad] at hzBad
      rcases hzBad with (hzG0 | hzGv) | hzZero
      · have hq_nonpos := hcross_G0_nonpos hzG0
        linarith
      · have hq := hcross_Gv hzGv
        linarith
      · rw [Set.mem_singleton_iff] at hzZero
        subst z
        simp [cross] at hqpos
  have hcover : C \ Bad = L ∪ R := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨hzC, hznotBad⟩
      have hnotG0 : z ∉ G0 := by
        intro h
        exact hznotBad (by dsimp [Bad]; exact Or.inl (Or.inl h))
      have hnotGv : z ∉ Gv := by
        intro h
        exact hznotBad (by dsimp [Bad]; exact Or.inl (Or.inr h))
      have hnotZero : z ≠ 0 := by
        intro hzero
        exact hznotBad (by
          dsimp [Bad]
          exact Or.inr (by simpa [hzero]))
      rcases lt_trichotomy (z 1) 0 with hyneg | hyeq | hypos
      · right
        dsimp [R]
        exact ⟨hzC, Or.inl hyneg⟩
      · rcases lt_trichotomy (z 0) 0 with hxneg | hxeq | hxpos
        · rcases hpos with hs | ⟨hs0, hc⟩
          · right
            dsimp [R]
            constructor
            · exact hzC
            · right
              dsimp [cross]
              rw [hyeq]
              nlinarith
          · exfalso
            apply hnotGv
            refine ⟨hzC, z 0 / c, ?_, ?_, ?_⟩
            · exact div_pos_of_neg_of_neg hxneg hc
            · field_simp [ne_of_lt hc]
            · rw [hyeq, hs0, mul_zero]
        · exfalso
          apply hnotZero
          ext i
          fin_cases i <;> simp [hxeq, hyeq]
        · exfalso
          apply hnotG0
          dsimp [G0]
          exact ⟨hzC, hyeq, hxpos⟩
      · rcases lt_trichotomy (cross z) 0 with hqneg | hqeq | hqpos
        · left
          dsimp [L]
          exact ⟨hzC, hypos, hqneg⟩
        · exfalso
          rcases hpos with hs | ⟨hs0, hc⟩
          · apply hnotGv
            refine ⟨hzC, z 1 / s, ?_, ?_, ?_⟩
            · exact div_pos hypos hs
            · have hqeq' : c * z 1 - s * z 0 = 0 := by
                simpa [cross] using hqeq
              field_simp [ne_of_gt hs]
              nlinarith
            · field_simp [ne_of_gt hs]
          · have hqeq' : c * z 1 = 0 := by
              simpa [cross, hs0] using hqeq
            nlinarith
        · right
          dsimp [R]
          exact ⟨hzC, Or.inr hqpos⟩
    · intro hz
      constructor
      · rcases hz with hzL | hzR
        · dsimp [L] at hzL
          exact hzL.1
        · dsimp [R] at hzR
          exact hzR.1
      · intro hzBad
        rcases hz with hzL | hzR
        · exact (Set.disjoint_left.mp hL_bad_disjoint) hzL hzBad
        · exact (Set.disjoint_left.mp hR_bad_disjoint) hzR hzBad
  refine ⟨hC_open, hL_open, hR_open, hL_connected, hR_connected, hLR_disjoint, ?_, ?_, ?_⟩
  · simpa [Bad] using hL_bad_disjoint
  · simpa [Bad] using hR_bad_disjoint
  · simpa [Bad] using hcover
