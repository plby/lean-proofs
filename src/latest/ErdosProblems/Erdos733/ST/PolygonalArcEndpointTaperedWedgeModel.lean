import Mathlib.Analysis.Convex.PathConnected
import ErdosProblems.Erdos733.ST.Preamble

open Set

-- [TABLET NODE: PolygonalArcEndpointTaperedWedgeModel]
lemma PolygonalArcEndpointTaperedWedgeModel (a K : ℝ) (ha : 0 < a) (hK : 0 < K) :
    let C : Set (Fin 2 → ℝ) :=
      {z | 0 < z 0 ∧ z 0 < a ∧ 0 < z 1 + K * z 0 ∧ z 1 < K * z 0}
    let L : Set (Fin 2 → ℝ) :=
      {z | 0 < z 0 ∧ z 0 < a ∧ 0 < z 1 ∧ z 1 < K * z 0}
    let R : Set (Fin 2 → ℝ) :=
      {z | 0 < z 0 ∧ z 0 < a ∧ 0 < z 1 + K * z 0 ∧ z 1 < 0}
    let G : Set (Fin 2 → ℝ) :=
      {z | 0 < z 0 ∧ z 0 < a ∧ z 1 = 0}
    IsOpen C ∧ IsOpen L ∧ IsOpen R ∧
      IsConnected L ∧ IsConnected R ∧
      Disjoint L R ∧ (0 : Fin 2 → ℝ) ∉ C ∧
      G ⊆ C ∧ C \ G = L ∪ R := by
-- BODY
  intro C L R G
  have hcoord0 : Continuous fun z : Fin 2 → ℝ => z 0 :=
    continuous_apply 0
  have hcoord1 : Continuous fun z : Fin 2 → ℝ => z 1 :=
    continuous_apply 1
  have hlin2 : Continuous fun z : Fin 2 → ℝ => z 1 + K * z 0 :=
    hcoord1.add (continuous_const.mul hcoord0)
  have hlinUpper : Continuous fun z : Fin 2 → ℝ => z 1 - K * z 0 :=
    hcoord1.sub (continuous_const.mul hcoord0)
  have hC_open : IsOpen C := by
    dsimp [C]
    repeat' apply IsOpen.inter
    · exact isOpen_lt continuous_const hcoord0
    · exact isOpen_lt hcoord0 continuous_const
    · exact isOpen_lt continuous_const hlin2
    · exact isOpen_lt hcoord1 (continuous_const.mul hcoord0)
  have hL_open : IsOpen L := by
    dsimp [L]
    repeat' apply IsOpen.inter
    · exact isOpen_lt continuous_const hcoord0
    · exact isOpen_lt hcoord0 continuous_const
    · exact isOpen_lt continuous_const hcoord1
    · exact isOpen_lt hcoord1 (continuous_const.mul hcoord0)
  have hR_open : IsOpen R := by
    dsimp [R]
    repeat' apply IsOpen.inter
    · exact isOpen_lt continuous_const hcoord0
    · exact isOpen_lt hcoord0 continuous_const
    · exact isOpen_lt continuous_const hlin2
    · exact isOpen_lt hcoord1 continuous_const
  let X : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 0
  let Y : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 1
  let Lower : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := Y + K • X
  let Upper : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := Y - K • X
  have hXgt : Convex ℝ {z : Fin 2 → ℝ | (0 : ℝ) < X z} :=
    convex_halfSpace_gt X.isLinear 0
  have hXlt : Convex ℝ {z : Fin 2 → ℝ | X z < a} :=
    convex_halfSpace_lt X.isLinear a
  have hYgt : Convex ℝ {z : Fin 2 → ℝ | (0 : ℝ) < Y z} :=
    convex_halfSpace_gt Y.isLinear 0
  have hYlt : Convex ℝ {z : Fin 2 → ℝ | Y z < (0 : ℝ)} :=
    convex_halfSpace_lt Y.isLinear 0
  have hLowerGt : Convex ℝ {z : Fin 2 → ℝ | (0 : ℝ) < Lower z} :=
    convex_halfSpace_gt Lower.isLinear 0
  have hUpperLt : Convex ℝ {z : Fin 2 → ℝ | Upper z < (0 : ℝ)} :=
    convex_halfSpace_lt Upper.isLinear 0
  have hL_conv : Convex ℝ L := by
    simpa [L, X, Y, Upper, Set.inter_def, sub_eq_add_neg, add_comm, add_left_comm,
      add_assoc] using (hXgt.inter (hXlt.inter (hYgt.inter hUpperLt)))
  have hR_conv : Convex ℝ R := by
    simpa [R, X, Y, Lower, Set.inter_def, add_comm, add_left_comm, add_assoc] using
      (hXgt.inter (hXlt.inter (hLowerGt.inter hYlt)))
  have hL_nonempty : L.Nonempty := by
    refine ⟨fun i => if i = 0 then a / 2 else K * a / 4, ?_⟩
    dsimp [L]
    have ha2 : 0 < a / 2 := by positivity
    have hKa4 : 0 < K * a / 4 := by positivity
    have hKa4_lt : K * a / 4 < K * (a / 2) := by nlinarith [mul_pos hK ha]
    simp [ha2, hKa4, hKa4_lt]
    nlinarith
  have hR_nonempty : R.Nonempty := by
    refine ⟨fun i => if i = 0 then a / 2 else -(K * a / 4), ?_⟩
    dsimp [R]
    have ha2 : 0 < a / 2 := by positivity
    have hKa4 : 0 < K * a / 4 := by positivity
    have hsum_pos : 0 < -(K * a / 4) + K * (a / 2) := by nlinarith [mul_pos hK ha]
    simp [ha2, hKa4, hsum_pos]
    nlinarith
  refine ⟨hC_open, hL_open, hR_open, hL_conv.isConnected hL_nonempty,
    hR_conv.isConnected hR_nonempty, ?_, ?_, ?_, ?_⟩
  · rw [Set.disjoint_left]
    intro z hzL hzR
    dsimp [L] at hzL
    dsimp [R] at hzR
    linarith
  · dsimp [C]
    simp
  · intro z hz
    dsimp [G] at hz
    dsimp [C]
    rcases hz with ⟨hz0, hza, hz1⟩
    have hKz : 0 < K * z 0 := mul_pos hK hz0
    constructor
    · exact hz0
    constructor
    · exact hza
    constructor
    · rw [hz1]
      linarith
    · rw [hz1]
      linarith
  · ext z
    constructor
    · intro hz
      rcases hz with ⟨hzC, hznotG⟩
      dsimp [C] at hzC
      rcases hzC with ⟨hz0, hza, hzlow, hzhigh⟩
      have hzne : z 1 ≠ 0 := by
        intro hz1
        exact hznotG (by dsimp [G]; exact ⟨hz0, hza, hz1⟩)
      rcases lt_or_gt_of_ne hzne with hneg | hpos
      · right
        dsimp [R]
        exact ⟨hz0, hza, hzlow, hneg⟩
      · left
        dsimp [L]
        exact ⟨hz0, hza, hpos, hzhigh⟩
    · intro hz
      rcases hz with hzL | hzR
      · constructor
        · dsimp [L] at hzL
          dsimp [C]
          rcases hzL with ⟨hz0, hza, hzpos, hzhigh⟩
          have hsum : 0 < z 1 + K * z 0 := by
            have hKz : 0 < K * z 0 := mul_pos hK hz0
            linarith
          exact ⟨hz0, hza, hsum, hzhigh⟩
        · dsimp [G]
          intro hG
          rcases hG with ⟨_, _, hz1⟩
          dsimp [L] at hzL
          linarith
      · constructor
        · dsimp [R] at hzR
          dsimp [C]
          rcases hzR with ⟨hz0, hza, hzlow, hzneg⟩
          have hhigh : z 1 < K * z 0 := by
            have hKz : 0 < K * z 0 := mul_pos hK hz0
            linarith
          exact ⟨hz0, hza, hzlow, hhigh⟩
        · dsimp [G]
          intro hG
          rcases hG with ⟨_, _, hz1⟩
          dsimp [R] at hzR
          linarith
