import Util.IncidenceGeometry.UnitCircleCyclicAngleData
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Finset.Sort

open Classical
open scoped Fin.NatCast
noncomputable section

lemma UnitCircleCyclicAngleBasicOrder
    (p : EuclideanSpace ℝ (Fin 2))
    (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (θ : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S} → ℝ)
    (hθ_mem : ∀ x, 0 ≤ θ x ∧ θ x < 2 * Real.pi)
    (hθ_point : ∀ x,
      x.1 =
        p + WithLp.toLp 2
          (fun i : Fin 2 =>
            if i = 0 then Real.cos (θ x) else Real.sin (θ x)))
    (hθ_inj : Function.Injective θ)
    (hcard : 3 ≤ S.card) :
    ∃ (succ :
        {x : EuclideanSpace ℝ (Fin 2) // x ∈ S} →
          {x : EuclideanSpace ℝ (Fin 2) // x ∈ S})
      (startAngle endAngle :
        {x : EuclideanSpace ℝ (Fin 2) // x ∈ S} → ℝ),
      Function.Bijective succ ∧
      (∀ x, x.1 ≠ (succ x).1) ∧
      (∀ x y,
        (Sym2.mk x.1 (succ x).1 :
            Sym2 (EuclideanSpace ℝ (Fin 2))) =
          Sym2.mk y.1 (succ y).1 →
        x = y) ∧
      (∀ x, 0 ≤ startAngle x ∧ startAngle x < 2 * Real.pi) ∧
      (∀ x,
        x.1 =
          p + WithLp.toLp 2
            (fun i : Fin 2 =>
              if i = 0 then Real.cos (startAngle x) else
                Real.sin (startAngle x))) ∧
      (∀ x,
        (succ x).1 =
          p + WithLp.toLp 2
            (fun i : Fin 2 =>
              if i = 0 then Real.cos (endAngle x) else
                Real.sin (endAngle x))) ∧
      (∀ x, endAngle x = startAngle (succ x) ∨
        endAngle x = startAngle (succ x) + 2 * Real.pi) ∧
      (∀ x, startAngle x < endAngle x) ∧
      (∀ x, endAngle x < startAngle x + 2 * Real.pi) ∧
      (∀ (x y : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S}) (t : ℝ),
        0 < t → t < 1 →
          y.1 ≠
            p + WithLp.toLp 2
              (fun i : Fin 2 =>
                if i = 0 then
                  Real.cos ((1 - t) * startAngle x + t * endAngle x)
                else
                  Real.sin ((1 - t) * startAngle x + t * endAngle x))) ∧
      (∀ (x y : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S}) (s t : ℝ),
        x ≠ y → 0 < s → s < 1 → 0 < t → t < 1 →
          p + WithLp.toLp 2
              (fun i : Fin 2 =>
                if i = 0 then
                  Real.cos ((1 - s) * startAngle x + s * endAngle x)
                else
                  Real.sin ((1 - s) * startAngle x + s * endAngle x)) ≠
            p + WithLp.toLp 2
              (fun i : Fin 2 =>
                if i = 0 then
                  Real.cos ((1 - t) * startAngle y + t * endAngle y)
                else
                  Real.sin ((1 - t) * startAngle y + t * endAngle y))) := by
  let A := {x : EuclideanSpace ℝ (Fin 2) // x ∈ S}
  let n := Fintype.card A
  have hnS : n = S.card := by
    simp [n, A]
  have hn3 : 3 ≤ n := by
    simpa [hnS] using hcard
  have hnpos : 0 < n := by omega
  have : NeZero n := ⟨Nat.ne_of_gt hnpos⟩
  let : LinearOrder A := LinearOrder.lift' θ hθ_inj
  let e : Fin n ≃o A := Fintype.orderIsoFinOfCardEq A rfl
  let shift : Equiv.Perm (Fin n) :=
    { toFun := fun i => i + 1
      invFun := fun i => i - 1
      left_inv := by
        intro i
        simp
      right_inv := by
        intro i
        simp }
  let succ : A → A := fun x => e (shift (e.symm x))
  let startAngle : A → ℝ := θ
  let endAngle : A → ℝ :=
    fun x => if shift (e.symm x) = 0 then θ (succ x) + 2 * Real.pi else θ (succ x)
  have hθ_strict : StrictMono (fun i : Fin n => θ (e i)) := by
    intro i j hij
    change θ (e i) < θ (e j)
    exact e.strictMono hij
  have hshift_apply : ∀ i : Fin n, shift i = i + 1 := by
    intro i
    rfl
  have hshift_ne_self : ∀ i : Fin n, shift i ≠ i := by
    intro i h
    have hone_zero : (1 : Fin n) = 0 := by
      apply add_left_cancel (a := i)
      calc
        i + 1 = i := by simpa [hshift_apply] using h
        _ = i + 0 := by simp
    have hdiv : n ∣ 1 := by
      simpa using (Fin.natCast_eq_zero (a := 1) (n := n)).mp hone_zero
    have hle : n ≤ 1 := Nat.le_of_dvd (by norm_num) hdiv
    omega
  have hshift2_ne_self : ∀ i : Fin n, shift (shift i) ≠ i := by
    intro i h
    have htwo_zero : (2 : Fin n) = 0 := by
      apply add_left_cancel (a := i)
      calc
        i + (2 : Fin n) = i + 1 + 1 := by norm_num [hshift_apply, add_assoc]
        _ = i := by simpa [hshift_apply] using h
        _ = i + 0 := by simp
    have hdiv : n ∣ 2 := by
      simpa using (Fin.natCast_eq_zero (a := 2) (n := n)).mp htwo_zero
    have hle : n ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    omega
  have hshift_lt_of_ne_zero : ∀ i : Fin n, shift i ≠ 0 → i < shift i := by
    intro i hne
    have hne' : i + 1 ≠ 0 := by simpa [hshift_apply] using hne
    have hlt : i.val + 1 < n := by
      by_contra hnot
      have hle : i.val + 1 ≤ n := Nat.succ_le_of_lt i.isLt
      have heq : i.val + 1 = n := le_antisymm hle (le_of_not_gt hnot)
      have hzero : i + 1 = 0 := by
        have hone : ((1 : Fin n) : ℕ) = 1 := by
          change 1 % n = 1
          exact Nat.mod_eq_of_lt (by omega)
        ext
        rw [Fin.val_add_eq_ite]
        rw [hone, heq]
        simp
      exact hne' hzero
    simp [hshift_apply, Fin.lt_def, Fin.val_add_one_of_lt' hlt]
  have hshift_val_of_ne_zero :
      ∀ i : Fin n, shift i ≠ 0 → (shift i).val = i.val + 1 := by
    intro i hne
    have hne' : i + 1 ≠ 0 := by simpa [hshift_apply] using hne
    have hlt : i.val + 1 < n := by
      by_contra hnot
      have hle : i.val + 1 ≤ n := Nat.succ_le_of_lt i.isLt
      have heq : i.val + 1 = n := le_antisymm hle (le_of_not_gt hnot)
      have hzero : i + 1 = 0 := by
        have hone : ((1 : Fin n) : ℕ) = 1 := by
          change 1 % n = 1
          exact Nat.mod_eq_of_lt (by omega)
        ext
        rw [Fin.val_add_eq_ite]
        rw [hone, heq]
        simp
      exact hne' hzero
    simpa [hshift_apply] using Fin.val_add_one_of_lt' hlt
  have hshift_le_of_lt :
      ∀ {i j : Fin n}, shift i ≠ 0 → i < j → shift i ≤ j := by
    intro i j hne hij
    rw [Fin.le_def, hshift_val_of_ne_zero i hne]
    exact Nat.succ_le_of_lt (Fin.lt_def.mp hij)
  have hwrap_max : ∀ {i j : Fin n}, shift i = 0 → j ≤ i := by
    intro i j hwrap
    refine le_of_not_gt ?_
    intro hij
    have hlt : i.val + 1 < n := by
      have hijv : i.val < j.val := Fin.lt_def.mp hij
      omega
    have hval : ((i + 1 : Fin n) : ℕ) = i.val + 1 :=
      Fin.val_add_one_of_lt' hlt
    have hzero : ((i + 1 : Fin n) : ℕ) = 0 := by
      simpa [hshift_apply] using congrArg Fin.val hwrap
    omega
  have hsucc_bijective : Function.Bijective succ := by
    constructor
    · intro x y hxy
      dsimp [succ] at hxy
      have h1 := e.injective hxy
      have h2 := shift.injective h1
      exact e.symm.injective h2
    · intro y
      exact ⟨e (shift.symm (e.symm y)), by simp [succ]⟩
  have hsucc_ne : ∀ x : A, x.1 ≠ (succ x).1 := by
    intro x hx
    have hxs : succ x = x := Subtype.ext hx.symm
    have hidx : shift (e.symm x) = e.symm x := by
      exact e.injective (by simpa [succ] using hxs)
    exact hshift_ne_self (e.symm x) hidx
  have hendpoint_unique :
      ∀ x y : A,
        (Sym2.mk x.1 (succ x).1 :
            Sym2 (EuclideanSpace ℝ (Fin 2))) =
          Sym2.mk y.1 (succ y).1 →
        x = y := by
    intro x y hxy
    rcases (Sym2.eq_iff).mp hxy with hdir | hswap
    · exact Subtype.ext hdir.1
    · have hx_succy : x = succ y := Subtype.ext hswap.1
      have hsuccx_y : succ x = y := Subtype.ext hswap.2
      have hidx1 : e.symm x = shift (e.symm y) := by
        simpa [succ] using congrArg e.symm hx_succy
      have hidx2 : shift (e.symm x) = e.symm y := by
        simpa [succ] using congrArg e.symm hsuccx_y
      have hperiod : shift (shift (e.symm y)) = e.symm y := by
        simpa [hidx1] using hidx2
      exact False.elim (hshift2_ne_self (e.symm y) hperiod)
  have hend_point : ∀ x : A,
      (succ x).1 =
        p + WithLp.toLp 2
          (fun i : Fin 2 =>
            if i = 0 then Real.cos (endAngle x) else Real.sin (endAngle x)) := by
    intro x
    by_cases hwrap : shift (e.symm x) = 0
    · simpa [endAngle, hwrap, Real.cos_add_two_pi, Real.sin_add_two_pi]
        using hθ_point (succ x)
    · simpa [endAngle, hwrap] using hθ_point (succ x)
  have hend_lift : ∀ x : A,
      endAngle x = startAngle (succ x) ∨
        endAngle x = startAngle (succ x) + 2 * Real.pi := by
    intro x
    by_cases hwrap : shift (e.symm x) = 0
    · exact Or.inr (by simp [endAngle, startAngle, hwrap])
    · exact Or.inl (by simp [endAngle, startAngle, hwrap])
  have hgap_pos : ∀ x : A, startAngle x < endAngle x := by
    intro x
    by_cases hwrap : shift (e.symm x) = 0
    · have hidx_ne_zero : e.symm x ≠ 0 := by
        intro hzero
        have : shift (e.symm x) = 1 := by simp [hshift_apply, hzero]
        have h10 : (1 : Fin n) = 0 := by simpa [this] using hwrap
        have hdiv : n ∣ 1 := by
          simpa using (Fin.natCast_eq_zero (a := 1) (n := n)).mp h10
        have hle : n ≤ 1 := Nat.le_of_dvd (by norm_num) hdiv
        omega
      have hzero_lt : (0 : Fin n) < e.symm x :=
        lt_of_le_of_ne (Fin.zero_le _) (Ne.symm hidx_ne_zero)
      have hθlt : θ (e 0) < θ (e (e.symm x)) := hθ_strict hzero_lt
      have hθlt' : θ (succ x) < θ x := by
        simpa [succ, hwrap] using hθlt
      have hxmem := hθ_mem x
      have hsuccmem := hθ_mem (succ x)
      simp [startAngle, endAngle, hwrap]
      linarith [hxmem.2, hsuccmem.1]
    · have hi_lt : e.symm x < shift (e.symm x) :=
        hshift_lt_of_ne_zero (e.symm x) hwrap
      have hθlt : θ (e (e.symm x)) < θ (e (shift (e.symm x))) :=
        hθ_strict hi_lt
      simpa [startAngle, endAngle, succ, hwrap] using hθlt
  have hgap_short : ∀ x : A, endAngle x < startAngle x + 2 * Real.pi := by
    intro x
    by_cases hwrap : shift (e.symm x) = 0
    · have hidx_ne_zero : e.symm x ≠ 0 := by
        intro hzero
        have : shift (e.symm x) = 1 := by simp [hshift_apply, hzero]
        have h10 : (1 : Fin n) = 0 := by simpa [this] using hwrap
        have hdiv : n ∣ 1 := by
          simpa using (Fin.natCast_eq_zero (a := 1) (n := n)).mp h10
        have hle : n ≤ 1 := Nat.le_of_dvd (by norm_num) hdiv
        omega
      have hzero_lt : (0 : Fin n) < e.symm x :=
        lt_of_le_of_ne (Fin.zero_le _) (Ne.symm hidx_ne_zero)
      have hθlt : θ (e 0) < θ (e (e.symm x)) := hθ_strict hzero_lt
      have hθlt' : θ (succ x) < θ x := by
        simpa [succ, hwrap] using hθlt
      simp [startAngle, endAngle, hwrap]
      linarith
    · have hmem_start := hθ_mem x
      have hmem_end := hθ_mem (succ x)
      simp [startAngle, endAngle, hwrap]
      linarith
  have hθ_mono : Monotone (fun i : Fin n => θ (e i)) := hθ_strict.monotone
  have : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  have hangle_open :
      ∀ (x : A) (t : ℝ), 0 < t → t < 1 →
        startAngle x < (1 - t) * startAngle x + t * endAngle x ∧
          (1 - t) * startAngle x + t * endAngle x < endAngle x := by
    intro x t ht0 ht1
    have hgap : startAngle x < endAngle x := hgap_pos x
    have hdiff_pos : 0 < endAngle x - startAngle x := sub_pos.mpr hgap
    have hrewrite :
        (1 - t) * startAngle x + t * endAngle x =
          startAngle x + t * (endAngle x - startAngle x) := by
      ring
    rw [hrewrite]
    constructor
    · have hmul : 0 < t * (endAngle x - startAngle x) :=
        mul_pos ht0 hdiff_pos
      linarith
    · have hmul :
        t * (endAngle x - startAngle x) <
          1 * (endAngle x - startAngle x) :=
        mul_lt_mul_of_pos_right ht1 hdiff_pos
      linarith
  have hmod_between_nonwrap :
      ∀ (i : Fin n) (t : ℝ), shift i ≠ 0 → 0 < t → t < 1 →
        θ (e i) <
            toIcoMod Real.two_pi_pos 0
              ((1 - t) * θ (e i) + t * θ (e (shift i))) ∧
          toIcoMod Real.two_pi_pos 0
              ((1 - t) * θ (e i) + t * θ (e (shift i))) <
            θ (e (shift i)) := by
    intro i t hnonwrap ht0 ht1
    have hopen := hangle_open (e i) t ht0 ht1
    have hαIco :
        ((1 - t) * θ (e i) + t * θ (e (shift i))) ∈
          Set.Ico (0 : ℝ) (0 + 2 * Real.pi) := by
      constructor
      · have hmem := hθ_mem (e i)
        have hleft :
            θ (e i) <
              (1 - t) * θ (e i) + t * θ (e (shift i)) := by
          simpa [startAngle, endAngle, succ, hnonwrap] using hopen.1
        linarith
      · have hmem := hθ_mem (e (shift i))
        have hright :
            (1 - t) * θ (e i) + t * θ (e (shift i)) <
              θ (e (shift i)) := by
          simpa [startAngle, endAngle, succ, hnonwrap] using hopen.2
        simpa [zero_add] using lt_trans hright hmem.2
    have hmod :
        toIcoMod Real.two_pi_pos 0
            ((1 - t) * θ (e i) + t * θ (e (shift i))) =
          ((1 - t) * θ (e i) + t * θ (e (shift i))) :=
      (toIcoMod_eq_self Real.two_pi_pos).mpr hαIco
    have hleft :
        θ (e i) <
          (1 - t) * θ (e i) + t * θ (e (shift i)) := by
      simpa [startAngle, endAngle, succ, hnonwrap] using hopen.1
    have hright :
        (1 - t) * θ (e i) + t * θ (e (shift i)) <
          θ (e (shift i)) := by
      simpa [startAngle, endAngle, succ, hnonwrap] using hopen.2
    constructor <;> linarith
  have hmod_wrap :
      ∀ (i : Fin n) (t : ℝ), shift i = 0 → 0 < t → t < 1 →
        θ (e i) <
            toIcoMod Real.two_pi_pos 0
              ((1 - t) * θ (e i) + t * (θ (e 0) + 2 * Real.pi)) ∨
          toIcoMod Real.two_pi_pos 0
              ((1 - t) * θ (e i) + t * (θ (e 0) + 2 * Real.pi)) <
            θ (e 0) := by
    intro i t hwrap ht0 ht1
    have hopen := hangle_open (e i) t ht0 ht1
    have hleft :
        θ (e i) <
          (1 - t) * θ (e i) + t * (θ (e 0) + 2 * Real.pi) := by
      simpa [startAngle, endAngle, succ, hwrap] using hopen.1
    have hright :
        (1 - t) * θ (e i) + t * (θ (e 0) + 2 * Real.pi) <
          θ (e 0) + 2 * Real.pi := by
      simpa [startAngle, endAngle, succ, hwrap] using hopen.2
    by_cases hlt :
        (1 - t) * θ (e i) + t * (θ (e 0) + 2 * Real.pi) <
          2 * Real.pi
    · left
      have hαIco :
          ((1 - t) * θ (e i) + t * (θ (e 0) + 2 * Real.pi)) ∈
            Set.Ico (0 : ℝ) (0 + 2 * Real.pi) := by
        constructor
        · have hmem := hθ_mem (e i)
          linarith
        · simpa [zero_add] using hlt
      have hmod :
          toIcoMod Real.two_pi_pos 0
              ((1 - t) * θ (e i) + t * (θ (e 0) + 2 * Real.pi)) =
            ((1 - t) * θ (e i) + t * (θ (e 0) + 2 * Real.pi)) :=
        (toIcoMod_eq_self Real.two_pi_pos).mpr hαIco
      linarith
    · right
      have hge :
          2 * Real.pi ≤
            (1 - t) * θ (e i) + t * (θ (e 0) + 2 * Real.pi) :=
        le_of_not_gt hlt
      have hsubIco :
          ((1 - t) * θ (e i) + t * (θ (e 0) + 2 * Real.pi) -
              2 * Real.pi) ∈
            Set.Ico (0 : ℝ) (0 + 2 * Real.pi) := by
        constructor
        · linarith
        · have hmem0 := hθ_mem (e 0)
          linarith
      have hmod :
          toIcoMod Real.two_pi_pos 0
              ((1 - t) * θ (e i) + t * (θ (e 0) + 2 * Real.pi)) =
            ((1 - t) * θ (e i) + t * (θ (e 0) + 2 * Real.pi) -
              2 * Real.pi) := by
        rw [toIcoMod_eq_iff Real.two_pi_pos]
        constructor
        · exact hsubIco
        · refine ⟨(1 : ℤ), ?_⟩
          simp
      linarith
  have hno_mod_angle_in_gap :
      ∀ (x y : A) (t : ℝ), 0 < t → t < 1 →
        toIcoMod Real.two_pi_pos 0
            ((1 - t) * startAngle x + t * endAngle x) ≠
          θ y := by
    intro x y t ht0 ht1 hmod
    let i : Fin n := e.symm x
    let j : Fin n := e.symm y
    have hxe : e i = x := by simp [i]
    have hye : e j = y := by simp [j]
    by_cases hwrap : shift i = 0
    · have hloc := hmod_wrap i t hwrap ht0 ht1
      have hmod' :
          toIcoMod Real.two_pi_pos 0
              ((1 - t) * θ (e i) + t * (θ (e 0) + 2 * Real.pi)) =
            θ (e j) := by
        simpa [i, j, startAngle, endAngle, succ, hwrap] using hmod
      have hj_le_i : j ≤ i := hwrap_max hwrap
      have hθji : θ (e j) ≤ θ (e i) := hθ_mono hj_le_i
      have hθ0j : θ (e 0) ≤ θ (e j) := hθ_mono (Fin.zero_le j)
      rcases hloc with hgt | hlt0
      · linarith
      · linarith
    · have hloc := hmod_between_nonwrap i t hwrap ht0 ht1
      have hmod' :
          toIcoMod Real.two_pi_pos 0
              ((1 - t) * θ (e i) + t * θ (e (shift i))) =
            θ (e j) := by
        simpa [i, j, startAngle, endAngle, succ, hwrap] using hmod
      have htotal : j ≤ i ∨ i < j := le_or_gt j i
      rcases htotal with hji | hij
      · have hθji : θ (e j) ≤ θ (e i) := hθ_mono hji
        linarith
      · have hsj : shift i ≤ j := hshift_le_of_lt hwrap hij
        have hθsj : θ (e (shift i)) ≤ θ (e j) := hθ_mono hsj
        linarith
  have hangle_eq_of_circle_eq :
      ∀ {α β : ℝ},
        p + WithLp.toLp 2
            (fun i : Fin 2 => if i = 0 then Real.cos α else Real.sin α) =
          p + WithLp.toLp 2
            (fun i : Fin 2 => if i = 0 then Real.cos β else Real.sin β) →
        (α : Real.Angle) = (β : Real.Angle) := by
    intro α β h
    have hcos_coord :
        p (0 : Fin 2) + Real.cos α = p (0 : Fin 2) + Real.cos β := by
      simpa using congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z (0 : Fin 2)) h
    have hsin_coord :
        p (1 : Fin 2) + Real.sin α = p (1 : Fin 2) + Real.sin β := by
      simpa using congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z (1 : Fin 2)) h
    have hcos : Real.cos α = Real.cos β := add_left_cancel hcos_coord
    have hsin : Real.sin α = Real.sin β := add_left_cancel hsin_coord
    exact Real.Angle.cos_sin_inj hcos hsin
  have hmod_eq_of_angle_eq :
      ∀ {α β : ℝ}, 0 ≤ β → β < 2 * Real.pi →
        (α : Real.Angle) = (β : Real.Angle) →
          toIcoMod Real.two_pi_pos 0 α = β := by
    intro α β hβ0 hβ2 hangle
    have hβIco : β ∈ Set.Ico (0 : ℝ) (0 + 2 * Real.pi) := by
      exact ⟨hβ0, by simpa [zero_add] using hβ2⟩
    have hmodIco :
        toIcoMod Real.two_pi_pos 0 α ∈ Set.Ico (0 : ℝ) (0 + 2 * Real.pi) :=
      toIcoMod_mem_Ico Real.two_pi_pos 0 α
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ico hmodIco hβIco).mp
      ((Real.Angle.coe_toIcoMod α 0).trans hangle)
  have hno_S_in_open_gap :
      ∀ (x y : A) (t : ℝ), 0 < t → t < 1 →
        y.1 ≠
          p + WithLp.toLp 2
            (fun i : Fin 2 =>
              if i = 0 then
                Real.cos ((1 - t) * startAngle x + t * endAngle x)
              else
                Real.sin ((1 - t) * startAngle x + t * endAngle x)) := by
    intro x y t ht0 ht1 hpoint
    let α := (1 - t) * startAngle x + t * endAngle x
    have hcircle :
        p + WithLp.toLp 2
            (fun i : Fin 2 => if i = 0 then Real.cos (θ y) else Real.sin (θ y)) =
          p + WithLp.toLp 2
            (fun i : Fin 2 => if i = 0 then Real.cos α else Real.sin α) := by
      calc
        p + WithLp.toLp 2
            (fun i : Fin 2 => if i = 0 then Real.cos (θ y) else Real.sin (θ y)) =
            y.1 := (hθ_point y).symm
        _ = p + WithLp.toLp 2
            (fun i : Fin 2 => if i = 0 then Real.cos α else Real.sin α) := by
          simpa [α] using hpoint
    have hangle : (α : Real.Angle) = (θ y : Real.Angle) :=
      (hangle_eq_of_circle_eq hcircle).symm
    have hmod :
        toIcoMod Real.two_pi_pos 0 α = θ y :=
      hmod_eq_of_angle_eq (hθ_mem y).1 (hθ_mem y).2 hangle
    exact hno_mod_angle_in_gap x y t ht0 ht1 (by simpa [α] using hmod)
  have hmod_gaps_disjoint :
      ∀ (x y : A) (s t : ℝ), x ≠ y → 0 < s → s < 1 → 0 < t → t < 1 →
        toIcoMod Real.two_pi_pos 0
            ((1 - s) * startAngle x + s * endAngle x) ≠
          toIcoMod Real.two_pi_pos 0
            ((1 - t) * startAngle y + t * endAngle y) := by
    intro x y s t hxy hs0 hs1 ht0 ht1 hmod
    let i : Fin n := e.symm x
    let j : Fin n := e.symm y
    have hij_ne : i ≠ j := by
      intro hij
      apply hxy
      calc
        x = e i := by simp [i]
        _ = e j := by rw [hij]
        _ = y := by simp [j]
    by_cases hwrap_i : shift i = 0
    · by_cases hwrap_j : shift j = 0
      · exact hij_ne (shift.injective (hwrap_i.trans hwrap_j.symm))
      · have hloc_i := hmod_wrap i s hwrap_i hs0 hs1
        have hloc_j := hmod_between_nonwrap j t hwrap_j ht0 ht1
        have hmod' :
            toIcoMod Real.two_pi_pos 0
                ((1 - s) * θ (e i) + s * (θ (e 0) + 2 * Real.pi)) =
              toIcoMod Real.two_pi_pos 0
                ((1 - t) * θ (e j) + t * θ (e (shift j))) := by
          simpa [i, j, startAngle, endAngle, succ, hwrap_i, hwrap_j] using hmod
        have hji : j < i := by
          have hle : j ≤ i := hwrap_max hwrap_i
          exact lt_of_le_of_ne hle (Ne.symm hij_ne)
        have hsj_i : shift j ≤ i := hshift_le_of_lt hwrap_j hji
        have hθsj_i : θ (e (shift j)) ≤ θ (e i) := hθ_mono hsj_i
        have hθ0j : θ (e 0) ≤ θ (e j) := hθ_mono (Fin.zero_le j)
        rcases hloc_i with hi_gt | hi_lt0
        · linarith
        · linarith
    · by_cases hwrap_j : shift j = 0
      · have hloc_i := hmod_between_nonwrap i s hwrap_i hs0 hs1
        have hloc_j := hmod_wrap j t hwrap_j ht0 ht1
        have hmod' :
            toIcoMod Real.two_pi_pos 0
                ((1 - s) * θ (e i) + s * θ (e (shift i))) =
              toIcoMod Real.two_pi_pos 0
                ((1 - t) * θ (e j) + t * (θ (e 0) + 2 * Real.pi)) := by
          simpa [i, j, startAngle, endAngle, succ, hwrap_i, hwrap_j] using hmod
        have hij_lt : i < j := by
          have hle : i ≤ j := hwrap_max hwrap_j
          exact lt_of_le_of_ne hle hij_ne
        have hsi_j : shift i ≤ j := hshift_le_of_lt hwrap_i hij_lt
        have hθsi_j : θ (e (shift i)) ≤ θ (e j) := hθ_mono hsi_j
        have hθ0i : θ (e 0) ≤ θ (e i) := hθ_mono (Fin.zero_le i)
        rcases hloc_j with hj_gt | hj_lt0
        · linarith
        · linarith
      · have hloc_i := hmod_between_nonwrap i s hwrap_i hs0 hs1
        have hloc_j := hmod_between_nonwrap j t hwrap_j ht0 ht1
        have hmod' :
            toIcoMod Real.two_pi_pos 0
                ((1 - s) * θ (e i) + s * θ (e (shift i))) =
              toIcoMod Real.two_pi_pos 0
                ((1 - t) * θ (e j) + t * θ (e (shift j))) := by
          simpa [i, j, startAngle, endAngle, succ, hwrap_i, hwrap_j] using hmod
        have htotal : i < j ∨ j < i := lt_or_gt_of_ne hij_ne
        rcases htotal with hij | hji
        · have hsi_j : shift i ≤ j := hshift_le_of_lt hwrap_i hij
          have hθsi_j : θ (e (shift i)) ≤ θ (e j) := hθ_mono hsi_j
          linarith
        · have hsj_i : shift j ≤ i := hshift_le_of_lt hwrap_j hji
          have hθsj_i : θ (e (shift j)) ≤ θ (e i) := hθ_mono hsj_i
          linarith
  have hopen_gaps_disjoint :
      ∀ (x y : A) (s t : ℝ),
        x ≠ y → 0 < s → s < 1 → 0 < t → t < 1 →
          p + WithLp.toLp 2
              (fun i : Fin 2 =>
                if i = 0 then
                  Real.cos ((1 - s) * startAngle x + s * endAngle x)
                else
                  Real.sin ((1 - s) * startAngle x + s * endAngle x)) ≠
            p + WithLp.toLp 2
              (fun i : Fin 2 =>
                if i = 0 then
                  Real.cos ((1 - t) * startAngle y + t * endAngle y)
                else
                  Real.sin ((1 - t) * startAngle y + t * endAngle y)) := by
    intro x y s t hxy hs0 hs1 ht0 ht1 hpoint
    let α := (1 - s) * startAngle x + s * endAngle x
    let β := (1 - t) * startAngle y + t * endAngle y
    have hangle : (α : Real.Angle) = (β : Real.Angle) := by
      apply hangle_eq_of_circle_eq
      simpa [α, β] using hpoint
    have hmod :
        toIcoMod Real.two_pi_pos 0 α =
          toIcoMod Real.two_pi_pos 0 β := by
      have hαIco :
          toIcoMod Real.two_pi_pos 0 α ∈ Set.Ico (0 : ℝ) (0 + 2 * Real.pi) :=
        toIcoMod_mem_Ico Real.two_pi_pos 0 α
      have hβIco :
          toIcoMod Real.two_pi_pos 0 β ∈ Set.Ico (0 : ℝ) (0 + 2 * Real.pi) :=
        toIcoMod_mem_Ico Real.two_pi_pos 0 β
      exact (AddCircle.coe_eq_coe_iff_of_mem_Ico hαIco hβIco).mp
        ((Real.Angle.coe_toIcoMod α 0).trans
          (hangle.trans (Real.Angle.coe_toIcoMod β 0).symm))
    exact hmod_gaps_disjoint x y s t hxy hs0 hs1 ht0 ht1 (by simpa [α, β] using hmod)
  exact ⟨succ, startAngle, endAngle, hsucc_bijective, hsucc_ne, hendpoint_unique,
    hθ_mem, hθ_point, hend_point, hend_lift, hgap_pos, hgap_short,
    hno_S_in_open_gap, hopen_gaps_disjoint⟩
