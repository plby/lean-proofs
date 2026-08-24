import ErdosProblems.Erdos360.CyclicInverse
import ErdosProblems.Erdos360.AffineConnector

open scoped Pointwise

namespace Erdos360

/-!
# Carry completion for the quotient--remainder partial lift

This file isolates the exact finite PL4--PL5 mechanism.  There are three
parts.

* The Fourier-core constants force every translate of the core to meet the
  core double sumset as soon as the latter has the `3/2` lower bound supplied
  by the fibre theorem.
* A *zero-carry* ternary collision with the affine core puts the new point in
  the same affine fibre coset.
* Once every full fibre has this affine form, the sole possible obstruction
  to preservation of pair sums is the class `1 + m • u` in the quotient
  subgroup.  Excluding that class makes the full lift an order-two Freiman
  isomorphism.

The middle hypothesis is deliberately stated as equality of lifted sums.
It is the precise output of the carry-cell separation count in the
Deshouillers--Freiman proof; no no-wrap hypothesis on the full set is hidden
in the statement.
-/

attribute [local instance] Classical.propDecidable

/-- With the exact Fourier-core constants, a `3/2` lower bound for the core
double sumset forces every core translate to collide with the core double
sumset.  This is the cardinal part of (PL6). -/
theorem exists_core_ternary_collision_of_dense_smallDoubling
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {B C : Finset G}
    (hB : B.Nonempty)
    (hCB : C ⊆ B)
    (hdense : 33 * B.card ≤ 40 * C.card)
    (hsmall : 25 * (B + B).card ≤ 51 * B.card)
    (hcore : 3 * C.card ≤ 2 * (C + C).card) :
    ∀ z ∈ B, ∃ c₁ ∈ C, ∃ c₂ ∈ C, ∃ c₃ ∈ C,
      z + c₃ = c₁ + c₂ := by
  classical
  have hstrict : (B + B).card < C.card + (C + C).card := by
    have hBpos : 0 < B.card := Finset.card_pos.mpr hB
    omega
  intro z hzB
  let T : Finset G := C.image (fun c => z + c)
  have hTcard : T.card = C.card := by
    dsimp only [T]
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    exact add_left_cancel hab
  have hTsub : T ⊆ B + B := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.add_mem_add hzB (hCB hc)
  have hCCsub : C + C ⊆ B + B :=
    Finset.add_subset_add hCB hCB
  by_contra hnone
  push Not at hnone
  have hdis : Disjoint T (C + C) := by
    rw [Finset.disjoint_left]
    intro x hxT hxCC
    obtain ⟨c₃, hc₃, hzc₃⟩ := Finset.mem_image.mp hxT
    obtain ⟨c₁, hc₁, c₂, hc₂, hc₁c₂⟩ := Finset.mem_add.mp hxCC
    apply hnone c₁ hc₁ c₂ hc₂ c₃ hc₃
    exact hzc₃.trans hc₁c₂.symm
  have hunion : T ∪ (C + C) ⊆ B + B := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hTsub hx
    · exact hCCsub hx
  have hcard := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint hdis, hTcard] at hcard
  omega

/-- The non-strict Balasubramanian--Pandey endpoint is sufficient for the
`3/2` core-sumset lower bound used above.  Here `s` is the number of occupied
layers and `h` is the common subgroup cardinality. -/
lemma three_mul_core_le_two_sumset_of_nonstrict_fiber_excess
    {Ccard Csum s h : ℕ}
    (hs : 2 ≤ s) (hsize : Ccard ≤ s * h)
    (hsharp : (s - 1) * h ≤ Csum - Ccard) :
    3 * Ccard ≤ 2 * Csum := by
  by_cases hh : h = 0
  · subst h
    simp at hsize
    simp [hsize]
  · have hhpos : 0 < h := Nat.pos_of_ne_zero hh
    have hCle : Ccard ≤ Csum := by
      by_contra hnot
      have : Csum - Ccard = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hnot)
      rw [this] at hsharp
      have : 0 < (s - 1) * h := Nat.mul_pos (by omega) hhpos
      omega
    have htwos : s ≤ 2 * (s - 1) := by omega
    have hhalf : Ccard ≤ 2 * ((s - 1) * h) := by
      calc
        Ccard ≤ s * h := hsize
        _ ≤ (2 * (s - 1)) * h := Nat.mul_le_mul_right h htwos
        _ = 2 * ((s - 1) * h) := by ring
    have hsharp' : (s - 1) * h + Ccard ≤ Csum := by
      exact Nat.add_le_of_le_sub hCle hsharp
    omega

/-- A lifted ternary relation with three affine-core points puts its fourth
point in the same affine fibre coset.  This is the algebraic PL4 → PL5
step after carry separation. -/
lemma affine_quotientFiber_of_lifted_ternary
    {m d : ℕ} [NeZero d] [NeZero (m * d)]
    {H : AddSubgroup (ZMod d)} {u v : ZMod d}
    {z c₁ c₂ c₃ : ZMod (m * d)}
    (hc₁ : (c₁.val / m : ZMod d) -
      ((c₁.val % m) • u + v) ∈ H)
    (hc₂ : (c₂.val / m : ZMod d) -
      ((c₂.val % m) • u + v) ∈ H)
    (hc₃ : (c₃.val / m : ZMod d) -
      ((c₃.val % m) • u + v) ∈ H)
    (hrel : zmodQuotRemLift m d z + zmodQuotRemLift m d c₃ =
      zmodQuotRemLift m d c₁ + zmodQuotRemLift m d c₂) :
    (z.val / m : ZMod d) - ((z.val % m) • u + v) ∈ H := by
  have hr : z.val % m + c₃.val % m =
      c₁.val % m + c₂.val % m := congrArg Prod.fst hrel
  have hq : (z.val / m : ZMod d) + (c₃.val / m : ZMod d) =
      (c₁.val / m : ZMod d) + (c₂.val / m : ZMod d) :=
    congrArg Prod.snd hrel
  have hmem := H.sub_mem (H.add_mem hc₁ hc₂) hc₃
  have hq' : (z.val / m : ZMod d) =
      (c₁.val / m : ZMod d) + (c₂.val / m : ZMod d) -
        (c₃.val / m : ZMod d) := by
    rw [eq_sub_iff_add_eq]
    exact hq
  have hru : (z.val % m) • u + (c₃.val % m) • u =
      (c₁.val % m) • u + (c₂.val % m) • u := by
    simpa only [add_nsmul] using congrArg (fun n : ℕ => n • u) hr
  have hru' : (z.val % m) • u =
      (c₁.val % m) • u + (c₂.val % m) • u -
        (c₃.val % m) • u := by
    rw [eq_sub_iff_add_eq]
    exact hru
  convert hmem using 1
  rw [hq', hru']
  abel

/-- If every point of the full set has a zero-carry ternary collision with
the affine core, the affine coset formula extends from the core to the full
set. -/
theorem affine_quotientFibers_of_zeroCarry_core_completion
    {m d : ℕ} [NeZero d] [NeZero (m * d)]
    {B C : Finset (ZMod (m * d))}
    {H : AddSubgroup (ZMod d)} {u v : ZMod d}
    (hcore : ∀ c ∈ C,
      (c.val / m : ZMod d) - ((c.val % m) • u + v) ∈ H)
    (hcollision : ∀ z ∈ B,
      ∃ c₁ ∈ C, ∃ c₂ ∈ C, ∃ c₃ ∈ C,
        zmodQuotRemLift m d z + zmodQuotRemLift m d c₃ =
          zmodQuotRemLift m d c₁ + zmodQuotRemLift m d c₂) :
    ∀ z ∈ B,
      (z.val / m : ZMod d) - ((z.val % m) • u + v) ∈ H := by
  intro z hz
  obtain ⟨c₁, hc₁, c₂, hc₂, c₃, hc₃, hrel⟩ := hcollision z hz
  exact affine_quotientFiber_of_lifted_ternary
    (hcore c₁ hc₁) (hcore c₂ hc₂) (hcore c₃ hc₃) hrel

/-- Ambient equality of two pair sums forces equality of their first lifted
coordinates unless the unique nonzero carry class `1 + m • u` belongs to
the common quotient subgroup. -/
lemma firstCoordinate_pairSum_eq_of_affine_noCarry
    {m d : ℕ} [NeZero d] [NeZero (m * d)]
    (hm : 0 < m) {H : AddSubgroup (ZMod d)} {u v : ZMod d}
    {a b c e : ZMod (m * d)}
    (ha : (a.val / m : ZMod d) - ((a.val % m) • u + v) ∈ H)
    (hb : (b.val / m : ZMod d) - ((b.val % m) • u + v) ∈ H)
    (hc : (c.val / m : ZMod d) - ((c.val % m) • u + v) ∈ H)
    (he : (e.val / m : ZMod d) - ((e.val % m) • u + v) ∈ H)
    (hcarry : (1 : ZMod d) + m • u ∉ H)
    (hsum : a + b = c + e) :
    a.val % m + b.val % m = c.val % m + e.val % m := by
  let ra := a.val % m
  let rb := b.val % m
  let rc := c.val % m
  let re := e.val % m
  let qa := a.val / m
  let qb := b.val / m
  let qc := c.val / m
  let qe := e.val / m
  have haVal : a.val = m * qa + ra := by
    dsimp [qa, ra]
    exact (zmod_val_quot_rem m a).symm
  have hbVal : b.val = m * qb + rb := by
    dsimp [qb, rb]
    exact (zmod_val_quot_rem m b).symm
  have hcVal : c.val = m * qc + rc := by
    dsimp [qc, rc]
    exact (zmod_val_quot_rem m c).symm
  have heVal : e.val = m * qe + re := by
    dsimp [qe, re]
    exact (zmod_val_quot_rem m e).symm
  have hcast : (a.val : ZMod (m * d)) + b.val =
      (c.val : ZMod (m * d)) + e.val := by
    simpa only [ZMod.natCast_zmod_val] using hsum
  have hcast' : ((a.val + b.val : ℕ) : ZMod (m * d)) =
      ((c.val + e.val : ℕ) : ZMod (m * d)) := by
    simpa only [Nat.cast_add] using hcast
  have htotal : a.val + b.val ≡ c.val + e.val [MOD m * d] :=
    ZMod.natCast_eq_natCast_iff _ _ _ |>.mp hcast'
  have hsmallmod : a.val + b.val ≡ c.val + e.val [MOD m] :=
    Nat.ModEq.of_dvd (dvd_mul_right m d) htotal
  have hrmod : ra + rb ≡ rc + re [MOD m] := by
    rw [Nat.ModEq] at hsmallmod ⊢
    simpa [ra, rb, rc, re, Nat.add_mod] using hsmallmod
  have hra : ra < m := Nat.mod_lt _ hm
  have hrb : rb < m := Nat.mod_lt _ hm
  have hrc : rc < m := Nat.mod_lt _ hm
  have hre : re < m := Nat.mod_lt _ hm
  have hablt : ra + rb < 2 * m := by omega
  have hcelt : rc + re < 2 * m := by omega
  have habdiv : (ra + rb) / m < 2 :=
    (Nat.div_lt_iff_lt_mul hm).2 (by simpa [mul_comm] using hablt)
  have hcediv : (rc + re) / m < 2 :=
    (Nat.div_lt_iff_lt_mul hm).2 (by simpa [mul_comm] using hcelt)
  have habdecomp := Nat.mod_add_div (ra + rb) m
  have hcedecomp := Nat.mod_add_div (rc + re) m
  have habdivCases : (ra + rb) / m = 0 ∨ (ra + rb) / m = 1 := by
    have hnonneg : 0 ≤ (ra + rb) / m := Nat.zero_le _
    omega
  have hcedivCases : (rc + re) / m = 0 ∨ (rc + re) / m = 1 := by
    have hnonneg : 0 ≤ (rc + re) / m := Nat.zero_le _
    omega
  have hcases : ra + rb = rc + re ∨
      ra + rb = rc + re + m ∨ rc + re = ra + rb + m := by
    rw [Nat.ModEq] at hrmod
    rcases habdivCases with habdivCases | habdivCases <;>
      rcases hcedivCases with hcedivCases | hcedivCases
    all_goals
      rw [habdivCases] at habdecomp
      rw [hcedivCases] at hcedecomp
      norm_num at habdecomp hcedecomp
      omega
  have hmem := H.sub_mem (H.add_mem ha hb) (H.add_mem hc he)
  have hmemAgg :
      (((qa : ZMod d) + qb - qc - qe) -
        ((ra + rb) • u - (rc + re) • u)) ∈ H := by
    convert hmem using 1 <;> simp only [add_nsmul] <;> abel
  rcases hcases with heq | heq | heq
  · exact heq
  · exfalso
    have habVal : a.val + b.val = m * (qa + qb) + (ra + rb) := by
      rw [haVal, hbVal, Nat.mul_add]
      omega
    have hceVal : c.val + e.val = m * (qc + qe) + (rc + re) := by
      rw [hcVal, heVal, Nat.mul_add]
      omega
    have hexpanded :
        m * (qa + qb + 1) + (rc + re) ≡
          m * (qc + qe) + (rc + re) [MOD m * d] := by
      have h := htotal
      rw [habVal, hceVal, heq] at h
      convert h using 1 <;> ring
    have hmul : m * (qa + qb + 1) ≡ m * (qc + qe) [MOD m * d] :=
      Nat.ModEq.add_right_cancel' (rc + re) hexpanded
    have hqmod : qa + qb + 1 ≡ qc + qe [MOD d] :=
      Nat.ModEq.mul_left_cancel' hm.ne' hmul
    have hq : (qa : ZMod d) + qb + 1 = (qc : ZMod d) + qe := by
      have := ZMod.natCast_eq_natCast_iff _ _ d |>.mpr hqmod
      simpa only [Nat.cast_add, Nat.cast_one] using this
    have hneg : -((1 : ZMod d) + m • u) ∈ H := by
      have hqdiff : ((qa : ZMod d) + qb - qc - qe) = -1 := by
        calc
          (qa : ZMod d) + qb - qc - qe =
              ((qa : ZMod d) + qb) - ((qc : ZMod d) + qe) := by abel
          _ = ((qa : ZMod d) + qb) -
              (((qa : ZMod d) + qb) + 1) := by rw [← hq]
          _ = -1 := by abel
      have hudiff : (ra + rb) • u - (rc + re) • u = m • u := by
        have hsmul := congrArg (fun n : ℕ => n • u) heq
        simp only [add_nsmul] at hsmul ⊢
        rw [hsmul]
        abel
      convert hmemAgg using 1
      rw [hqdiff, hudiff]
      abel
    exact hcarry (by simpa using H.neg_mem hneg)
  · exfalso
    have habVal : a.val + b.val = m * (qa + qb) + (ra + rb) := by
      rw [haVal, hbVal, Nat.mul_add]
      omega
    have hceVal : c.val + e.val = m * (qc + qe) + (rc + re) := by
      rw [hcVal, heVal, Nat.mul_add]
      omega
    have hexpanded :
        m * (qa + qb) + (ra + rb) ≡
          m * (qc + qe + 1) + (ra + rb) [MOD m * d] := by
      have h := htotal
      rw [habVal, hceVal, heq] at h
      convert h using 1 <;> ring
    have hmul : m * (qa + qb) ≡ m * (qc + qe + 1) [MOD m * d] :=
      Nat.ModEq.add_right_cancel' (ra + rb) hexpanded
    have hqmod : qa + qb ≡ qc + qe + 1 [MOD d] :=
      Nat.ModEq.mul_left_cancel' hm.ne' hmul
    have hq : (qa : ZMod d) + qb = (qc : ZMod d) + qe + 1 := by
      have := ZMod.natCast_eq_natCast_iff _ _ d |>.mpr hqmod
      simpa only [Nat.cast_add, Nat.cast_one] using this
    have hpos : (1 : ZMod d) + m • u ∈ H := by
      have hqdiff : ((qa : ZMod d) + qb - qc - qe) = 1 := by
        calc
          (qa : ZMod d) + qb - qc - qe =
              ((qa : ZMod d) + qb) - ((qc : ZMod d) + qe) := by abel
          _ = (((qc : ZMod d) + qe) + 1) -
              ((qc : ZMod d) + qe) := by rw [hq]
          _ = 1 := by abel
      have hudiff : (ra + rb) • u - (rc + re) • u = -(m • u) := by
        have hsmul := congrArg (fun n : ℕ => n • u) heq
        simp only [add_nsmul] at hsmul ⊢
        rw [hsmul]
        abel
      convert hmemAgg using 1
      rw [hqdiff, hudiff]
      abel
    exact hcarry hpos

/-- Under the affine-fibre formula and the forbidden-carry condition,
quotient--remainder coordinates preserve and reflect all pair-sum
relations, without any no-wrap hypothesis on the full set. -/
lemma zmodQuotRemLift_add_eq_iff_of_affine_noCarry
    {m d : ℕ} [NeZero d] [NeZero (m * d)]
    (hm : 0 < m) {H : AddSubgroup (ZMod d)} {u v : ZMod d}
    {a b c e : ZMod (m * d)}
    (ha : (a.val / m : ZMod d) - ((a.val % m) • u + v) ∈ H)
    (hb : (b.val / m : ZMod d) - ((b.val % m) • u + v) ∈ H)
    (hc : (c.val / m : ZMod d) - ((c.val % m) • u + v) ∈ H)
    (he : (e.val / m : ZMod d) - ((e.val % m) • u + v) ∈ H)
    (hcarry : (1 : ZMod d) + m • u ∉ H) :
    zmodQuotRemLift m d a + zmodQuotRemLift m d b =
        zmodQuotRemLift m d c + zmodQuotRemLift m d e ↔
      a + b = c + e := by
  constructor
  · intro hlift
    have hr : a.val % m + b.val % m = c.val % m + e.val % m :=
      congrArg Prod.fst hlift
    have hq : (a.val / m : ZMod d) + (b.val / m : ZMod d) =
        (c.val / m : ZMod d) + (e.val / m : ZMod d) :=
      congrArg Prod.snd hlift
    have haRec := zmodQuotientEmbedding_quotient_add_remainder
      (m := m) (d := d) a
    have hbRec := zmodQuotientEmbedding_quotient_add_remainder
      (m := m) (d := d) b
    have hcRec := zmodQuotientEmbedding_quotient_add_remainder
      (m := m) (d := d) c
    have heRec := zmodQuotientEmbedding_quotient_add_remainder
      (m := m) (d := d) e
    calc
      a + b =
          zmodQuotientEmbedding m d (a.val / m : ZMod d) +
              ((a.val % m : ℕ) : ZMod (m * d)) +
            (zmodQuotientEmbedding m d (b.val / m : ZMod d) +
              ((b.val % m : ℕ) : ZMod (m * d))) := by
              rw [haRec, hbRec]
      _ = zmodQuotientEmbedding m d
            ((a.val / m : ZMod d) + (b.val / m : ZMod d)) +
            ((a.val % m + b.val % m : ℕ) : ZMod (m * d)) := by
              simp only [map_add, Nat.cast_add]
              abel
      _ = zmodQuotientEmbedding m d
            ((c.val / m : ZMod d) + (e.val / m : ZMod d)) +
            ((c.val % m + e.val % m : ℕ) : ZMod (m * d)) := by
              rw [hq, hr]
      _ = c + e := by
              rw [map_add, Nat.cast_add]
              calc
                zmodQuotientEmbedding m d (c.val / m : ZMod d) +
                    zmodQuotientEmbedding m d (e.val / m : ZMod d) +
                    (((c.val % m : ℕ) : ZMod (m * d)) +
                      ((e.val % m : ℕ) : ZMod (m * d))) =
                    (zmodQuotientEmbedding m d (c.val / m : ZMod d) +
                      ((c.val % m : ℕ) : ZMod (m * d))) +
                    (zmodQuotientEmbedding m d (e.val / m : ZMod d) +
                      ((e.val % m : ℕ) : ZMod (m * d))) := by abel
                _ = c + e := by rw [hcRec, heRec]
  · intro hsum
    have hr := firstCoordinate_pairSum_eq_of_affine_noCarry hm
      ha hb hc he hcarry hsum
    apply Prod.ext hr
    change (a.val / m : ZMod d) + (b.val / m : ZMod d) =
      (c.val / m : ZMod d) + (e.val / m : ZMod d)
    apply zmodQuotientEmbedding_injective hm
    rw [map_add, map_add]
    have haRec := zmodQuotientEmbedding_quotient_add_remainder
      (m := m) (d := d) a
    have hbRec := zmodQuotientEmbedding_quotient_add_remainder
      (m := m) (d := d) b
    have hcRec := zmodQuotientEmbedding_quotient_add_remainder
      (m := m) (d := d) c
    have heRec := zmodQuotientEmbedding_quotient_add_remainder
      (m := m) (d := d) e
    calc
      zmodQuotientEmbedding m d (a.val / m : ZMod d) +
          zmodQuotientEmbedding m d (b.val / m : ZMod d) =
          (zmodQuotientEmbedding m d (a.val / m : ZMod d) +
            ((a.val % m : ℕ) : ZMod (m * d))) +
          (zmodQuotientEmbedding m d (b.val / m : ZMod d) +
            ((b.val % m : ℕ) : ZMod (m * d))) -
          ((a.val % m + b.val % m : ℕ) : ZMod (m * d)) := by
            rw [Nat.cast_add]
            abel
      _ =
          (a + b) - ((a.val % m + b.val % m : ℕ) : ZMod (m * d)) := by
            rw [haRec, hbRec]
      _ = (c + e) -
          ((c.val % m + e.val % m : ℕ) : ZMod (m * d)) := by
            rw [hsum, hr]
      _ =
          (zmodQuotientEmbedding m d (c.val / m : ZMod d) +
            ((c.val % m : ℕ) : ZMod (m * d))) +
          (zmodQuotientEmbedding m d (e.val / m : ZMod d) +
            ((e.val % m : ℕ) : ZMod (m * d))) -
          ((c.val % m + e.val % m : ℕ) : ZMod (m * d)) := by
            rw [hcRec, heRec]
      _ = zmodQuotientEmbedding m d (c.val / m : ZMod d) +
          zmodQuotientEmbedding m d (e.val / m : ZMod d) := by
            rw [Nat.cast_add]
            abel

/-- The full PL5 conclusion and the carry obstruction package the partial
lift as an order-two Freiman isomorphism on the original full set. -/
theorem zmodQuotRemLift_isAddFreimanIso_of_affine_noCarry
    {m d : ℕ} [NeZero d] [NeZero (m * d)]
    (hm : 0 < m) (B : Finset (ZMod (m * d)))
    {H : AddSubgroup (ZMod d)} {u v : ZMod d}
    (haffine : ∀ z ∈ B,
      (z.val / m : ZMod d) - ((z.val % m) • u + v) ∈ H)
    (hcarry : (1 : ZMod d) + m • u ∉ H) :
    IsAddFreimanIso 2 (B : Set (ZMod (m * d)))
      ((zmodQuotRemLift m d) '' (B : Set (ZMod (m * d))))
      (zmodQuotRemLift m d) := by
  rw [isAddFreimanIso_two]
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx
      exact ⟨x, hx, rfl⟩
    · exact (zmodQuotRemLift_injective hm).injOn
    · intro y hy
      exact hy
  · intro a ha b hb c hc e he
    exact zmodQuotRemLift_add_eq_iff_of_affine_noCarry hm
      (haffine a ha) (haffine b hb) (haffine c hc) (haffine e he) hcarry

/-- End-to-end algebraic PL4 → PL5 completion once the carry-cell count has
returned lifted ternary collisions. -/
theorem partialLift_carryCompletion
    {m d : ℕ} [NeZero d] [NeZero (m * d)]
    (hm : 0 < m) {B C : Finset (ZMod (m * d))}
    {H : AddSubgroup (ZMod d)} {u v : ZMod d}
    (hcore : ∀ c ∈ C,
      (c.val / m : ZMod d) - ((c.val % m) • u + v) ∈ H)
    (hcollision : ∀ z ∈ B,
      ∃ c₁ ∈ C, ∃ c₂ ∈ C, ∃ c₃ ∈ C,
        zmodQuotRemLift m d z + zmodQuotRemLift m d c₃ =
          zmodQuotRemLift m d c₁ + zmodQuotRemLift m d c₂)
    (hcarry : (1 : ZMod d) + m • u ∉ H) :
    (∀ z ∈ B,
      (z.val / m : ZMod d) - ((z.val % m) • u + v) ∈ H) ∧
    IsAddFreimanIso 2 (B : Set (ZMod (m * d)))
      ((zmodQuotRemLift m d) '' (B : Set (ZMod (m * d))))
      (zmodQuotRemLift m d) := by
  have haffine := affine_quotientFibers_of_zeroCarry_core_completion
    hcore hcollision
  exact ⟨haffine,
    zmodQuotRemLift_isAddFreimanIso_of_affine_noCarry hm B haffine hcarry⟩

/-- The same completion, stated in the geometric form used by the cyclic
inverse theorem: every point of the full affine image belongs to the one
cyclic progression of embedded `H`-cosets with the PL4 start and step. -/
theorem partialLift_carryCompletion_cyclicProgression
    {m d : ℕ} [NeZero d] [NeZero (m * d)]
    (hm : 0 < m) {B C : Finset (ZMod (m * d))}
    {H : AddSubgroup (ZMod d)} {u v : ZMod d}
    (hcore : ∀ c ∈ C,
      (c.val / m : ZMod d) - ((c.val % m) • u + v) ∈ H)
    (hcollision : ∀ z ∈ B,
      ∃ c₁ ∈ C, ∃ c₂ ∈ C, ∃ c₃ ∈ C,
        zmodQuotRemLift m d z + zmodQuotRemLift m d c₃ =
          zmodQuotRemLift m d c₁ + zmodQuotRemLift m d c₂)
    (hcarry : (1 : ZMod d) + m • u ∉ H) :
    B ⊆ cyclicCosetProgression
        (H.map (zmodQuotientEmbedding m d))
        (zmodQuotientEmbedding m d v)
        ((1 : ZMod (m * d)) + zmodQuotientEmbedding m d u) m ∧
      IsAddFreimanIso 2 (B : Set (ZMod (m * d)))
        ((zmodQuotRemLift m d) '' (B : Set (ZMod (m * d))))
        (zmodQuotRemLift m d) := by
  have hcompleted := partialLift_carryCompletion hm hcore hcollision hcarry
  refine ⟨?_, hcompleted.2⟩
  apply zmodQuotRem_affineFiber_subset_cyclicCosetProgression
  intro z hz
  exact ⟨Nat.mod_lt _ hm, hcompleted.1 z hz⟩

/-- The `m` consecutive cosets generated by a step whose `m`-fold multiple
returns to `K` form an additive subgroup. -/
noncomputable def wrappedCosetProgressionSubgroup
    {n : ℕ} [NeZero n] (K : AddSubgroup (ZMod n))
    (s : ZMod n) (m : ℕ) (hm : 0 < m) (hwrap : m • s ∈ K) :
    AddSubgroup (ZMod n) where
  carrier := ↑(cyclicCosetProgression K 0 s m)
  zero_mem' := by
    change 0 ∈ cyclicCosetProgression K 0 s m
    rw [mem_cyclicCosetProgression_iff]
    exact ⟨0, hm, by simp⟩
  add_mem' := by
    intro x y hx hy
    change x ∈ cyclicCosetProgression K 0 s m at hx
    change y ∈ cyclicCosetProgression K 0 s m at hy
    change x + y ∈ cyclicCosetProgression K 0 s m
    rw [mem_cyclicCosetProgression_iff] at hx hy ⊢
    obtain ⟨i, hi, hxi⟩ := hx
    obtain ⟨j, hj, hyj⟩ := hy
    by_cases hij : i + j < m
    · refine ⟨i + j, hij, ?_⟩
      have hadd := K.add_mem hxi hyj
      convert hadd using 1 <;> simp only [zero_add, add_nsmul] <;> abel
    · have hmij : m ≤ i + j := Nat.le_of_not_gt hij
      refine ⟨i + j - m, by omega, ?_⟩
      have hadd := K.add_mem hxi hyj
      have hboth := K.add_mem hadd hwrap
      have hsmul : (i + j - m) • s = (i + j) • s - m • s := by
        rw [eq_sub_iff_add_eq]
        rw [← add_nsmul, Nat.sub_add_cancel hmij]
      have heq : x + y - (0 + (i + j - m) • s) =
          (x - (0 + i • s)) + (y - (0 + j • s)) + m • s := by
        simp only [zero_add]
        rw [hsmul, add_nsmul]
        abel
      rw [heq]
      exact hboth
  neg_mem' := by
    intro x hx
    change x ∈ cyclicCosetProgression K 0 s m at hx
    change -x ∈ cyclicCosetProgression K 0 s m
    rw [mem_cyclicCosetProgression_iff] at hx ⊢
    obtain ⟨i, hi, hxi⟩ := hx
    by_cases hi0 : i = 0
    · subst i
      exact ⟨0, hm, by simpa using K.neg_mem hxi⟩
    · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
      refine ⟨m - i, by omega, ?_⟩
      have hsub := K.sub_mem (K.neg_mem hxi) hwrap
      have hsmul : (m - i) • s = m • s - i • s := by
        rw [eq_sub_iff_add_eq]
        rw [add_comm, ← add_nsmul, Nat.add_sub_of_le hi.le]
      have heq : -x - (0 + (m - i) • s) =
          -(x - (0 + i • s)) - m • s := by
        simp only [zero_add]
        rw [hsmul]
        abel
      rw [heq]
      exact hsub

lemma subgroupFinset_wrappedCosetProgressionSubgroup
    {n : ℕ} [NeZero n] (K : AddSubgroup (ZMod n))
    (s : ZMod n) (m : ℕ) (hm : 0 < m) (hwrap : m • s ∈ K) :
    subgroupFinset (wrappedCosetProgressionSubgroup K s m hm hwrap) =
      cyclicCosetProgression K 0 s m := by
  ext x
  rw [mem_subgroupFinset]
  rfl

/-- If the fibre subgroup has fewer than `d` elements, the wrapped progression
subgroup in `ZMod (m*d)` is proper. -/
lemma wrappedCosetProgressionSubgroup_ne_top
    {m d : ℕ} [NeZero d] [NeZero (m * d)] (hm : 0 < m)
    (K : AddSubgroup (ZMod (m * d))) (s : ZMod (m * d))
    (hwrap : m • s ∈ K) (hKcard : Nat.card K < d) :
    wrappedCosetProgressionSubgroup K s m hm hwrap ≠ ⊤ := by
  let L := wrappedCosetProgressionSubgroup K s m hm hwrap
  have hcard : Nat.card L ≤ m * Nat.card K := by
    calc
      Nat.card L = (subgroupFinset L).card := (card_subgroupFinset L).symm
      _ = (cyclicCosetProgression K 0 s m).card := by
        rw [subgroupFinset_wrappedCosetProgressionSubgroup]
      _ ≤ m * Nat.card K := cyclicCosetProgression_card_le K 0 s m
  have hlt : Nat.card L < m * d :=
    hcard.trans_lt ((Nat.mul_lt_mul_left hm).2 hKcard)
  intro htop
  change L = ⊤ at htop
  have htopcard : Nat.card L = m * d := by
    rw [htop]
    simp
  omega

/-- If the carry class closes the `m`-step progression, affine fibres put the
whole set in a coset of a proper subgroup. -/
theorem exists_proper_coset_of_affine_fibers_and_carry
    {m d : ℕ} [NeZero d] [NeZero (m * d)] (hm : 0 < m)
    (B : Finset (ZMod (m * d)))
    (H : AddSubgroup (ZMod d)) (u v : ZMod d)
    (hHcard : Nat.card H < d)
    (haffine : ∀ z ∈ B,
      (z.val / m : ZMod d) - ((z.val % m) • u + v) ∈ H)
    (hcarry : (1 : ZMod d) + m • u ∈ H) :
    ∃ L : AddSubgroup (ZMod (m * d)), L ≠ ⊤ ∧
      ∃ a : ZMod (m * d),
        (B : Set (ZMod (m * d))) ⊆ a +ᵥ (L : Set (ZMod (m * d))) := by
  classical
  let K := H.map (zmodQuotientEmbedding m d)
  let s : ZMod (m * d) := 1 + zmodQuotientEmbedding m d u
  have hwrap : m • s ∈ K := by
    apply AddSubgroup.mem_map.mpr
    refine ⟨(1 : ZMod d) + m • u, hcarry, ?_⟩
    dsimp only [s]
    simp only [map_add, map_nsmul]
    have hone : zmodQuotientEmbedding m d (1 : ZMod d) =
        m • (1 : ZMod (m * d)) := by
      rw [show (1 : ZMod d) = ((1 : ℕ) : ZMod d) by simp]
      rw [zmodQuotientEmbedding_natCast]
      simp [nsmul_eq_mul]
    rw [hone, nsmul_add]
  let L := wrappedCosetProgressionSubgroup K s m hm hwrap
  have hKcard : Nat.card K = Nat.card H :=
    natCard_map_zmodQuotientEmbedding hm H
  have hLproper : L ≠ ⊤ := by
    apply wrappedCosetProgressionSubgroup_ne_top hm K s hwrap
    rw [hKcard]
    exact hHcard
  refine ⟨L, hLproper, zmodQuotientEmbedding m d v, ?_⟩
  intro z hz
  rw [Set.mem_vadd_set]
  refine ⟨z - zmodQuotientEmbedding m d v, ?_, by
    simp only [vadd_eq_add]
    abel⟩
  change z - zmodQuotientEmbedding m d v ∈
    cyclicCosetProgression K 0 s m
  rw [mem_cyclicCosetProgression_iff]
  refine ⟨z.val % m, Nat.mod_lt _ hm, ?_⟩
  apply AddSubgroup.mem_map.mpr
  refine ⟨(z.val / m : ZMod d) - ((z.val % m) • u + v),
    haffine z hz, ?_⟩
  have hzrec := zmodQuotientEmbedding_quotient_add_remainder
    (m := m) (d := d) z
  dsimp only [s]
  rw [map_sub, map_add, map_nsmul]
  calc
    zmodQuotientEmbedding m d (z.val / m : ZMod d) -
          ((z.val % m) • zmodQuotientEmbedding m d u +
            zmodQuotientEmbedding m d v) =
        (zmodQuotientEmbedding m d (z.val / m : ZMod d) +
            ((z.val % m : ℕ) : ZMod (m * d)) -
          zmodQuotientEmbedding m d v) -
          ((0 : ZMod (m * d)) + (z.val % m) •
            ((1 : ZMod (m * d)) + zmodQuotientEmbedding m d u)) := by
      simp only [zero_add, add_nsmul, nsmul_one, nsmul_eq_mul]
      ring
    _ = (z - zmodQuotientEmbedding m d v) -
          ((0 : ZMod (m * d)) + (z.val % m) •
            ((1 : ZMod (m * d)) + zmodQuotientEmbedding m d u)) := by
      rw [hzrec]
    _ = (z - zmodQuotientEmbedding m d v) -
          (0 + (z.val % m) • s) := by rfl

/-- Minimality against proper subgroup cosets excludes exactly the carry class
which would close the cyclic progression. -/
theorem noCarryClass_of_affine_fibers_minimal
    {m d : ℕ} [NeZero d] [NeZero (m * d)] (hm : 0 < m)
    (B : Finset (ZMod (m * d)))
    (H : AddSubgroup (ZMod d)) (u v : ZMod d)
    (hHcard : Nat.card H < d)
    (hminimal : NotContainedInProperCoset B)
    (haffine : ∀ z ∈ B,
      (z.val / m : ZMod d) - ((z.val % m) • u + v) ∈ H) :
    (1 : ZMod d) + m • u ∉ H := by
  intro hcarry
  obtain ⟨L, hLproper, a, hBa⟩ :=
    exists_proper_coset_of_affine_fibers_and_carry hm B H u v hHcard
      haffine hcarry
  exact hminimal L hLproper a hBa

/-- The carry class is already excluded at the affine-core stage.  Indeed,
if it belonged to `H`, the affine core would lie in a coset of the proper
wrapped subgroup.  The exact dense-core/small-doubling collision estimate
then propagates that same coset containment from `C` to every point of `B`,
contradicting the minimal-subgroup reduction.  No affine conclusion for the
points of `B \ C` is used here. -/
theorem noCarryClass_of_affine_core_minimal
    {m d : ℕ} [NeZero d] [NeZero (m * d)] (hm : 0 < m)
    {B C : Finset (ZMod (m * d))}
    (hB : B.Nonempty)
    (hCB : C ⊆ B)
    (hdense : 33 * B.card ≤ 40 * C.card)
    (hsmall : 25 * (B + B).card ≤ 51 * B.card)
    (hcoreSum : 3 * C.card ≤ 2 * (C + C).card)
    (H : AddSubgroup (ZMod d)) (u v : ZMod d)
    (hHcard : Nat.card H < d)
    (hminimal : NotContainedInProperCoset B)
    (hcoreAffine : ∀ c ∈ C,
      (c.val / m : ZMod d) - ((c.val % m) • u + v) ∈ H) :
    (1 : ZMod d) + m • u ∉ H := by
  have hcollision := exists_core_ternary_collision_of_dense_smallDoubling
    hB hCB hdense hsmall hcoreSum
  intro hcarry
  obtain ⟨L, hLproper, a, hCcoset⟩ :=
    exists_proper_coset_of_affine_fibers_and_carry
      hm C H u v hHcard hcoreAffine hcarry
  apply hminimal L hLproper a
  intro z hz
  obtain ⟨c₁, hc₁, c₂, hc₂, c₃, hc₃, hrelation⟩ :=
    hcollision z hz
  have hc₁coset := hCcoset (by simpa using hc₁)
  have hc₂coset := hCcoset (by simpa using hc₂)
  have hc₃coset := hCcoset (by simpa using hc₃)
  rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hc₁coset hc₂coset hc₃coset ⊢
  simp only [vadd_eq_add] at hc₁coset hc₂coset hc₃coset ⊢
  have hclosed := L.sub_mem (L.add_mem hc₁coset hc₂coset) hc₃coset
  have hz : z = c₁ + c₂ - c₃ := by
    rw [eq_sub_iff_add_eq]
    exact hrelation
  have hzform : -a + z = (-a + c₁) + (-a + c₂) - (-a + c₃) := by
    rw [hz]
    abel
  rw [hzform]
  exact hclosed

/-- Source-level carry completion: a zero-carry core completion first extends
the affine fibre description to `B`; minimality then supplies the carry
obstruction, yielding both the cyclic progression and preservation of pair
sums by the partial lift. -/
theorem partialLift_carryCompletion_minimal
    {m d : ℕ} [NeZero d] [NeZero (m * d)]
    (hm : 0 < m) {B C : Finset (ZMod (m * d))}
    {H : AddSubgroup (ZMod d)} {u v : ZMod d}
    (hHcard : Nat.card H < d)
    (hminimal : NotContainedInProperCoset B)
    (hcore : ∀ c ∈ C,
      (c.val / m : ZMod d) - ((c.val % m) • u + v) ∈ H)
    (hcollision : ∀ z ∈ B,
      ∃ c₁ ∈ C, ∃ c₂ ∈ C, ∃ c₃ ∈ C,
        zmodQuotRemLift m d z + zmodQuotRemLift m d c₃ =
          zmodQuotRemLift m d c₁ + zmodQuotRemLift m d c₂) :
    (∀ z ∈ B,
      (z.val / m : ZMod d) - ((z.val % m) • u + v) ∈ H) ∧
      B ⊆ cyclicCosetProgression
        (H.map (zmodQuotientEmbedding m d))
        (zmodQuotientEmbedding m d v)
        ((1 : ZMod (m * d)) + zmodQuotientEmbedding m d u) m ∧
      IsAddFreimanIso 2 (B : Set (ZMod (m * d)))
        ((zmodQuotRemLift m d) '' (B : Set (ZMod (m * d))))
        (zmodQuotRemLift m d) := by
  have haffine := affine_quotientFibers_of_zeroCarry_core_completion
    hcore hcollision
  have hcarry := noCarryClass_of_affine_fibers_minimal
    hm B H u v hHcard hminimal haffine
  have hcompleted := partialLift_carryCompletion_cyclicProgression
    hm hcore hcollision hcarry
  exact ⟨haffine, hcompleted⟩

/-- Carry completion with a noncircular source-level dependency graph.  The
carry obstruction is proved solely from the affine core, the exact
dense-core estimates, and minimality, before the zero-carry completion
hypothesis is used. -/
theorem partialLift_carryCompletion_of_core_bounds_minimal
    {m d : ℕ} [NeZero d] [NeZero (m * d)]
    (hm : 0 < m) {B C : Finset (ZMod (m * d))}
    {H : AddSubgroup (ZMod d)} {u v : ZMod d}
    (hB : B.Nonempty)
    (hCB : C ⊆ B)
    (hdense : 33 * B.card ≤ 40 * C.card)
    (hsmall : 25 * (B + B).card ≤ 51 * B.card)
    (hcoreSum : 3 * C.card ≤ 2 * (C + C).card)
    (hHcard : Nat.card H < d)
    (hminimal : NotContainedInProperCoset B)
    (hcore : ∀ c ∈ C,
      (c.val / m : ZMod d) - ((c.val % m) • u + v) ∈ H)
    (hcollision : ∀ z ∈ B,
      ∃ c₁ ∈ C, ∃ c₂ ∈ C, ∃ c₃ ∈ C,
        zmodQuotRemLift m d z + zmodQuotRemLift m d c₃ =
          zmodQuotRemLift m d c₁ + zmodQuotRemLift m d c₂) :
    (∀ z ∈ B,
      (z.val / m : ZMod d) - ((z.val % m) • u + v) ∈ H) ∧
      B ⊆ cyclicCosetProgression
        (H.map (zmodQuotientEmbedding m d))
        (zmodQuotientEmbedding m d v)
        ((1 : ZMod (m * d)) + zmodQuotientEmbedding m d u) m ∧
      IsAddFreimanIso 2 (B : Set (ZMod (m * d)))
        ((zmodQuotRemLift m d) '' (B : Set (ZMod (m * d))))
        (zmodQuotRemLift m d) := by
  have hcarry := noCarryClass_of_affine_core_minimal
    hm hB hCB hdense hsmall hcoreSum H u v hHcard hminimal hcore
  have haffine := affine_quotientFibers_of_zeroCarry_core_completion
    hcore hcollision
  have hcompleted := partialLift_carryCompletion_cyclicProgression
    hm hcore hcollision hcarry
  exact ⟨haffine, hcompleted⟩

end Erdos360

#print axioms Erdos360.exists_core_ternary_collision_of_dense_smallDoubling
#print axioms Erdos360.partialLift_carryCompletion
#print axioms Erdos360.partialLift_carryCompletion_cyclicProgression
#print axioms Erdos360.partialLift_carryCompletion_minimal
#print axioms Erdos360.noCarryClass_of_affine_core_minimal
#print axioms Erdos360.partialLift_carryCompletion_of_core_bounds_minimal
