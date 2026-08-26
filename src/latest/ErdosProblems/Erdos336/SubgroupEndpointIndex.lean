import ErdosProblems.Erdos336.SubgroupZProduct
import ErdosProblems.Erdos336.EndpointCyclicQuotient

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- Explicit index count for a subgroup `J=<g>+K` modulo an endpoint
displacement `δ=L g+kδ`. -/
theorem card_endpointQuotient_subgroup
    (J : AddSubgroup (ℤ × H)) (K : AddSubgroup H)
    (g δ : ℤ × H) (L : ℕ) (hL : 0 < L)
    (hgJ : g ∈ J) (hgpos : 0 < g.1)
    (hK : ∀ k ∈ K, (0, k) ∈ J)
    (hdecomp : ∀ x ∈ J, ∃ n : ℤ, ∃ k ∈ K,
      x = n • g + (0, k))
    (kδ : H) (hkδ : kδ ∈ K)
    (hδrep : δ = (L : ℤ) • g + (0, kδ))
    (F : Finset ((ℤ × H) ⧸ AddSubgroup.zmultiples δ))
    (hF : ∀ z, z ∈ F ↔ ∃ x ∈ J,
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples δ)) x = z) :
    F.card = L * (addSubgroupFinset K).card := by
  classical
  let Δ := AddSubgroup.zmultiples δ
  let q : (ℤ × H) →+ ((ℤ × H) ⧸ Δ) := QuotientAddGroup.mk' Δ
  letI : Fintype K := Fintype.ofFinite K
  let D := Fin L × K
  let e : D → ↥F := fun u =>
    ⟨q ((u.1.1 : ℤ) • g + (0, u.2.1)), by
      apply (hF _).mpr
      refine ⟨(u.1.1 : ℤ) • g + (0, u.2.1), ?_, rfl⟩
      exact J.add_mem (J.zsmul_mem hgJ _) (hK u.2.1 u.2.2)⟩
  have hδfst : δ.1 = (L : ℤ) * g.1 := by
    have h := congrArg Prod.fst hδrep
    change δ.1 = (L : ℤ) * g.1 + 0 at h
    simpa using h
  have heinj : Function.Injective e := by
    intro u v huv
    have hqeq := congrArg (fun z : ↥F => z.1) huv
    change q ((u.1.1 : ℤ) • g + (0, u.2.1)) =
      q ((v.1.1 : ℤ) • g + (0, v.2.1)) at hqeq
    have hmem : (((u.1.1 : ℤ) • g + (0, u.2.1)) -
        ((v.1.1 : ℤ) • g + (0, v.2.1))) ∈ Δ := by
      apply (QuotientAddGroup.eq_iff_sub_mem).mp
      simpa [q, Δ] using hqeq
    obtain ⟨t, ht⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
    have hfirst := congrArg Prod.fst ht
    change t * δ.1 =
      (u.1.1 : ℤ) * g.1 + 0 - ((v.1.1 : ℤ) * g.1 + 0) at hfirst
    ring_nf at hfirst
    rw [hδfst] at hfirst
    have hcancel : t * (L : ℤ) = (u.1.1 : ℤ) - (v.1.1 : ℤ) := by
      apply mul_right_cancel₀ (ne_of_gt hgpos)
      nlinarith
    have htzero : t = 0 := by
      have hu0 : (0 : ℤ) ≤ (u.1.1 : ℤ) := by positivity
      have hv0 : (0 : ℤ) ≤ (v.1.1 : ℤ) := by positivity
      have huL : (u.1.1 : ℤ) < L := by exact_mod_cast u.1.2
      have hvL : (v.1.1 : ℤ) < L := by exact_mod_cast v.1.2
      have hLInt : (0 : ℤ) < L := by exact_mod_cast hL
      nlinarith
    have huvval : u.1.1 = v.1.1 := by
      rw [htzero] at hcancel
      exact_mod_cast (by linarith : (u.1.1 : ℤ) = (v.1.1 : ℤ))
    have hsecond := congrArg Prod.snd ht
    rw [htzero] at hsecond
    simp only [zero_zsmul, Prod.snd_zero, Prod.snd_sub, Prod.snd_add] at hsecond
    have hiEq : (u.1.1 : ℤ) = (v.1.1 : ℤ) := by exact_mod_cast huvval
    rw [hiEq] at hsecond
    have hkval : u.2.1 = v.2.1 := by
      have hadd := sub_eq_zero.mp hsecond.symm
      exact add_left_cancel hadd
    apply Prod.ext
    · exact Fin.ext huvval
    · exact Subtype.ext hkval
  have hesurj : Function.Surjective e := by
    intro z
    obtain ⟨x, hxJ, hxz⟩ := (hF z.1).mp z.2
    obtain ⟨n, k, hk, hxrep⟩ := hdecomp x hxJ
    let t : ℤ := n / (L : ℤ)
    let rem : ℤ := n % (L : ℤ)
    have hLInt : (0 : ℤ) < L := by exact_mod_cast hL
    have hrem0 : 0 ≤ rem := Int.emod_nonneg _ (by omega)
    have hremL : rem < (L : ℤ) := Int.emod_lt_of_pos _ hLInt
    let i : ℕ := rem.toNat
    have hiInt : (i : ℤ) = rem := Int.toNat_of_nonneg hrem0
    have hiL : i < L := by
      have hiLInt : (i : ℤ) < (L : ℤ) := by rw [hiInt]; exact hremL
      exact_mod_cast hiLInt
    let k' : H := k - t • kδ
    have hk' : k' ∈ K := K.sub_mem hk (K.zsmul_mem hkδ t)
    let u : D := ⟨⟨i, hiL⟩, ⟨k', hk'⟩⟩
    refine ⟨u, Subtype.ext ?_⟩
    change q ((i : ℤ) • g + (0, k')) = z.1
    rw [← hxz, hxrep]
    apply (QuotientAddGroup.eq_iff_sub_mem).mpr
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨-t, ?_⟩
    dsimp [u, k', i]
    have hdiv := Int.ediv_mul_add_emod n (L : ℤ)
    have hn : n = t * (L : ℤ) + rem := by
      dsimp [t, rem]
      linarith
    rw [hiInt, hn, hδrep]
    have hv : ((0 : ℤ), k - t • kδ) =
        ((0 : ℤ), k) - t • ((0 : ℤ), kδ) := by
      ext <;> simp
    rw [hv]
    module
  have hbij : Function.Bijective e := ⟨heinj, hesurj⟩
  have hcard := Fintype.card_congr (Equiv.ofBijective e hbij)
  have hkcard : Fintype.card K = (addSubgroupFinset K).card := by
    exact Fintype.card_of_subtype (addSubgroupFinset K) (mem_addSubgroupFinset K)
  simpa [D, Fintype.card_prod, hkcard] using hcard.symm

end Erdos336
