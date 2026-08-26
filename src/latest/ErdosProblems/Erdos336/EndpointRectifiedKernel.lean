import ErdosProblems.Erdos336.RelativePrimitiveEndpointAssembly
import ErdosProblems.Erdos336.RectifiedSaturationBridge

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

set_option maxHeartbeats 1000000

open scoped Pointwise

variable {N m : ℕ} [NeZero N] [NeZero m]

/-- The vertical part of the endpoint-quotient stabilizer of a normalized
rectified graph is killed by the original rectifying homomorphism. -/
theorem endpointVerticalPart_le_rectifyingKernel
    (A : Finset (ZMod N)) (π : ZMod N →+ ZMod m)
    (houter : ∀ x ∈ A,
      ∃ q : ℕ, 2 * q < m ∧ π x = (q : ZMod m))
    (T : Finset (ℤ × ZMod N)) (hT : T = rectifiedLift A π 0)
    (hzero : ((0 : ℤ), 0) ∈ T) (δ : ℤ × ZMod N) (hδT : δ ∈ T) :
    let Δ := AddSubgroup.zmultiples δ
    let q : (ℤ × ZMod N) →+ ((ℤ × ZMod N) ⧸ Δ) := QuotientAddGroup.mk' Δ
    let B := T.image q
    let Fsub : AddSubgroup ((ℤ × ZMod N) ⧸ Δ) :=
      AddAction.stabilizer ((ℤ × ZMod N) ⧸ Δ) (B + B : Set ((ℤ × ZMod N) ⧸ Δ))
    endpointVerticalPart δ Fsub ≤ π.ker := by
  classical
  dsimp
  let Δ := AddSubgroup.zmultiples δ
  let q : (ℤ × ZMod N) →+ ((ℤ × ZMod N) ⧸ Δ) := QuotientAddGroup.mk' Δ
  let B := T.image q
  let Fsub : AddSubgroup ((ℤ × ZMod N) ⧸ Δ) :=
    AddAction.stabilizer ((ℤ × ZMod N) ⧸ Δ) (B + B : Set ((ℤ × ZMod N) ⧸ Δ))
  let θ : (ℤ × ZMod N) →+ ZMod m :=
    { toFun := fun x => π x.2 - (x.1 : ZMod m)
      map_zero' := by simp
      map_add' := by
        intro x y
        simp only [Prod.snd_add, Prod.fst_add, map_add, Int.cast_add]
        abel }
  have hθT : ∀ x ∈ T, θ x = 0 := by
    intro x hx
    rw [hT] at hx
    obtain ⟨a, ha, hxa⟩ := mem_rectifiedLift.mp hx
    have hs := (halfIntervalLabel_spec π 0 a (by simpa using houter a ha)).2
    rw [hxa]
    dsimp [θ]
    rw [hs]
    simp
  have hθδ : θ δ = 0 := hθT δ hδT
  intro k hk
  change π k = 0
  change verticalEndpointHom δ k ∈ Fsub at hk
  have hzeroB : 0 ∈ B :=
    Finset.mem_image.mpr ⟨(0, 0), hzero, q.map_zero⟩
  have hzeroBB : 0 ∈ B + B :=
    Finset.mem_add.mpr ⟨0, hzeroB, 0, hzeroB, by simp⟩
  have hBBne : (B + B).Nonempty := ⟨0, hzeroBB⟩
  have hfFin : verticalEndpointHom δ k ∈ (B + B).addStab := by
    rw [← SetLike.mem_coe, Finset.coe_addStab hBBne]
    simpa [Fsub] using hk
  have hfBB : verticalEndpointHom δ k ∈ B + B := by
    have hshift := (Finset.mem_addStab' hBBne).mp hfFin hzeroBB
    simpa [vadd_eq_add] using hshift
  obtain ⟨u, huB, v, hvB, huv⟩ := Finset.mem_add.mp hfBB
  obtain ⟨y, hyT, hyu⟩ := Finset.mem_image.mp huB
  obtain ⟨z, hzT, hzv⟩ := Finset.mem_image.mp hvB
  have hqeq : q (y + z) = q (0, k) := by
    rw [q.map_add, hyu, hzv, huv]
    exact (verticalEndpointHom_apply δ k).symm
  have hmemΔ : (y + z) - (0, k) ∈ Δ :=
    (QuotientAddGroup.eq_iff_sub_mem).mp hqeq
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hmemΔ
  have hθy : θ y = 0 := hθT y hyT
  have hθz : θ z = 0 := hθT z hzT
  have heq := congrArg θ hn
  rw [map_zsmul, hθδ, zsmul_zero, map_sub, map_add, hθy, hθz] at heq
  have hneg : -π k = 0 := by
    simpa [θ] using heq.symm
  exact neg_eq_zero.mp hneg

end Erdos336
