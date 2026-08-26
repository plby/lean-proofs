/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma65

/-!
# Two-row allocation with the matching-edge rounding cost explicit

Each row total pays the two source demands, two reserves and two per-edge
caps. Fact 6.4 then gives a genuine disjoint matching partition.
-/

open scoped BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoTwoRowSurplusAllocation

open Finset Erdos547b.ZhaoLemma65

theorem exists_twoRowSurplus_univ {E : Type*} [Fintype E] [DecidableEq E]
    (a b : E → ℝ) (fa fb reserve cap : ℝ)
    (ha : ∀ e, 0 ≤ a e) (hb : ∀ e, 0 ≤ b e)
    (haCap : ∀ e, a e ≤ cap) (hbCap : ∀ e, b e ≤ cap)
    (hfa : 0 ≤ fa) (hfb : 0 ≤ fb) (hreserve : 0 ≤ reserve) (hcap : 0 < cap)
    (hA : fa + fb + 2 * reserve + 2 * cap ≤ ∑ e, a e)
    (hB : fa + fb + 2 * reserve + 2 * cap ≤ ∑ e, b e) :
    ∃ Ea Eb : Finset E, Disjoint Ea Eb ∧ Ea ∪ Eb = Finset.univ ∧
      fa + reserve < ∑ e ∈ Ea, a e ∧ fb + reserve < ∑ e ∈ Eb, b e := by
  let D := fa + fb + 2 * reserve + 2 * cap
  have hD : 0 < D := by dsimp only [D]; positivity
  have hs : 0 < fa + reserve + cap := by positivity
  have ht : 0 < fb + reserve + cap := by positivity
  have hratio : (fa + reserve + cap) / (∑ e, a e) + (fb + reserve + cap) / (∑ e, b e) ≤ 1 := by
    have hfirst := div_le_div_of_nonneg_left hs.le hD hA
    have hsecond := div_le_div_of_nonneg_left ht.le hD hB
    have hsum : (fa + reserve + cap) / D + (fb + reserve + cap) / D = 1 := by
      rw [← add_div]
      have heq : fa + reserve + cap + (fb + reserve + cap) = D := by dsimp only [D]; ring
      rw [heq, div_self hD.ne']
    linarith only [hfirst, hsecond, hsum]
  obtain ⟨Ea, Eb, hdis, hcover, ha, _, hb⟩ := zhaoFact6_4 a b cap (∑ e, a e) (∑ e, b e)
    (fa + reserve + cap) (fb + reserve + cap) ha hb haCap hbCap rfl rfl
    (hD.trans_le hA) (hD.trans_le hB) hs ht hratio
  exact ⟨Ea, Eb, hdis, hcover, by linarith only [ha], by linarith only [hb, hcap]⟩

theorem exists_twoRowSurplus {E : Type*} [DecidableEq E]
    (M : Finset E) (a b : E → ℝ) (fa fb reserve cap : ℝ)
    (ha : ∀ e ∈ M, 0 ≤ a e) (hb : ∀ e ∈ M, 0 ≤ b e)
    (haCap : ∀ e ∈ M, a e ≤ cap) (hbCap : ∀ e ∈ M, b e ≤ cap)
    (hfa : 0 ≤ fa) (hfb : 0 ≤ fb) (hreserve : 0 ≤ reserve) (hcap : 0 < cap)
    (hA : fa + fb + 2 * reserve + 2 * cap ≤ ∑ e ∈ M, a e)
    (hB : fa + fb + 2 * reserve + 2 * cap ≤ ∑ e ∈ M, b e) :
    ∃ Ea Eb : Finset E, Ea ⊆ M ∧ Eb ⊆ M ∧ Disjoint Ea Eb ∧ Ea ∪ Eb = M ∧
      fa + reserve < ∑ e ∈ Ea, a e ∧ fb + reserve < ∑ e ∈ Eb, b e := by
  have hsum (w : E → ℝ) : (∑ e : M, w e) = ∑ e ∈ M, w e := by
    rw [Finset.univ_eq_attach, Finset.sum_attach]
  obtain ⟨Pa, Pb, hdis, hcover, hPa, hPb⟩ := exists_twoRowSurplus_univ
    (fun e : M => a e) (fun e : M => b e) fa fb reserve cap
    (fun e => ha e e.2) (fun e => hb e e.2) (fun e => haCap e e.2) (fun e => hbCap e e.2)
    hfa hfb hreserve hcap (by simpa only [hsum] using hA) (by simpa only [hsum] using hB)
  have hsub (P : Finset {e // e ∈ M}) : P.image Subtype.val ⊆ M := by
    intro e he
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp he
    exact x.2
  have himage (P : Finset {e // e ∈ M}) (w : E → ℝ) :
      (∑ e ∈ P.image Subtype.val, w e) = ∑ e ∈ P, w e :=
    Finset.sum_image (fun x _ y _ h => Subtype.ext h)
  refine ⟨Pa.image Subtype.val, Pb.image Subtype.val, hsub Pa, hsub Pb, ?_, ?_, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro e heA heB
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp heA
    obtain ⟨y, hy, hye⟩ := Finset.mem_image.mp heB
    have hxy : x = y := Subtype.ext (hxe.trans hye.symm)
    exact Finset.disjoint_left.mp hdis hx (hxy.symm ▸ hy)
  · rw [← Finset.image_union, hcover, Finset.univ_eq_attach, Finset.attach_image_val]
  · simpa only [himage] using hPa
  · simpa only [himage] using hPb

end Erdos547b.ZhaoTwoRowSurplusAllocation

#print axioms Erdos547b.ZhaoTwoRowSurplusAllocation.exists_twoRowSurplus_univ
#print axioms Erdos547b.ZhaoTwoRowSurplusAllocation.exists_twoRowSurplus
