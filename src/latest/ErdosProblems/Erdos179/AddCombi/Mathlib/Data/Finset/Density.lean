module

public import Mathlib.Data.Finset.Density
public import Mathlib.Data.Fintype.Prod

import ErdosProblems.Erdos179.AddCombi.Mathlib.Algebra.Order.Ring.NNRat

public section

namespace Finset
variable {K α β : Type*} [DivisionRing K] [CharZero K] [Fintype α] [Fintype β]
  {s t : Finset α} {a : α}


@[simp] lemma dens_product (s : Finset α) (t : Finset β) : (s ×ˢ t).dens = s.dens * t.dens := by
  simp [dens, mul_div_mul_comm]

variable [DecidableEq α]

lemma dens_union_eq_dens_add_dens : (s ∪ t).dens = s.dens + t.dens ↔ Disjoint s t := by
  rw [← dens_union_add_dens_inter]; simp [disjoint_iff_inter_eq_empty]

@[grind =]
lemma dens_sdiff_of_subset (h : s ⊆ t) : (t \ s).dens = t.dens - s.dens := by
  suffices (t \ s).dens = (t \ s ∪ s).dens - s.dens by rwa [sdiff_union_of_subset h] at this
  rw [dens_union_of_disjoint sdiff_disjoint, add_tsub_cancel_right]

lemma cast_dens_inter : ((s ∩ t).dens : K) = s.dens + t.dens - (s ∪ t).dens := by
  rw [eq_sub_iff_add_eq]; norm_cast; exact dens_inter_add_dens_union ..

lemma cast_dens_union : ((s ∪ t).dens : K) = s.dens + t.dens - (s ∩ t).dens := by
  rw [eq_sub_iff_add_eq]; norm_cast; exact dens_union_add_dens_inter ..

lemma cast_dens_sdiff (h : s ⊆ t) : ((t \ s).dens : K) = t.dens - s.dens := by
  rw [dens_sdiff_of_subset h, NNRat.cast_sub (dens_mono h)]

end Finset
