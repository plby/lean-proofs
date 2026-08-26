import ErdosProblems.Erdos556.Reservoir
import ErdosProblems.Erdos556.PathOperations

/-!
# Long paths with prescribed endpoints

Two short reservoir connections attach prescribed endpoints to a long path
outside the reservoir. The second connection avoids the whole first one.
-/

namespace Erdos556

open SimpleGraph Finset

theorem exists_path_with_prescribed_ends_of_reservoir {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} (L : ℕ) (R : Finset V)
    (hres : ∀ x y S, S.card ≤ L + 1 → ShortConnection G L x y (R \ S))
    (u v : V) (huv : u ≠ v) {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (hlen : 0 < p.length) (hav : ∀ x ∈ p.support, x ∉ R ∧ x ≠ u ∧ x ≠ v) :
    ∃ q : G.Walk u v, q.IsPath ∧ p.length ≤ q.length ∧ q.length ≤ p.length + 2 * L := by
  classical
  have hab : a ≠ b := by
    intro h
    have hz := ((hp.nil_iff_eq).mpr h).length_eq_zero
    omega
  have hau : a ≠ u := (hav a p.start_mem_support).2.1
  have hav' : a ≠ v := (hav a p.start_mem_support).2.2
  have hbu : b ≠ u := (hav b p.end_mem_support).2.1
  obtain ⟨r, hr, hrlen, hrR⟩ := hres u a {v} (by simp)
  have hrv : v ∉ r.support := by
    intro hv
    have h := hrR v hv huv.symm hav'.symm
    exact (mem_sdiff.mp h).2 (mem_singleton_self v)
  have hrP (z : V) (hzr : z ∈ r.support) (hzp : z ∈ p.support) : z = a := by
    by_contra hza
    have hzu := (hav z hzp).2.1
    exact (hav z hzp).1 (mem_sdiff.mp (hrR z hzr hzu hza)).1
  have hrb : b ∉ r.support := by
    intro h
    exact hab (hrP b h p.end_mem_support).symm
  have hcard : r.support.toFinset.card ≤ L + 1 := by
    have h := List.toFinset_card_le r.support
    rw [r.length_support] at h
    omega
  obtain ⟨s, hs, hslen, hsR⟩ := hres v b r.support.toFinset hcard
  have hrs (z : V) (hzr : z ∈ r.support) (hzs : z ∈ s.support) : False := by
    have hzv : z ≠ v := fun h => hrv (h ▸ hzr)
    have hzb : z ≠ b := fun h => hrb (h ▸ hzr)
    exact (mem_sdiff.mp (hsR z hzs hzv hzb)).2 (List.mem_toFinset.mpr hzr)
  have hsP (z : V) (hzp : z ∈ p.support) (hzs : z ∈ s.support) : z = b := by
    by_contra hzb
    have hzv := (hav z hzp).2.2
    exact (hav z hzp).1 (mem_sdiff.mp (hsR z hzs hzv hzb)).1
  have hrp : (r.append p).IsPath := isPath_append_of_support_inter r p hr hp hrP
  have hq : ((r.append p).append s.reverse).IsPath := by
    apply isPath_append_of_support_inter (r.append p) s.reverse hrp hs.reverse
    intro z hz hzsr
    have hzs : z ∈ s.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hzsr
    rcases (Walk.mem_support_append_iff _ _).mp hz with hzr | hzp
    · exact (hrs z hzr hzs).elim
    · exact hsP z hzp hzs
  refine ⟨(r.append p).append s.reverse, hq, ?_, ?_⟩ <;>
    simp only [Walk.length_append, Walk.length_reverse] <;> omega

#print axioms exists_path_with_prescribed_ends_of_reservoir

end Erdos556
