import ErdosProblems.Erdos4.TiltedBlocks

/-! Root companions in different prime fibers are disjoint and avoid the root residue. -/

open scoped BigOperators

namespace Erdos4.Tilted

open RandomResidueSieve

noncomputable def rootCompanions {C : Finset ℕ} (P : Finpartition C) (v : ℕ) : Finset ℕ :=
  (P.part v).erase v

theorem rootCompanions_subset {C : Finset ℕ} (P : Finpartition C) (v : ℕ) :
    rootCompanions P v ⊆ C := (Finset.erase_subset _ _).trans (P.part_subset v)

theorem rootCompanions_ne_root {C : Finset ℕ} (P : Finpartition C) {v n : ℕ}
    (hn : n ∈ rootCompanions P v) : n ≠ v := (Finset.mem_erase.mp hn).1

theorem insert_rootCompanions {C : Finset ℕ} (P : Finpartition C) {v : ℕ} (hv : v ∈ C) :
    insert v (rootCompanions P v) = P.part v := Finset.insert_erase (P.mem_part hv)

theorem rootCompanions_card_le {C : Finset ℕ} (P : Finpartition C) {v K : ℕ} (hv : v ∈ C)
    (hcard : ∀ E ∈ P.parts, E.card ≤ K) : (rootCompanions P v).card ≤ K :=
  (Finset.card_erase_le).trans (hcard _ (P.part_mem.mpr hv))

theorem rootCompanions_squarefree {C : Finset ℕ} (P : Finpartition C) {v : ℕ} (hv : v ∈ C)
    (hsq : ∀ E ∈ P.parts, Squarefree (∏ n ∈ E, n)) :
    Squarefree (∏ n ∈ rootCompanions P v, n) := by
  apply (hsq _ (P.part_mem.mpr hv)).squarefree_of_dvd
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.erase_subset v (P.part v))

theorem rootCompanions_fiber {C : Finset ℕ} (P : Finpartition C) {v p : ℕ} (hv : v ∈ C)
    (hfiber : ∀ E ∈ P.parts, ∀ n ∈ E, ∀ m ∈ E, (n : ZMod p) = (m : ZMod p)) :
    ∀ n ∈ rootCompanions P v, (n : ZMod p) = (v : ZMod p) := by
  intro n hn
  exact hfiber _ (P.part_mem.mpr hv) n (Finset.mem_of_mem_erase hn) v (P.mem_part hv)

theorem rootCompanions_avoid_root {C : Finset ℕ} (P : Finpartition C) {v p s Y : ℕ}
    (hv : v ∈ C) (hp : p.Prime) (hs : s.Prime) (hps : p ≠ s) (hwidth : Y < p * s)
    (hbound : ∀ n ∈ C, n ≤ Y)
    (hfiber : ∀ E ∈ P.parts, ∀ n ∈ E, ∀ m ∈ E, (n : ZMod p) = (m : ZMod p)) :
    (v : ZMod s) ∉ (rootCompanions P v).image (fun n : ℕ => (n : ZMod s)) := by
  intro hvimage
  obtain ⟨n, hn, hnv⟩ := Finset.mem_image.mp hvimage
  have heq : n = v := fiber_residue_injective hp hs hps hwidth
    (fun n hn => hbound n (P.part_subset v hn))
    (hfiber _ (P.part_mem.mpr hv)) (Finset.mem_of_mem_erase hn) (P.mem_part hv) hnv
  exact rootCompanions_ne_root P hn heq

theorem rootCompanions_disjoint {C : Finset ℕ} (P Q : Finpartition C) {v p q Y : ℕ}
    (hv : v ∈ C) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hwidth : Y < p * q)
    (hbound : ∀ n ∈ C, n ≤ Y)
    (hfiberP : ∀ E ∈ P.parts, ∀ n ∈ E, ∀ m ∈ E, (n : ZMod p) = (m : ZMod p))
    (hfiberQ : ∀ E ∈ Q.parts, ∀ n ∈ E, ∀ m ∈ E, (n : ZMod q) = (m : ZMod q)) :
    Disjoint (rootCompanions P v) (rootCompanions Q v) := by
  apply Finset.disjoint_left.mpr
  intro n hnP hnQ
  have heq : n = v := eq_of_two_residues ((Nat.coprime_primes hp hq).mpr hpq)
    ((hbound n (rootCompanions_subset P v hnP)).trans_lt hwidth) ((hbound v hv).trans_lt hwidth)
    (rootCompanions_fiber P hv hfiberP n hnP) (rootCompanions_fiber Q hv hfiberQ n hnQ)
  exact rootCompanions_ne_root P hnP heq

end Erdos4.Tilted
