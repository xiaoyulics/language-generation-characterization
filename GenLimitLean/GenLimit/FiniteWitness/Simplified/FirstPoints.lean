import GenLimit.FiniteWitness.Normalization
import Mathlib.Data.Nat.Nth

/-! First-k checkpoints, exactly as in the simplified manuscript. -/

namespace GenLimit.FiniteWitness.Simplified

noncomputable section
open scoped Classical

noncomputable def firstPoints (L : Set ℕ) (k : ℕ) : Finset ℕ := by
  classical
  exact ((Finset.range k).image (Nat.nth L)).filter
    (fun x => x ∈ L ∧ Nat.count L x < k)

@[simp] theorem mem_firstPoints (L : Set ℕ) (k x : ℕ) :
    x ∈ firstPoints L k ↔ x ∈ L ∧ Nat.count L x < k := by
  classical
  rw [firstPoints, Finset.mem_filter]
  constructor
  · exact And.right
  · intro h
    refine ⟨Finset.mem_image.mpr ⟨Nat.count L x, ?_, ?_⟩, h⟩
    · exact Finset.mem_range.mpr h.2
    · exact Nat.nth_count h.1

theorem firstPoints_subset (L : Set ℕ) (k : ℕ) :
    (↑(firstPoints L k) : Set ℕ) ⊆ L := fun x hx => ((mem_firstPoints L k x).mp hx).1

theorem firstPoints_mono (L : Set ℕ) {j k : ℕ} (hjk : j ≤ k) :
    firstPoints L j ⊆ firstPoints L k := by
  intro x hx
  rw [mem_firstPoints] at hx ⊢
  exact ⟨hx.1, hx.2.trans_le hjk⟩

theorem firstPoints_card {L : Set ℕ} (hL : L.Infinite) (k : ℕ) :
    (firstPoints L k).card = k := by
  classical
  have he : firstPoints L k = (Finset.range k).image (Nat.nth L) := by
    apply Finset.filter_eq_self.mpr
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨Nat.nth_mem_of_infinite hL j, by
      rw [Nat.count_nth_of_infinite hL]
      exact Finset.mem_range.mp hj⟩
  rw [he, Finset.card_image_of_injective _ (Nat.nth_injective hL), Finset.card_range]

theorem firstPoints_exhausts (L : Set ℕ) {x : ℕ} (hx : x ∈ L) :
    ∃ k, x ∈ firstPoints L (k + 1) := by
  classical
  exact ⟨Nat.count L x, (mem_firstPoints _ _ _).mpr ⟨hx, Nat.lt_succ_self _⟩⟩

theorem firstPoints_agree {L : Set ℕ} (hL : L.Infinite) {S : Finset ℕ} {j k : ℕ}
    (hSL : (↑S : Set ℕ) ⊆ L) (hseen : firstPoints L k ⊆ S) (hjk : j ≤ k) :
    firstPoints (↑S : Set ℕ) j = firstPoints L j := by
  classical
  ext x
  simp only [mem_firstPoints, Finset.mem_coe]
  constructor
  · rintro ⟨hxS, hcount⟩
    refine ⟨hSL hxS, ?_⟩
    by_contra hn
    have hsub : firstPoints L j ⊆ (Finset.range x).filter (fun y => (↑S : Set ℕ) y) := by
      intro y hy
      have hym := (mem_firstPoints _ _ _).mp hy
      have hyx : y < x := by
        by_contra hny
        have hm := Nat.count_monotone L (Nat.le_of_not_lt hny)
        omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hyx,
        hseen (firstPoints_mono L hjk hy)⟩
    have hc := Finset.card_le_card hsub
    rw [firstPoints_card hL, ← Nat.count_eq_card_filter_range] at hc
    omega
  · rintro ⟨hxL, hcount⟩
    refine ⟨hseen (firstPoints_mono L hjk ((mem_firstPoints _ _ _).mpr ⟨hxL, hcount⟩)), ?_⟩
    exact (Nat.count_mono_left (p := (↑S : Set ℕ)) (q := L) (fun y hy => hSL hy)).trans_lt hcount

end
end GenLimit.FiniteWitness.Simplified
