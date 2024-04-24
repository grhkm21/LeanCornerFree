import Mathlib.Tactic

open Int Finset BigOperators Filter

def T (q a b : ℤ) : Finset (Ico 0 q × Ico 0 q) :=
  univ.filter fun v ↦ v.fst.val + v.snd.val ∈ Ico a b

theorem mem_T {q a b : ℤ} {v} : v ∈ T q a b ↔ v.fst.val + v.snd.val ∈ Ico a b := by
  simp [T, mem_filter]

theorem Int.le_of_lt_succ {x a : Int} (h : x < a.succ) : x ≤ a := Int.le_of_add_le_add_right h

theorem Int.mem_Ico_succ {a x : ℤ} : x ∈ Ico a a.succ ↔ a = x := by
  rw [mem_Ico]
  constructor <;> intro h
  · exact Int.eq_iff_le_and_ge.mpr ⟨h.left, Int.le_of_lt_succ h.right⟩
  · simpa [h] using lt_succ_self _

/- set_option maxHeartbeats 0 in -/
/- example {q a b : ℤ} : -/
/-     (T q a b).card = ∑ i in Ico a b, (T q i i.succ).card := by -/
/-   repeat simp_rw [← Fintype.card_coe] -/
/-   rw [← sum_coe_sort, ← Fintype.card_sigma] -/
/-   apply Fintype.card_congr -/
/-   exact { -/
/-     toFun := by -/
/-       intro ⟨⟨x, y⟩, h⟩ -/
/-       use ⟨x.val + y.val, mem_T.mp h⟩, ⟨x, y⟩, mem_T.mpr (by rw [Int.mem_Ico_succ]) -/
/-     invFun := by -/
/-       intro ⟨i, ⟨⟨x, y⟩, h⟩⟩ -/
/-       use ⟨x, y⟩ -/
/-       rw [mem_T] at h ⊢ -/
/-       obtain ⟨hi₁, hi₂⟩ := mem_Ico.mp i.prop -/
/-       apply mem_of_subset ((Ico_subset_Ico_iff (lt_succ _)).mpr ⟨hi₁, ?_⟩) h -/
/-       rwa [← lt_iff_add_one_le] -/
/-     left_inv := by intro; simp -/
/-     right_inv := by -/
/-       intro ⟨i, ⟨⟨x, y⟩, h⟩⟩ -/
/-       simp -/
/-       constructor -/
/-       · sorry -/
/-       · congr 1 -/
/-         · done -/
/-         /- · done -/ -/
/-         · apply proof_irrel_heq -/
/-   } -/

#check Tendsto

