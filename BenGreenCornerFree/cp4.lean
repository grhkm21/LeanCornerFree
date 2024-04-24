import Mathlib.Tactic

open Int Set BigOperators Filter

def map_Mathlib {α β : Type*} (f : α → β) (F : Filter α) : Filter β where
  sets := (Set.preimage f) ⁻¹' F.sets
  univ_sets := univ_mem
  sets_of_superset hs st := sorry
  inter_sets hs ht := sorry

def map_paper {α β : Type*} (f : α → β) (F : Filter α) : Filter β where
  sets := (Set.preimage f) ⁻¹' F.sets
  univ_sets := univ_mem
  sets_of_superset hs st := sorry
  inter_sets hs ht := sorry

variable {α β : Type*} (f : α → β) (F : Filter α)

lemma Mathlib_paper : ∀ S : Set β,
    S ∈ (Set.preimage f) ⁻¹' F.sets ↔ f ⁻¹' S ∈ F.sets := by
  simp

lemma Mathlib_mine : ∀ S : Set β,
    S ∈ F.map f ↔ S ∈ (generate ((f '' ·) '' F.sets)).sets := by
  intro S
  simp only [mem_map, Filter.mem_sets]
  constructor <;> intro h
  · done
  · done
