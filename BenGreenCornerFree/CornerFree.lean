import Mathlib.Tactic

open Nat hiding log

open Finset Real

open scoped BigOperators

namespace BenGreen

variable {α : Type*} [DecidableEq α] [CommGroup α] {s t : Finset α}

/-
Main reference: https://arxiv.org/pdf/2102.11702.pdf
-/

@[to_additive "poggers"]
def MulCornerFree (s : Set (α × α)) : Prop :=
  ∀ x y d, (x, y) ∈ s → (x * d, y) ∈ s → (x, y * d) ∈ s → d = 1

-- This is not computable, but is decidable
@[to_additive "poggie"]
def MulCornerFree' (s : Set (α × α)) : Prop :=
  ∀ x y x' y' d, (x, y) ∈ s → (x', y) ∈ s → (x, y') ∈ s → x' = x * d → y' = y * d → d = 1

@[to_additive "poggies"]
theorem MulCornerFree_iff_MulCornerFree' (s : Set (α × α)) :
  MulCornerFree s ↔ MulCornerFree' s :=
by
  dsimp [MulCornerFree, MulCornerFree']
  exact ⟨fun h x y x' y' d h₁ h₂ h₃ hx hy ↦ h x y d h₁ (hx ▸ h₂) (hy ▸ h₃),
    fun h x y d h₁ h₂ h₃ ↦ h x y (x * d) (y * d) d h₁ h₂ h₃ rfl rfl⟩

@[to_additive]
instance (s : Finset (α × α)) [DecidableEq α] :
  Decidable (MulCornerFree' (s : Set (α × α))) :=
by
  simp only [MulCornerFree', mem_coe]
  refine @decidable_of_iff _ (
    ∀ (d : α) (xy xy' x'y : s),
      xy.val.1 = xy'.val.1
    → xy.val.2 = x'y.val.2
    → x'y.val.1 = xy.val.1 * d
    → xy'.val.2 = xy.val.2 * d
    → d = 1
  ) ?_ ?_
  · -- Prove MulCornerFree' and the new Prop are equivalent
    constructor
    · intro h x y x' y' d hxy hx'y hxy' hx hy
      specialize h d ⟨(x, y), hxy⟩ ⟨(x, y'), hxy'⟩ ⟨(x', y), hx'y⟩
      simp only [hx, hy, h]
    · intro h d xy xy' x'y hx₁ hy₁ hx₂ hy₂
      specialize h xy.val.1 xy.val.2 x'y.val.1 xy'.val.2 d xy.prop
      rw [hy₁, hx₁] at h
      specialize h x'y.prop xy'.prop
      simp only [h, ←hx₁, ←hy₁, hx₂, hy₂]

  -- Prove the new Prop is decidable
  refine @decidable_of_iff _ (
    ∀ xy xy' x'y : s,
      xy.val.1 = xy'.val.1
    → xy.val.2 = x'y.val.2
    → x'y.val.1 * xy.val.2 = xy.val.1 * xy'.val.2
    → xy.val.1 = x'y.val.1
  ) ?_ ?_
  · -- Prove the new Prop is equivalent to the new new Prop
    constructor
    · intro h d xy xy' x'y hx₁ hy₁ hx₂ hy₂
      specialize h xy xy' x'y hx₁ hy₁
      simp_rw [hx₂, hy₂, mul_comm xy.val.2, ←mul_assoc, forall_true_left, self_eq_mul_right] at h
      exact h
    · intro h xy xy' x'y hx hy hd
      specialize h (x'y.val.1 / xy.val.1) xy xy' x'y hx hy
      simp_rw [mul_div, mul_comm, hd, mul_comm xy.val.1, mul_div_cancel''] at h
      simp only [forall_true_left] at h
      exact (div_eq_one.mp h).symm
  · -- Prove the new new Prop is decidable
    infer_instance

@[to_additive]
instance (s : Finset (α × α)) [DecidableEq α] : Decidable (MulCornerFree (s : Set (α × α))) :=
  decidable_of_iff
    (MulCornerFree' (s : Set (α × α)))
    (MulCornerFree_iff_MulCornerFree' (s : Set (α × α))).symm

@[to_additive "also poggers"]
noncomputable def mulCornerFreeNumber (s : Finset (α × α)) : ℕ :=
  Nat.findGreatest (fun m => ∃ (t : _) (_ : t ⊆ s), t.card = m ∧ MulCornerFree (t : Set (α × α))) s.card

end BenGreen

section asdf

variable {α : Type*}

def MyProp (s : Finset α) : Prop := ∀ a : α, a ∈ s

end asdf

