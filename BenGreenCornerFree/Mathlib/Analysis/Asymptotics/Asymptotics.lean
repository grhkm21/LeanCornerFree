import Mathlib.Analysis.Asymptotics.Asymptotics

open Asymptotics Filter

namespace Asymptotics

variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {E''' : Type*}
  {R : Type*} {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variable [Norm E] [Norm F] [Norm G]
variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedAddGroup E''']
  [SeminormedRing R']

variable [NormedDivisionRing 𝕜] [NormedDivisionRing 𝕜']
variable {c c' c₁ c₂ : ℝ} {f : α → E} {g : α → F} {k : α → G}
variable {f' : α → E'} {g' : α → F'} {k' : α → G'}
variable {f'' : α → E''} {g'' : α → F''} {k'' : α → G''}
variable {l l' : Filter α}

#check isBigO_iff
theorem IsBigO.neg (h : f' =O[l] g) : (-f') =O[l] g := by
  rw [isBigO_iff] at h ⊢
  simp_rw [Pi.neg_apply, norm_neg, h]

theorem isBigO_neg_iff : (-f') =O[l] g ↔ f' =O[l] g :=
  ⟨fun h ↦ neg_neg f' ▸ h.neg, fun h ↦ h.neg⟩
