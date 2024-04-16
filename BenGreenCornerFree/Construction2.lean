import Mathlib.Tactic
import Mathlib.Data.List.ToFinsupp

set_option autoImplicit false

namespace BenGreen

/- --------------------------------------------------------------------------- -/
/- Deprecated because we use new construction now (work with vectors directly) -/
/- --------------------------------------------------------------------------- -/

-- Before anything, let us check out the space ℤ_q^d
#check Module
#check Basis.ofVectorSpace
#check Nat.digits

-- We first define the π map in the paper
abbrev V (d : ℕ) := Fin d → ℤ
abbrev S (q d : ℕ) := Fin (q ^ d)
abbrev P (q d : ℕ) := S q d × S q d

def π (q d : ℕ) : S q d → V d := fun n ↦ (fun k ↦ (q.digits n).getD k 0)

theorem π_inj (q d : ℕ) [hq : Fact (1 < q)] : Function.Injective (π q d) := by
  intro n m h
  ext
  apply (Nat.digits_inj_iff (b := q)).mp
  ext i d'
  simp only [Option.mem_def]

  by_cases hi : i < d
  · replace h := congrFun h
    sorry
  · have : ∀ n < q ^ d, List.get? (q.digits n) i = none := by
      intro n hn
      by_cases hn : n = 0
      · simp only [hn, Fin.val_zero', Nat.digits_zero, List.get?_nil]
      · rw [List.get?_eq_none, Nat.digits_len _ _ hq.out ?_]
        · sorry
        · exact hn
    rw [this n n.prop, this m m.prop]

-- We also define a Prop expressing that
--   (x, y) ∈ [q^d - 1]²
--   ‖π(x) - π(y)‖₂² = r
--   q / 2 ≤ xᵢ + yᵢ < 3q / 2
def IsInCons {q d : ℕ} (P : S q d) : Prop :=
    ‖P.fst - P.snd‖

-- We first prove that (x + d)ᵢ + yᵢ = xᵢ + (y + d)ᵢ

-- This implies (0.2): π(x + d) = π(y) = π(x) + π(y + d)

-- We then invoke the parallelogram law

example : True := trivial
