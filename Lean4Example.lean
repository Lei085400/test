
-- import Theorem.Premises.real_theorem.mini_theorem

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.LocallyFinite
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Parity
#align_import data.nat.choose.sum from "leanprover-community/mathlib"@"4c19a16e4b705bf135cf9a80ac18fcc99c438514"


open Nat

open Finset

open BigOperators

variable {R : Type*}

-- namespace Commute

variable [Semiring R] {x y : R}

variable {α : Type u} {β : Type v} {γ : Type w} {s₂ s₁ s : Finset α} {a : α} {g f : α → β}

variable [CommMonoid β]

-- namespace exp_test

--定理1.2
theorem test12(h1:1 ≤ n)(h2:1 ≤ k) : choose n k = choose (n-1) k  + choose (n-1) (k-1) := by
  have hneg :  choose n k = choose (n - 1 + 1) (k - 1 + 1)  := by
   rw[Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
  rw[hneg]
  rw[add_comm (choose (n - 1) k) (choose (n - 1) (k - 1))]
  have hk : choose (n - 1) k = choose (n - 1) (k - 1 + 1) := by
   rw[Nat.sub_add_cancel h2]
  rw[hk, choose_succ_succ]

open Classical
variable (p : α → Prop)

theorem two_have (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  byContradiction
    (fun h1 : ¬ ∃ x, p x =>
      have h2 : ∀ x, ¬ p x :=
        fun x =>
        fun h3 : p x =>
        have h4 : ∃ x, p x :=  ⟨x, h3⟩
        show False from h1 h4
      show False from h h2)
