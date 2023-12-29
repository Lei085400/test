
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
-- import Mathlib.Data.Real.Basic
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

theorem sum_choose_eq_Ico (hn: n ≤ 2 * n): ∑ k in range n, choose (2 * n) k = ∑ k in Ico (n + 1) (2 * n + 1), (choose (2 * n) k) := by
  rw [range_eq_Ico]
  have h1 : ∑ k in Ico 0 n, Nat.choose (2 * n) k = ∑ k in Ico 0 n, Nat.choose (2 * n) (2 * n - k) := by
    refine' sum_congr rfl fun y hy ↦ _
    have yn : y < n := by exact (mem_Ico.1 hy).2
    have y2n : y ≤ 2 * n := by linarith
    rw[← choose_symm y2n]
  rw[h1]
  rw[sum_Ico_reflect]
  simp
  have two_mul_succ_sub : 2 * n + 1 - n = n + 1 := by
    have two_mul_add_sub : 2 * n + 1 - n = 2 * n - n + 1  := by
      rw[add_comm]
      rw[Nat.add_sub_assoc hn]
      rw[add_comm]
    rw[two_mul_add_sub]
    simp
    have h23: 2 * n - n = 2 * n - 1 * n := by simp
    rw[h23]
    rw[← Nat.mul_sub_right_distrib]
    simp
  rw[two_mul_succ_sub]
  linarith
