
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.ModEq

open Nat

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

-- end exp_test

-- open Nat (add_assoc add_comm)

-- theorem hello_world (a b c : Nat)
--   : a + b + c = a + c + b := by
--   rw [add_assoc, add_comm b, ←add_assoc]

-- theorem foo (a : Nat) : a + 1 = Nat.succ a := by rfl
