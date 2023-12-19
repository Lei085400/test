
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
