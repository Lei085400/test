import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Group.Defs

open Nat

theorem test12_from_0_to_0(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(gol:  choose n k = choose (n - 1) k + choose (n - 1) (k - 1)) :
   choose n k = choose (n - 1) k + choose (n - 1) (k - 1) := by
   have hneg :  choose n k = choose (n - 1 + 1) (k - 1 + 1)  := by
      rw[Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
   rw[gol]
--   sorry

theorem test12_from_0_to_1(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(gol:  choose (n - 1 + 1) (k - 1 + 1) = choose (n - 1) k + choose (n - 1) (k - 1)) :
   choose n k = choose (n - 1) k + choose (n - 1) (k - 1) := by
  have hneg :  choose n k = choose (n - 1 + 1) (k - 1 + 1)  := by
   rw[Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
  rw[hneg]
  rw[gol]

theorem test12_from_0_to_2(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(gol:  choose (n - 1 + 1) (k - 1 + 1) = choose (n - 1) (k - 1) + choose (n - 1) k) :
   choose n k = choose (n - 1) k + choose (n - 1) (k - 1) := by
  have hneg :  choose n k = choose (n - 1 + 1) (k - 1 + 1)  := by
   rw[Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
  rw[hneg]
  rw[add_comm (choose (n - 1) k) (choose (n - 1) (k - 1))]
  rw[gol]

theorem test12_from_0_to_3(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(gol:  choose (n - 1 + 1) (k - 1 + 1) = choose (n - 1) (k - 1) + choose (n - 1) k) :
   choose n k = choose (n - 1) k + choose (n - 1) (k - 1) := by
  have hneg :  choose n k = choose (n - 1 + 1) (k - 1 + 1)  := by
   rw[Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
  rw[hneg]
  rw[add_comm (choose (n - 1) k) (choose (n - 1) (k - 1))]
  have hk : choose (n - 1) k = choose (n - 1) (k - 1 + 1) := by
   rw[Nat.sub_add_cancel h2]
  rw[gol]

theorem test12_from_0_to_4(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k) :
   choose n k = choose (n - 1) k + choose (n - 1) (k - 1) := by
  have hneg :  choose n k = choose (n - 1 + 1) (k - 1 + 1)  := by
   rw[Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
  rw[hneg]
  rw[add_comm (choose (n - 1) k) (choose (n - 1) (k - 1))]
  have hk : choose (n - 1) k = choose (n - 1) (k - 1 + 1) := by
   rw[Nat.sub_add_cancel h2]
  rw[hk, choose_succ_succ]

theorem test12_from_1_to_1(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(hneg : choose n k = choose (n - 1 + 1) (k - 1 + 1))(gol:  choose (n - 1 + 1) (k - 1 + 1) = choose (n - 1) k + choose (n - 1) (k - 1)) :
   choose n k = choose (n - 1) k + choose (n - 1) (k - 1) := by
  rw[hneg]
  rw[gol]

theorem test12_from_1_to_2(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(hneg : choose n k = choose (n - 1 + 1) (k - 1 + 1))(gol:  choose (n - 1 + 1) (k - 1 + 1) = choose (n - 1) (k - 1) + choose (n - 1) k) :
   choose n k = choose (n - 1) k + choose (n - 1) (k - 1) := by
  rw[hneg]
  rw[add_comm (choose (n - 1) k) (choose (n - 1) (k - 1))]
  rw[gol]

theorem test12_from_1_to_3(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(hneg : choose n k = choose (n - 1 + 1) (k - 1 + 1))(gol:  choose (n - 1 + 1) (k - 1 + 1) = choose (n - 1) (k - 1) + choose (n - 1) k) :
   choose n k = choose (n - 1) k + choose (n - 1) (k - 1) := by
  rw[hneg]
  rw[add_comm (choose (n - 1) k) (choose (n - 1) (k - 1))]
  have hk : choose (n - 1) k = choose (n - 1) (k - 1 + 1) := by
   rw[Nat.sub_add_cancel h2]
  rw[gol]

theorem test12_from_1_to_4(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(hneg : choose n k = choose (n - 1 + 1) (k - 1 + 1)) :
   choose n k = choose (n - 1) k + choose (n - 1) (k - 1) := by
  rw[hneg]
  rw[add_comm (choose (n - 1) k) (choose (n - 1) (k - 1))]
  have hk : choose (n - 1) k = choose (n - 1) (k - 1 + 1) := by
   rw[Nat.sub_add_cancel h2]
  rw[hk, choose_succ_succ]

theorem test12_from_2_to_2(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(hneg : choose n k = choose (n - 1 + 1) (k - 1 + 1))(gol:  choose (n - 1 + 1) (k - 1 + 1) = choose (n - 1) (k - 1) + choose (n - 1) k) :
   choose (n - 1 + 1) (k - 1 + 1) = choose (n - 1) k + choose (n - 1) (k - 1) := by
  rw[add_comm (choose (n - 1) k) (choose (n - 1) (k - 1))]
  rw[gol]

theorem test12_from_2_to_3(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(hneg : choose n k = choose (n - 1 + 1) (k - 1 + 1))(gol:  choose (n - 1 + 1) (k - 1 + 1) = choose (n - 1) (k - 1) + choose (n - 1) k) :
   choose (n - 1 + 1) (k - 1 + 1) = choose (n - 1) k + choose (n - 1) (k - 1) := by
  rw[add_comm (choose (n - 1) k) (choose (n - 1) (k - 1))]
  have hk : choose (n - 1) k = choose (n - 1) (k - 1 + 1) := by
   rw[Nat.sub_add_cancel h2]
  rw[gol]

theorem test12_from_2_to_4(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(hneg : choose n k = choose (n - 1 + 1) (k - 1 + 1)) :
   choose (n - 1 + 1) (k - 1 + 1) = choose (n - 1) k + choose (n - 1) (k - 1) := by
  rw[add_comm (choose (n - 1) k) (choose (n - 1) (k - 1))]
  have hk : choose (n - 1) k = choose (n - 1) (k - 1 + 1) := by
   rw[Nat.sub_add_cancel h2]
  rw[hk, choose_succ_succ]

theorem test12_from_3_to_3(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(hneg : choose n k = choose (n - 1 + 1) (k - 1 + 1))(gol:  choose (n - 1 + 1) (k - 1 + 1) = choose (n - 1) (k - 1) + choose (n - 1) k) :
   choose (n - 1 + 1) (k - 1 + 1) = choose (n - 1) (k - 1) + choose (n - 1) k := by
  have hk : choose (n - 1) k = choose (n - 1) (k - 1 + 1) := by
   rw[Nat.sub_add_cancel h2]
  rw[gol]

theorem test12_from_3_to_4(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(hneg : choose n k = choose (n - 1 + 1) (k - 1 + 1)) :
   choose (n - 1 + 1) (k - 1 + 1) = choose (n - 1) (k - 1) + choose (n - 1) k := by
  have hk : choose (n - 1) k = choose (n - 1) (k - 1 + 1) := by
   rw[Nat.sub_add_cancel h2]
  rw[hk, choose_succ_succ]

theorem test12_from_4_to_4(n k : ℕ)(h1 : 1 ≤ n)(h2 : 1 ≤ k)(hneg : choose n k = choose (n - 1 + 1) (k - 1 + 1))(hk : choose (n - 1) k = choose (n - 1) (k - 1 + 1)) :
   choose (n - 1 + 1) (k - 1 + 1) = choose (n - 1) (k - 1) + choose (n - 1) k := by
  rw[hk, choose_succ_succ]
