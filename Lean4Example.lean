import Mathlib.Data.Nat.Choose.Sum

#align_import data.nat.choose.sum from "leanprover-community/mathlib"@"4c19a16e4b705bf135cf9a80ac18fcc99c438514"

open Nat

--原始定理
theorem idt1_Pascal's_Recurrence(h1:1 ≤ n)(h2:1 ≤ k) : choose n k = choose (n-1) k  + choose (n-1) (k-1) := by
  have choose_eq_choose_sub_add :  choose n k = choose (n - 1 + 1) (k - 1 + 1)  := by
    rw[Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
  rw[choose_eq_choose_sub_add]
  rw[add_comm (choose (n - 1) k) (choose (n - 1) (k - 1))]
  have choose_sub_eq_choose_sub_add : choose (n - 1) k = choose (n - 1) (k - 1 + 1) := by rw[Nat.sub_add_cancel h2]
  rw[choose_sub_eq_choose_sub_add, choose_succ_succ]



/-基于预测的后向数据增强:
摘取其中任意第n步到第n+m步策略
采用强化学习或LLM进行下一步/若干步策略预测得到新的目标G_{p}，其作为新的待证明定理T_{p}
反向应用所有策略
第n-1步的目标G_{n-1}写成新的假设h_{g}
重写h_{g}作为新定理证明的最后一步。-/

--例如，从第一步开始，在rw[add_comm (choose (n - 1) k) (choose (n - 1) (k - 1))]后断开，并往后预测一步得到新的目标，将其作为新的待证明定理
--候选策略： rw [mul_comm] ; rw [add_comm] ; rw [mul_assoc] ; rw [add_assoc] ; rw [pow_add]...
--依次使用候选策略，成功应用的话就会生成新的目标，报错就丢弃



--例如此处rw [mul_comm]应用失败，rw [add_comm]应用成功
-- theorem DA_idt1_Pascal's_Recurrence(h1:1 ≤ n)(h2:1 ≤ k) : choose n k = choose (n-1) k  + choose (n-1) (k-1) := by
--   have choose_eq_choose_sub_add :  choose n k = choose (n - 1 + 1) (k - 1 + 1)  := by
--     rw[Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
--   rw [choose_eq_choose_sub_add]
--   rw [add_comm (choose (n - 1) k) (choose (n - 1) (k - 1))]
--   rw [add_comm] --此处新的目标为choose (1 + (n - 1)) (k - 1 + 1) = choose (n - 1) (k - 1) + choose (n - 1) k



-- rw [add_comm]对应生成的新定理
-- theorem BDA2 (h1:1 ≤ n)(h2:1 ≤ k) (h0:choose n k = choose (n-1) k  + choose (n-1) (k-1)):
--  choose (1 + (n - 1)) (k - 1 + 1) = choose (n - 1) (k - 1) + choose (n - 1) k := by
--    have choose_eq_choose_sub_add :  choose n k = choose (n - 1 + 1) (k - 1 + 1)  := by
--     rw[Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
--    rw [← add_comm]
--    rw [← add_comm (choose (n - 1) k) (choose (n - 1) (k - 1))]
--    rw [← choose_eq_choose_sub_add]
--    rw [h0]
