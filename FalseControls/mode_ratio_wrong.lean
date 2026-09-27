import Suns.Basic
-- The mode ratio 2π/0.45 exceeds 13.96; it is not below 13.9.
example : 2 * Real.pi / 0.45 < 13.9 := by
  have := Real.pi_gt_d4
  rw [div_lt_iff₀ (by norm_num)]; linarith
