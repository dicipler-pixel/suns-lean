import Suns.Basic
-- One loop exchanges the pair, it does not restore it: e^{iπ} = −1, not 1.
example : Complex.exp (Real.pi * Complex.I) = 1 := by
  rw [Complex.exp_pi_mul_I]; norm_num
