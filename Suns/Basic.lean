/-
Transient Structure at Solar Rigidity Interfaces and the Exceptional Point of the Dynamo Wave
(Jeromie Beasley, DOI 10.5281/zenodo.21895551, v1.5): the exact mathematics under the graded
computations.

The paper's results are computations (grade [V]). What Lean can certify is the exact structure
those computations measure:
* the exceptional-point normal form `J(δ) = [[0, 1], [δ, 0]]`: eigenvalues `±√δ`, right and
  left eigenvectors, the eigenvalue condition number `κ = (1 + δ)/(2√δ)`, and the square-root law
  `κ√δ → const` with `κ → ∞` at the collision;
* the integer record: the branch `√r e^{iθ/2}` of the colliding pair is exchanged after one loop
  and restored after two, while the trace-log ledger `log det` does not depend on the branch;
* the hair-rate ladder in one operator: `A = [[−ε, γ], [0, −ε]]` has modal rate `−ε` but
  numerical abscissa `−ε + |γ|/2`, so energy grows initially whenever `|γ| > 2ε`;
* the mode ratio `λ/d = 2π/(k_max d) = 2π/0.450 ∈ (13.96, 13.97)`, and at the observed 65 km
  wavelength the lane widths `2d` and `4d` lie between 9 and 19 km.
-/
import Mathlib

namespace Suns

open Real Filter Topology Matrix

/-! ## The exceptional point: normal form and the square-root law -/

/-- The exceptional-point normal form. -/
def J (δ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; δ, 0]

/-- Right eigenvector for `±√δ`. -/
theorem J_right_eigen (δ : ℝ) (hδ : 0 ≤ δ) (s : ℝ) (hs : s = √δ ∨ s = -√δ) :
    J δ *ᵥ ![1, s] = s • ![1, s] := by
  have hss : s * s = δ := by
    rcases hs with rfl | rfl <;> simp [Real.mul_self_sqrt hδ]
  ext i
  fin_cases i <;> simp [J, mulVec, dotProduct, Fin.sum_univ_two, hss]

/-- Left eigenvector for `±√δ`. -/
theorem J_left_eigen (δ : ℝ) (hδ : 0 ≤ δ) (s : ℝ) (hs : s = √δ ∨ s = -√δ) :
    (J δ)ᵀ *ᵥ ![s, 1] = s • ![s, 1] := by
  have hss : s * s = δ := by
    rcases hs with rfl | rfl <;> simp [Real.mul_self_sqrt hδ]
  ext i
  fin_cases i <;> simp [J, mulVec, dotProduct, Fin.sum_univ_two, hss]

/-- The eigenvalue condition number `‖ℓ‖‖r‖/|ℓ·r|` of `J(δ)` at `√δ`. -/
noncomputable def kappa (δ : ℝ) : ℝ := √(1 + δ) * √(1 + δ) / (2 * √δ)

/-- **Closed form.** `κ(δ) = (1 + δ)/(2√δ)`, since `ℓ = (√δ, 1)`, `r = (1, √δ)`,
`‖ℓ‖ = ‖r‖ = √(1+δ)` and `ℓ·r = 2√δ`. -/
theorem kappa_eq (δ : ℝ) (hδ : 0 ≤ δ) : kappa δ = (1 + δ) / (2 * √δ) := by
  rw [kappa, Real.mul_self_sqrt (by linarith)]

/-- **The square-root law.** `κ√δ → 1/2` as `δ → 0⁺`. -/
theorem sqrt_law : Tendsto (fun δ => kappa δ * √δ) (𝓝[>] 0) (𝓝 (1 / 2)) := by
  have h : Tendsto (fun δ : ℝ => (1 + δ) / 2) (𝓝[>] 0) (𝓝 ((1 + 0) / 2)) :=
    (((continuous_const.add continuous_id).div_const 2).tendsto 0).mono_left nhdsWithin_le_nhds
  norm_num at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hs : 0 < √δ := Real.sqrt_pos.mpr hδ
  rw [kappa_eq δ hδ.le]
  field_simp

/-- **Defectivity at the collision.** `κ → ∞` as `δ → 0⁺`: the eigenvectors coalesce. -/
theorem kappa_diverges : Tendsto kappa (𝓝[>] 0) atTop := by
  have hs : Tendsto (fun δ : ℝ => √δ) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := (Real.continuous_sqrt.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact Real.sqrt_pos.mpr hδ
  have hinv : Tendsto (fun δ : ℝ => (√δ)⁻¹) (𝓝[>] 0) atTop := tendsto_inv_nhdsGT_zero.comp hs
  refine tendsto_atTop_mono' _ ?_ (hinv.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ' : (0 : ℝ) < δ := hδ
  have hs : 0 < √δ := Real.sqrt_pos.mpr hδ'
  rw [kappa_eq δ hδ'.le, show (√δ)⁻¹ / 2 = 1 / (2 * √δ) by ring]
  gcongr
  linarith

/-! ## The integer record: exchange after one loop, restore after two -/

/-- The branch of `√(r e^{iθ})` continued along the loop. -/
noncomputable def branch (r θ : ℝ) : ℂ := (√r : ℂ) * Complex.exp (θ / 2 * Complex.I)

/-- The branch squares to the discriminant `r e^{iθ}` at every point of the loop. -/
theorem branch_sq (r θ : ℝ) (hr : 0 ≤ r) :
    branch r θ ^ 2 = r * Complex.exp (θ * Complex.I) := by
  rw [branch, mul_pow, ← Complex.exp_nat_mul]
  have : ((√r : ℝ) : ℂ) ^ 2 = r := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hr]
  rw [this]
  congr 2
  push_cast
  ring

/-- **Exchange.** After one loop the colliding pair has swapped: `z(2π) = −z(0)`. -/
theorem exchange_one_loop (r : ℝ) : branch r (2 * π) = -branch r 0 := by
  simp only [branch]
  have : ((2 * π : ℝ) : ℂ) / 2 * Complex.I = π * Complex.I := by push_cast; ring
  rw [this, Complex.exp_pi_mul_I]
  simp

/-- **Restore.** After two loops the pair is restored: `z(4π) = z(0)`. -/
theorem restore_two_loops (r : ℝ) : branch r (4 * π) = branch r 0 := by
  simp only [branch]
  have : ((4 * π : ℝ) : ℂ) / 2 * Complex.I = 2 * π * Complex.I := by push_cast; ring
  rw [this, Complex.exp_two_pi_mul_I]
  simp

/-- **The ledger is single-valued.** The trace-log of the pair `a ± s` sees only
`det = a² − s² = a² − δ`, the same for either branch `s` or `−s`. -/
theorem ledger_branch_free (a s δ : ℂ) (hs : s ^ 2 = δ) :
    (a + s) * (a - s) = a ^ 2 - δ ∧ (a + s) * (a - s) = (a + -s) * (a - -s) := by
  constructor
  · rw [← hs]; ring
  · ring

/-! ## The hair-rate ladder in one operator -/

/-- The quadratic form `xᵀ A x` of `A = [[−ε, γ], [0, −ε]]`. -/
def hairForm (ε γ x₁ x₂ : ℝ) : ℝ := -ε * x₁ ^ 2 + γ * x₁ * x₂ - ε * x₂ ^ 2

/-- **Modal rate.** `A = [[−ε, γ], [0, −ε]]` has the single eigenvalue `−ε`. -/
theorem hair_modal (ε γ : ℝ) : (!![-ε, γ; 0, -ε] : Matrix (Fin 2) (Fin 2) ℝ).charpoly =
    (Polynomial.X + Polynomial.C ε) ^ 2 := by
  rw [charpoly_fin_two]
  simp [trace_fin_two, det_fin_two, map_add, map_neg, map_mul, map_sub]
  try ring

/-- **Numerical abscissa, upper bound.** `xᵀAx ≤ (−ε + |γ|/2)‖x‖²`. -/
theorem hair_abscissa_le (ε γ x₁ x₂ : ℝ) :
    hairForm ε γ x₁ x₂ ≤ (-ε + |γ| / 2) * (x₁ ^ 2 + x₂ ^ 2) := by
  unfold hairForm
  have h1 : γ * x₁ * x₂ ≤ |γ| * |x₁ * x₂| := by
    rw [mul_assoc]
    exact (le_abs_self _).trans (by rw [abs_mul])
  have h2 : 2 * |x₁ * x₂| ≤ x₁ ^ 2 + x₂ ^ 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|x₁| - |x₂|), sq_abs x₁, sq_abs x₂]
  nlinarith [abs_nonneg γ]

/-- **Numerical abscissa, attained.** At `x = (1, sign γ)` the bound is an equality. -/
theorem hair_abscissa_attained (ε γ : ℝ) :
    hairForm ε γ 1 (SignType.sign γ) = (-ε + |γ| / 2) * (1 ^ 2 + 1 ^ 2) ∨ γ = 0 := by
  rcases lt_trichotomy γ 0 with h | h | h
  · left; simp [hairForm, sign_neg h, abs_of_neg h]; ring
  · right; exact h
  · left; simp [hairForm, sign_pos h, abs_of_pos h]; ring

/-- **The ladder.** When `|γ| > 2ε > 0` the modal rate `−ε` is negative while the energy of
`x = (1, sign γ)` initially grows: `d‖e^{tA}x‖²/dt |₀ = 2xᵀAx > 0`. -/
theorem hair_ladder (ε γ : ℝ) (hε : 0 < ε) (hγ : 2 * ε < |γ|) :
    -ε < 0 ∧ 0 < hairForm ε γ 1 (SignType.sign γ) := by
  refine ⟨by linarith, ?_⟩
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    simp at hγ
    linarith
  rcases hair_abscissa_attained ε γ with h | h
  · rw [h]; nlinarith
  · exact absurd h hγ0

/-! ## The mode ratio and the lane width -/

/-- **Mode ratio.** `λ/d = 2π/(k_max d)` with `k_max d = 0.450` lies in `(13.96, 13.97)`. -/
theorem mode_ratio : 13.96 < 2 * π / 0.45 ∧ 2 * π / 0.45 < 13.97 := by
  have h1 := Real.pi_gt_d4
  have h2 := Real.pi_lt_d4
  constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

/-- **Lane width below the resolution floor.** At the observed 65 km wavelength,
`d = 65/(λ/d)`, and both conventions `2d` and `4d` put the lane between 9 and 19 km. -/
theorem lane_width :
    9 < 2 * (65 / (2 * π / 0.45)) ∧ 4 * (65 / (2 * π / 0.45)) < 19 := by
  have h1 := Real.pi_gt_d4
  have h2 := Real.pi_lt_d4
  have hp : 0 < π := Real.pi_pos
  have e : 65 / (2 * π / 0.45) = 14.625 / π := by field_simp; norm_num
  rw [e]
  constructor
  · rw [mul_div_assoc', lt_div_iff₀ hp]; linarith
  · rw [mul_div_assoc', div_lt_iff₀ hp]; linarith

end Suns
