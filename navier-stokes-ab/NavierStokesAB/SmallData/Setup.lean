import NavierStokesAB.SmallData.RealFields

/-!
# The solution attached to small data, and its velocity and pressure fields

`Small ν σ₀ a` packages the hypotheses on the data: weighted `ℓ¹` coefficients `a` (weight
`e^{σ₀|k|}`) that are small (`‖a‖ ≤ πν/4`), divergence free, and Hermitian. We fix the solution
`sol` of the mild equation and define

* `coef t k = e^{-σ₀|k|} sol_k(t)`: the physical Fourier coefficients of the velocity;
* `vel x t = Re Σ_k e_k(x) coef t k`, computed through `ev` so that joint smoothness is visible;
* `pcoef t n = Σⱼ pm_n (coef t j) (coef t (n - j))` and `prs x t = Re Σ_n e_n(x) pcoef t n`.
-/

open Real Complex Set Filter Topology MeasureTheory
open scoped NNReal BoundedContinuousFunction InnerProductSpace ComplexConjugate ContDiff

set_option synthInstance.maxHeartbeats 200000

namespace NavierStokesAB.SmallData

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

theorem wt_mul_wt (s s' : ℝ) (k : Λ) : wt s k * wt s' k = wt (s + s') k := wt_mul s s' k

theorem wt_smul_wt_smul (s s' : ℝ) (k : Λ) (z : V) :
    wt s k • wt s' k • z = wt (s + s') k • z := by
  rw [smul_smul, wt_mul]

/-- Small, divergence-free, Hermitian data. -/
structure Small (ν σ₀ : ℝ) (a : D) : Prop where
  pos : 0 < ν
  weight : 0 < σ₀
  small : ‖a‖ ≤ π * ν / 4
  div : ∀ k, ⟪kC k, a k⟫_ℂ = 0
  herm : ∀ k, a (-k) = vconj (a k)

namespace Small

variable {ν σ₀ : ℝ} {a : D} (h : Small ν σ₀ a)
include h

theorem exists_sol : ∃ b : X, ‖b‖ ≤ π * ν / 2 ∧ Φ h.pos h.weight.le a b = b :=
  exists_fixedPoint_Φ h.pos h.weight.le a h.small

/-- The solution of the mild equation. -/
noncomputable def sol : X := Classical.choose h.exists_sol

theorem sol_norm : ‖h.sol‖ ≤ π * ν / 2 := (Classical.choose_spec h.exists_sol).1

theorem sol_fix : Φ h.pos h.weight.le a h.sol = h.sol := (Classical.choose_spec h.exists_sol).2

theorem half_le : σ₀ / 2 ≤ σ₀ := by linarith [h.weight]
theorem half_lt : σ₀ / 2 < σ₀ := by linarith [h.weight]
theorem half_pos : 0 < σ₀ / 2 := by linarith [h.weight]
theorem quarter_le : σ₀ / 4 ≤ σ₀ / 2 := by linarith [h.weight]
theorem quarter_pos : 0 < σ₀ / 4 := by linarith [h.weight]

/-- The solution curve read at weight `σ₀ / 2`. -/
noncomputable def w (t : ℝ) : D := curve σ₀ (σ₀ / 2) h.half_le h.sol t

/-- Physical Fourier coefficients of the velocity at time `t`. -/
noncomputable def coef (t : ℝ) (k : Λ) : V := wt (-σ₀) k • h.sol k (Real.toNNReal t)

/-- Fourier coefficients of the pressure at time `t`. -/
noncomputable def pcoef (t : ℝ) (n : Λ) : ℂ := ∑' j, pm n (h.coef t j) (h.coef t (n - j))

/-- The velocity field. -/
noncomputable def vel (x : ℝ³) (t : ℝ) : ℝ³ := re3 (ev V (σ₀ / 2) x (h.w t))

/-- The pressure field. -/
noncomputable def prs (x : ℝ³) (t : ℝ) : ℝ :=
  (ev ℂ (σ₀ / 4) x (presOp (σ₀ / 2) (σ₀ / 4) h.half_pos.le h.quarter_le (h.w t) (h.w t))).re

/-- The initial datum. -/
noncomputable def datum (σ₀ : ℝ) (a : D) (x : ℝ³) : ℝ³ :=
  re3 (four (fun k => wt (-σ₀) k • a k) x)

/-! ### Weights -/

theorem norm_coef_le (t : ℝ) (k : Λ) : ‖h.coef t k‖ ≤ Real.exp (-σ₀ * kn k) * ‖h.sol‖ := by
  rw [coef, norm_smul, norm_wt]
  exact mul_le_mul_of_nonneg_left (((h.sol k).norm_coe_le_norm _).trans
    (lp.norm_apply_le_norm one_ne_zero h.sol k)) (Real.exp_pos _).le

theorem rapidDecay_coef (t : ℝ) : RapidDecay (h.coef t) := fun m =>
  ((summable_pow_mul_exp_neg_kn m h.weight).mul_right ‖h.sol‖).of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (kn_nonneg k) m) (norm_nonneg _)) fun k => by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (h.norm_coef_le t k) (pow_nonneg (kn_nonneg k) m)

theorem ev_w (x : ℝ³) (t : ℝ) : ev V (σ₀ / 2) x (h.w t) = four (h.coef t) x := by
  rw [ev_apply h.half_pos]
  congr 1
  funext k
  rw [w, curve_apply, coef, wt_smul_wt_smul]
  congr 2; ring

theorem vel_eq (x : ℝ³) (t : ℝ) : h.vel x t = re3 (four (h.coef t) x) := by
  rw [vel, ev_w]

theorem vel_fun (t : ℝ) : (fun x => h.vel x t) = re3 ∘ four (h.coef t) := by
  funext x; exact h.vel_eq x t

/-! ### Properties of the coefficients -/

theorem coef_div (t : ℝ) (k : Λ) : ⟪kC k, h.coef t k⟫_ℂ = 0 := by
  rw [coef, inner_smul_right, inner_kC_mode h.sol_fix h.div, mul_zero]

theorem coef_herm (t : ℝ) (k : Λ) : h.coef t (-k) = vconj (h.coef t k) := by
  rw [coef, coef, mode_neg h.pos h.weight.le a h.herm h.sol_norm h.sol_fix, wt, wt, kn_neg,
    vconj_ofReal_smul]

theorem coef_zero_time (k : Λ) : h.coef 0 k = wt (-σ₀) k • a k := by
  rw [coef, Real.toNNReal_zero]
  congr 1
  by_cases hk : k = 0
  · subst hk
    rw [mode_eq h.sol_fix 0, conv_mode_zero]
    simp
  rw [mode_eq h.sol_fix k, conv_mode_eq k hk]
  simp [duhFun]

theorem vconj_four_coef (x : ℝ³) (t : ℝ) : vconj (four (h.coef t) x) = four (h.coef t) x :=
  vconj_four (h.rapidDecay_coef t) (h.coef_herm t) x

theorem ofReal3_vel (x : ℝ³) (t : ℝ) : ofReal3 (h.vel x t) = four (h.coef t) x := by
  rw [vel_eq, ofReal3_re3 (h.vconj_four_coef x t)]

end Small

end NavierStokesAB.SmallData
